import * as THREE from 'three';
import { scene } from './scene-setup.js';
import { state } from './state.js';
import { MAZE_SIZE, TILE_SIZE, maze, emptyCells, getPos, rooms, bfsPath, exitGridX, exitGridZ } from './maze.js';
import { matFloor, matCeil, matWall, matDarkMetal, matRusty, matSteel, matChrome, matWarnYellow } from './textures.js';
import { registerPropSolid } from './collision.js';

// ================================================================
//  LEVEL GEOMETRY (Optimized for Performance)
// ================================================================
const WALL_HEIGHT = 14;

// 1. FLOOR
export const floorMesh = new THREE.Mesh(new THREE.PlaneGeometry(MAZE_SIZE * TILE_SIZE, MAZE_SIZE * TILE_SIZE), matFloor);
floorMesh.rotation.x = -Math.PI / 2;
floorMesh.receiveShadow = true;
scene.add(floorMesh);

// 2. CEILING
export const ceilMesh = new THREE.Mesh(new THREE.PlaneGeometry(MAZE_SIZE * TILE_SIZE, MAZE_SIZE * TILE_SIZE), matCeil);
ceilMesh.rotation.x = Math.PI / 2;
ceilMesh.position.y = WALL_HEIGHT;
ceilMesh.receiveShadow = true;
scene.add(ceilMesh);

// ================================================================
//  3. WALLS — real damaged geometry, not texture tricks.
//
//  Each wall tile is an extruded polygon: a square footprint with 1-3
//  corners genuinely cut inward (actual vertices, actual depth). Six
//  damage patterns are built ONCE; every wall instance picks one of the
//  six and gets a random 90-degree rotation, so with only 6 draw calls
//  total, no two walls read as identical. The cut corner is biased
//  toward whichever side of the tile actually faces open corridor, so
//  the damage is visible from where the player walks instead of being
//  hidden inside solid rock.
// ================================================================
const H = TILE_SIZE / 2;
// Local corners, unrotated: 0=(-x,-z) 1=(+x,-z) 2=(+x,+z) 3=(-x,+z)
const CORNERS = [
    new THREE.Vector2(-H, -H), new THREE.Vector2(H, -H),
    new THREE.Vector2(H, H), new THREE.Vector2(-H, H)
];

function wallShape(cuts) {
    const shape = new THREE.Shape();
    const pts = [];
    for (let c = 0; c < 4; c++) {
        const cut = cuts.find(k => k.corner === c);
        if (!cut) { pts.push(CORNERS[c]); continue; }
        const prev = CORNERS[(c + 3) % 4], next = CORNERS[(c + 1) % 4];
        pts.push(CORNERS[c].clone().lerp(prev, cut.depth), CORNERS[c].clone().lerp(next, cut.depth));
    }
    shape.moveTo(pts[0].x, pts[0].y);
    for (let i = 1; i < pts.length; i++) shape.lineTo(pts[i].x, pts[i].y);
    shape.closePath();
    return shape;
}

function buildWallGeo(cuts) {
    const geo = new THREE.ExtrudeGeometry(wallShape(cuts), { depth: WALL_HEIGHT, bevelEnabled: false, curveSegments: 1 });
    geo.rotateX(-Math.PI / 2); // extrude axis -> world Y, base already sits at y=0
    geo.computeVertexNormals();
    return geo;
}

// Damage patterns. Every wall gets SOME visible groove — there is no
// pristine/flat variant. "severe" walls also get a matching fallen
// chunk of debris on the floor, with a real hitbox.
const VARIANTS = [
    { key: 'mild1', weight: 30, cuts: [{ corner: 0, depth: 0.15 }] },
    { key: 'mod1', weight: 25, cuts: [{ corner: 0, depth: 0.32 }] },
    { key: 'worn3', weight: 10, cuts: [{ corner: 0, depth: 0.10 }, { corner: 1, depth: 0.10 }, { corner: 2, depth: 0.10 }] },
    { key: 'adj2', weight: 15, cuts: [{ corner: 0, depth: 0.18 }, { corner: 1, depth: 0.18 }] },
    { key: 'opp2', weight: 12, cuts: [{ corner: 0, depth: 0.20 }, { corner: 2, depth: 0.20 }] },
    { key: 'severe', weight: 8, cuts: [{ corner: 0, depth: 0.46 }] },
];
const totalWeight = VARIANTS.reduce((s, v) => s + v.weight, 0);
function pickVariant() {
    let r = Math.random() * totalWeight;
    for (const v of VARIANTS) { if (r < v.weight) return v; r -= v.weight; }
    return VARIANTS[0];
}

const variantGeo = {};
const variantMesh = {};
VARIANTS.forEach(v => { variantGeo[v.key] = buildWallGeo(v.cuts); });

// Count wall cells and pick a variant for each up-front.
const wallCells = [];
for (let i = 0; i < MAZE_SIZE; i++) for (let j = 0; j < MAZE_SIZE; j++) if (maze[i][j] === 1) {
    const openDirs = [];
    if (maze[i - 1]?.[j] === 0) openDirs.push(0); // west
    if (maze[i + 1]?.[j] === 0) openDirs.push(1); // east
    if (maze[i]?.[j - 1] === 0) openDirs.push(2); // north
    if (maze[i]?.[j + 1] === 0) openDirs.push(3); // south
    wallCells.push({ i, j, openDirs, variant: pickVariant() });
}

// Bucket by variant so each gets its own InstancedMesh.
const buckets = {};
VARIANTS.forEach(v => buckets[v.key] = []);
wallCells.forEach(c => buckets[c.variant.key].push(c));

// Corner 0 sits at local (-x,-z) i.e. faces "west+north". Rotating the
// instance 0/90/180/270 degrees moves which world-facing corner that
// damage actually shows on. Pick whichever rotation best faces an open
// corridor direction (west=0, east=1, north=2, south=3).
const ROT_FACES = [ // for rotation index r, which two open-dir codes does corner 0 end up nearest?
    [0, 2], // r=0: faces west+north
    [2, 1], // r=1 (90deg): faces north+east
    [1, 3], // r=2 (180deg): faces east+south
    [3, 0], // r=3 (270deg): faces south+west
];
function bestRotation(openDirs) {
    if (!openDirs.length) return Math.floor(Math.random() * 4);
    let best = 0, bestScore = -1;
    for (let r = 0; r < 4; r++) {
        const score = ROT_FACES[r].filter(d => openDirs.includes(d)).length;
        if (score > bestScore) { bestScore = score; best = r; }
    }
    return best;
}

const debrisChunks = [];
const _d = new THREE.Object3D();
VARIANTS.forEach(v => {
    const cells = buckets[v.key];
    if (!cells.length) return;
    const mesh = new THREE.InstancedMesh(variantGeo[v.key], matWall, cells.length);
    mesh.castShadow = true; mesh.receiveShadow = true;
    cells.forEach((c, idx) => {
        const p = getPos(c.i, c.j);
        const rot = bestRotation(c.openDirs);
        _d.position.set(p.x, 0, p.z);
        _d.rotation.set(0, rot * Math.PI / 2, 0);
        _d.updateMatrix();
        mesh.setMatrixAt(idx, _d.matrix);
        if (v.key === 'severe' && c.openDirs.length && Math.random() < 0.7) debrisChunks.push({ p, rot, dir: c.openDirs[0] });
    });
    mesh.instanceMatrix.needsUpdate = true;
    scene.add(mesh);
    variantMesh[v.key] = mesh;
});

// Fallen debris for severe walls: a real chunk on the floor, with a hitbox.
{
    const chunkGeo = new THREE.BoxGeometry(1.8, 1.3, 1.8);
    const DIR_OFFSET = [[-1, 0], [1, 0], [0, -1], [0, 1]];
    debrisChunks.forEach(dc => {
        const [ox, oz] = DIR_OFFSET[dc.dir];
        const m = new THREE.Mesh(chunkGeo, matRusty);
        m.position.set(dc.p.x + ox * (H + 0.9), 0.6, dc.p.z + oz * (H + 0.9));
        m.rotation.set((Math.random() - 0.5) * 0.3, Math.random() * Math.PI, (Math.random() - 0.5) * 0.3);
        m.scale.set(0.8 + Math.random() * 0.5, 0.6 + Math.random() * 0.4, 0.8 + Math.random() * 0.5);
        m.castShadow = true;
        scene.add(m);
        registerPropSolid(m);
    });
    // Light scatter of small rubble bits near the debris for extra realism (decorative, no hitbox)
    if (debrisChunks.length) {
        const rubGeo = new THREE.BoxGeometry(0.35, 0.22, 0.35);
        const rubMesh = new THREE.InstancedMesh(rubGeo, matRusty, debrisChunks.length * 2);
        let idx = 0;
        debrisChunks.forEach(dc => {
            const [ox, oz] = DIR_OFFSET[dc.dir];
            for (let k = 0; k < 2; k++) {
                _d.position.set(dc.p.x + ox * (H + 0.9) + (Math.random() - 0.5) * 1.5, 0.11, dc.p.z + oz * (H + 0.9) + (Math.random() - 0.5) * 1.5);
                _d.rotation.set(0, Math.random() * Math.PI, 0);
                _d.updateMatrix();
                rubMesh.setMatrixAt(idx++, _d.matrix);
            }
        });
        rubMesh.instanceMatrix.needsUpdate = true;
        scene.add(rubMesh);
    }
}

// --- CORRIDOR LIGHT FIXTURES ---
{
    const sp = getPos(1, 1);
    let added = 0;

    const lightTexCanvas = document.createElement('canvas');
    lightTexCanvas.width = lightTexCanvas.height = 64;
    const ltCtx = lightTexCanvas.getContext('2d');
    ltCtx.fillStyle = '#222'; ltCtx.fillRect(0, 0, 64, 64);
    for (let i = 0; i < 400; i++) {
        ltCtx.fillStyle = `rgba(255,255,255,${Math.random() * 0.05})`;
        ltCtx.fillRect(Math.random() * 64, Math.random() * 64, 1, 10 * Math.random());
    }
    const lightTex = new THREE.CanvasTexture(lightTexCanvas);
    lightTex.magFilter = THREE.NearestFilter;

    const fixtureMat = new THREE.MeshStandardMaterial({ map: lightTex, color: 0x444444, roughness: 0.8, metalness: 0.3 });

    for (const cell of emptyCells) {
        if (added >= 14) break;
        const pos = getPos(cell.x, cell.z);
        if (Math.hypot(pos.x - sp.x, pos.z - sp.z) < 14) continue;

        if (Math.random() > 0.85) {
            const lightGroup = new THREE.Group();
            lightGroup.position.set(pos.x, WALL_HEIGHT - 0.1, pos.z);

            const mainBody = new THREE.Mesh(new THREE.BoxGeometry(2.5, 0.15, 0.6), fixtureMat);
            lightGroup.add(mainBody);
            const bezelTop = new THREE.Mesh(new THREE.BoxGeometry(2.7, 0.04, 0.7), fixtureMat);
            bezelTop.position.y = 0.08;
            lightGroup.add(bezelTop);

            const screwGeo = new THREE.CylinderGeometry(0.03, 0.03, 0.02, 6);
            const screwMat = new THREE.MeshStandardMaterial({ color: 0x111111 });
            [[1.1, 0.22], [1.1, -0.22], [-1.1, 0.22], [-1.1, -0.22]].forEach(loc => {
                const s = new THREE.Mesh(screwGeo, screwMat);
                s.position.set(loc[0], -0.07, loc[1]);
                lightGroup.add(s);
            });

            const stripMat = new THREE.MeshStandardMaterial({ color: 0x000000, emissive: 0xbbddff, emissiveIntensity: 2 });
            const strip = new THREE.Mesh(new THREE.BoxGeometry(2.3, 0.05, 0.15), stripMat);
            strip.position.y = -0.09;
            lightGroup.add(strip);

            scene.add(lightGroup);

            const light = new THREE.PointLight(0x88bbff, 60, 25, 2);
            light.position.set(pos.x, WALL_HEIGHT - 1.4, pos.z);
            light.castShadow = true;
            light.shadow.mapSize.width = 256;
            light.shadow.mapSize.height = 256;
            light.shadow.bias = -0.005;
            scene.add(light);

            state.corridorLights.push({ light, strip: stripMat, base: 60, rate: 15, seed: Math.random() * 100, broken: Math.random() > 0.6 });
            added++;
        }
    }
}

// --- LANDMARK ROOM: tint the walls around the first carved room ---
if (rooms.length) {
    const lm = rooms[0];
    const landmarkMat = new THREE.MeshStandardMaterial({ map: matWall.map, color: 0x6a3a20, roughness: 0.9 });
    const cells = [];
    for (let i = lm.x - 4; i <= lm.x + 4; i++) for (let j = lm.z - 4; j <= lm.z + 4; j++)
        if (i > 0 && i < MAZE_SIZE - 1 && j > 0 && j < MAZE_SIZE - 1 && maze[i][j] === 1) cells.push(getPos(i, j));
    if (cells.length) {
        const lmMesh = new THREE.InstancedMesh(variantGeo.mild1, landmarkMat, cells.length);
        cells.forEach((p, idx) => {
            _d.position.set(p.x, 0.02, p.z);
            _d.rotation.set(0, Math.floor(Math.random() * 4) * Math.PI / 2, 0);
            _d.scale.set(1.004, 1.002, 1.004);
            _d.updateMatrix();
            lmMesh.setMatrixAt(idx, _d.matrix);
        });
        lmMesh.instanceMatrix.needsUpdate = true;
        scene.add(lmMesh);
    }
}

// ================================================================
//  PIPE NETWORK — only runs along real, contiguous corridor-facing
//  wall runs, with capped ends, wall brackets, and occasional valves.
//  Nothing floats disconnected.
// ================================================================
{
    const PIPE_Y = WALL_HEIGHT - 5;
    const pipeMat = matDarkMetal;
    const flangeGeo = new THREE.CylinderGeometry(0.22, 0.22, 0.3, 8);
    const bracketGeo = new THREE.BoxGeometry(0.5, 0.4, 0.22);
    let pipeRunsBuilt = 0;
    const MAX_RUNS = 20;

    function buildPipeRun(cells, axis, faceOffset) {
        if (pipeRunsBuilt >= MAX_RUNS || cells.length < 2 || Math.random() > 0.4) return;
        pipeRunsBuilt++;
        const first = getPos(cells[0].i, cells[0].j), last = getPos(cells[cells.length - 1].i, cells[cells.length - 1].j);
        const len = Math.hypot(last.x - first.x, last.z - first.z) + TILE_SIZE;
        const midX = (first.x + last.x) / 2 + faceOffset.x, midZ = (first.z + last.z) / 2 + faceOffset.z;

        const pipeGeo = new THREE.CylinderGeometry(0.16, 0.16, len, 8);
        const pipe = new THREE.Mesh(pipeGeo, pipeMat);
        pipe.position.set(midX, PIPE_Y, midZ);
        pipe.rotation.set(axis === 'x' ? 0 : 0, 0, axis === 'x' ? Math.PI / 2 : 0);
        if (axis === 'z') pipe.rotation.set(Math.PI / 2, 0, 0);
        pipe.castShadow = true;
        scene.add(pipe);

        // End flanges
        [[first, -1], [last, 1]].forEach(([end, sign]) => {
            const ep = getPos(end.i, end.j);
            const cap = new THREE.Mesh(flangeGeo, matChrome);
            cap.position.set(ep.x + faceOffset.x + (axis === 'x' ? sign * TILE_SIZE / 2 : 0), PIPE_Y, ep.z + faceOffset.z + (axis === 'z' ? sign * TILE_SIZE / 2 : 0));
            cap.rotation.copy(pipe.rotation);
            scene.add(cap);
        });

        // Wall brackets every ~2 tiles
        for (let k = 0; k < cells.length; k += 2) {
            const bp = getPos(cells[k].i, cells[k].j);
            const br = new THREE.Mesh(bracketGeo, matSteel);
            br.position.set(bp.x + faceOffset.x * 0.7, PIPE_Y, bp.z + faceOffset.z * 0.7);
            br.rotation.copy(pipe.rotation);
            scene.add(br);
        }

        // Occasional valve at the run's midpoint
        if (Math.random() < 0.25) {
            const vg = new THREE.Group();
            vg.position.set(midX, PIPE_Y - 0.6, midZ);
            const vBody = new THREE.Mesh(new THREE.CylinderGeometry(0.28, 0.28, 0.5, 10), matSteel);
            vg.add(vBody);
            const vH1 = new THREE.Mesh(new THREE.BoxGeometry(1.0, 0.14, 0.14), matWarnYellow); vH1.position.y = 0.32; vg.add(vH1);
            const vH2 = new THREE.Mesh(new THREE.BoxGeometry(0.14, 0.14, 1.0), matWarnYellow); vH2.position.y = 0.32; vg.add(vH2);
            vg.rotation.copy(pipe.rotation);
            scene.add(vg);
        }
    }

    // Horizontal runs (vary i, fixed j) facing north (j-1 open) or south (j+1 open)
    for (let j = 1; j < MAZE_SIZE - 1; j++) {
        [[-1, 0, -1], [1, 0, 1]].forEach(([dj, ox, oz]) => {
            let run = [];
            for (let i = 0; i < MAZE_SIZE; i++) {
                const open = maze[i]?.[j] === 1 && maze[i]?.[j + dj] === 0;
                if (open) run.push({ i, j });
                else { buildPipeRun(run, 'x', { x: 0, z: oz * (H + 0.25) }); run = []; }
            }
            buildPipeRun(run, 'x', { x: 0, z: oz * (H + 0.25) });
        });
    }
    // Vertical runs (vary j, fixed i) facing west (i-1 open) or east (i+1 open)
    for (let i = 1; i < MAZE_SIZE - 1; i++) {
        [[-1, -1, 0], [1, 1, 0]].forEach(([di, ox, oz]) => {
            let run = [];
            for (let j = 0; j < MAZE_SIZE; j++) {
                const open = maze[i]?.[j] === 1 && maze[i + di]?.[j] === 0;
                if (open) run.push({ i, j });
                else { buildPipeRun(run, 'z', { x: ox * (H + 0.25), z: 0 }); run = []; }
            }
            buildPipeRun(run, 'z', { x: ox * (H + 0.25), z: 0 });
        });
    }
}

// --- DEAD-END PROPS: crates/barrels marking unexplored-feeling dead ends (now solid) ---
{
    const crateGeo = new THREE.BoxGeometry(1.6, 1.6, 1.6);
    const barrelGeo = new THREE.CylinderGeometry(0.7, 0.75, 1.7, 10);
    const sp = getPos(1, 1);
    emptyCells.forEach(c => {
        let openN = 0;
        [[0, -1], [0, 1], [-1, 0], [1, 0]].forEach(([dx, dz]) => { if (maze[c.x + dx]?.[c.z + dz] === 0) openN++; });
        if (openN !== 1 || Math.random() > 0.5) return;
        const p = getPos(c.x, c.z);
        if (Math.hypot(p.x - sp.x, p.z - sp.z) < 16) return;
        const useCrate = Math.random() < 0.5;
        const m = new THREE.Mesh(useCrate ? crateGeo : barrelGeo, useCrate ? matRusty : matDarkMetal);
        m.position.set(p.x, useCrate ? 0.8 : 0.85, p.z);
        m.rotation.y = Math.random() * Math.PI;
        m.castShadow = true;
        scene.add(m);
        registerPropSolid(m);
    });
}

// --- FLOOR VARIATION: grated metal patch on the approach to the door ---
{
    const doorP = getPos(exitGridX, exitGridZ);
    const patch = new THREE.Mesh(new THREE.PlaneGeometry(TILE_SIZE * 3, TILE_SIZE * 4), matDarkMetal);
    patch.rotation.x = -Math.PI / 2;
    patch.position.set(doorP.x, 0.02, doorP.z - TILE_SIZE * 1.5);
    patch.receiveShadow = true;
    scene.add(patch);
}

// --- CEILING DUCTS: hanging beams for height-variation feel (non-solid, above head height) ---
{
    const sp = getPos(1, 1);
    let ducts = 0;
    for (const cell of emptyCells) {
        if (ducts >= 10) break;
        const p = getPos(cell.x, cell.z);
        if (Math.hypot(p.x - sp.x, p.z - sp.z) < 20 || Math.random() > 0.9) continue;
        const duct = new THREE.Mesh(new THREE.BoxGeometry(TILE_SIZE * 0.9, 0.7, 0.7), matDarkMetal);
        duct.position.set(p.x, WALL_HEIGHT - 3.4, p.z);
        duct.rotation.y = Math.random() < 0.5 ? 0 : Math.PI / 2;
        duct.castShadow = true;
        scene.add(duct);
        ducts++;
    }
}

// --- PUDDLES: cheap reflective-looking floor decals near pipes/damp corners ---
{
    const puddleMat = new THREE.MeshStandardMaterial({ color: 0x0a1418, roughness: 0.15, metalness: 0.3, transparent: true, opacity: 0.75 });
    const puddleGeo = new THREE.CylinderGeometry(1.4, 1.4, 0.02, 14);
    const sp = getPos(1, 1);
    let puddles = 0;
    for (const cell of emptyCells) {
        if (puddles >= 8) break;
        const p = getPos(cell.x, cell.z);
        if (Math.hypot(p.x - sp.x, p.z - sp.z) < 16 || Math.random() > 0.93) continue;
        const pd = new THREE.Mesh(puddleGeo, puddleMat);
        pd.position.set(p.x + (Math.random() - 0.5) * 3, 0.015, p.z + (Math.random() - 0.5) * 3);
        pd.scale.set(0.6 + Math.random() * 0.7, 1, 0.6 + Math.random() * 0.7);
        scene.add(pd);
        puddles++;
    }
}

// --- DIRECTIONAL FLOOR WEAR: darkened trail along the shortest path to the door ---
{
    const wearMat = new THREE.MeshBasicMaterial({ color: 0x000000, transparent: true, opacity: 0.16, depthWrite: false });
    const path = bfsPath(1, 1, exitGridX, exitGridZ);
    path.forEach(node => {
        const p = getPos(node.x, node.z);
        const w = new THREE.Mesh(new THREE.PlaneGeometry(TILE_SIZE * 0.85, TILE_SIZE * 0.85), wearMat);
        w.rotation.x = -Math.PI / 2;
        w.position.set(p.x, 0.012, p.z);
        scene.add(w);
    });
}
