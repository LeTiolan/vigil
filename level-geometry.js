import * as THREE from 'three';
import { scene } from './scene-setup.js';
import { state } from './state.js';
import { MAZE_SIZE, TILE_SIZE, maze, emptyCells, getPos, rooms, bfsPath, exitGridX, exitGridZ } from './maze.js';
import { matFloor, matCeil, matWall, matDarkMetal, matRusty } from './textures.js';

// ================================================================
//  LEVEL GEOMETRY (Optimized for Performance)
// ================================================================

// 1. FLOOR
export const floorMesh = new THREE.Mesh(new THREE.PlaneGeometry(MAZE_SIZE * TILE_SIZE, MAZE_SIZE * TILE_SIZE), matFloor);
floorMesh.rotation.x = -Math.PI / 2;
floorMesh.receiveShadow = true;
scene.add(floorMesh);

// 2. CEILING
export const ceilMesh = new THREE.Mesh(new THREE.PlaneGeometry(MAZE_SIZE * TILE_SIZE, MAZE_SIZE * TILE_SIZE), matCeil);
ceilMesh.rotation.x = Math.PI / 2;
ceilMesh.position.y = 14;
ceilMesh.receiveShadow = true;
scene.add(ceilMesh);

// 3. WALLS (InstancedMesh)
let wallCount = 0;
for (let i = 0; i < MAZE_SIZE; i++) {
    for (let j = 0; j < MAZE_SIZE; j++) {
        if (maze[i][j] === 1) wallCount++;
    }
}

const iWallGeo = new THREE.BoxGeometry(TILE_SIZE, 14, TILE_SIZE);
matWall.shadowSide = THREE.DoubleSide;
export const iWallMesh = new THREE.InstancedMesh(iWallGeo, matWall, wallCount);
iWallMesh.castShadow = true;
iWallMesh.receiveShadow = true;

const _dm = new THREE.Object3D();
let _wi = 0;
for (let i = 0; i < MAZE_SIZE; i++) {
    for (let j = 0; j < MAZE_SIZE; j++) {
        if (maze[i][j] === 1) {
            const p = getPos(i, j);
            _dm.position.set(p.x, 7, p.z);
            _dm.updateMatrix();
            iWallMesh.setMatrixAt(_wi++, _dm.matrix);
        }
    }
}
iWallMesh.instanceMatrix.needsUpdate = true;
scene.add(iWallMesh);

// --- CORRIDOR LIGHT FIXTURES ---
{
    const sp = getPos(1, 1);
    let added = 0;

    // 1. Procedural Scratched Texture
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

    const fixtureMat = new THREE.MeshStandardMaterial({
        map: lightTex, color: 0x444444, roughness: 0.8, metalness: 0.3
    });

    for (const cell of emptyCells) {
        if (added >= 14) break;
        const pos = getPos(cell.x, cell.z);
        if (Math.hypot(pos.x - sp.x, pos.z - sp.z) < 14) continue;

        if (Math.random() > 0.85) {
            const lightGroup = new THREE.Group();
            lightGroup.position.set(pos.x, 13.9, pos.z);

            // A. THE HOUSING
            const mainBody = new THREE.Mesh(new THREE.BoxGeometry(2.5, 0.15, 0.6), fixtureMat);
            lightGroup.add(mainBody);
            const bezelTop = new THREE.Mesh(new THREE.BoxGeometry(2.7, 0.04, 0.7), fixtureMat);
            bezelTop.position.y = 0.08;
            lightGroup.add(bezelTop);

            // B. THE HARDWARE (screws)
            const screwGeo = new THREE.CylinderGeometry(0.03, 0.03, 0.02, 6);
            const screwMat = new THREE.MeshStandardMaterial({ color: 0x111111 });
            [[1.1, 0.22], [1.1, -0.22], [-1.1, 0.22], [-1.1, -0.22]].forEach(loc => {
                const s = new THREE.Mesh(screwGeo, screwMat);
                s.position.set(loc[0], -0.07, loc[1]);
                lightGroup.add(s);
            });

            // C. THE RADIATING ELEMENT (glowing tube)
            const stripMat = new THREE.MeshStandardMaterial({
                color: 0x000000, emissive: 0xbbddff, emissiveIntensity: 2
            });
            const strip = new THREE.Mesh(new THREE.BoxGeometry(2.3, 0.05, 0.15), stripMat);
            strip.position.y = -0.09;
            lightGroup.add(strip);

            scene.add(lightGroup);

            // D. THE SIMPLE FUNCTIONING LIGHT
            const light = new THREE.PointLight(0x88bbff, 60, 25, 2);
            light.position.set(pos.x, 12.5, pos.z);
            light.castShadow = true;
            light.shadow.mapSize.width = 256;
            light.shadow.mapSize.height = 256;
            light.shadow.bias = -0.005;
            scene.add(light);

            // Push both the light AND the strip to the shared state array
            state.corridorLights.push({
                light: light,
                strip: stripMat,
                base: 60,
                rate: 15,
                seed: Math.random() * 100,
                broken: Math.random() > 0.6
            });

            added++;
        }
    }
}

// --- WALL DAMAGE: chipped corners + fallen rubble (proportional, base-weighted) ---
{
    const off = Math.floor(MAZE_SIZE / 2);
    const chipGeo = new THREE.BoxGeometry(1, 1, 1);
    const rubGeo = new THREE.BoxGeometry(0.35, 0.22, 0.35);
    const chips = [], rubble = [];
    for (let i = 1; i < MAZE_SIZE - 1; i++) for (let j = 1; j < MAZE_SIZE - 1; j++) {
        if (maze[i][j] !== 1 || Math.random() > 0.14) continue;
        const wx = (i - off) * TILE_SIZE, wz = (j - off) * TILE_SIZE;
        const cxs = Math.random() < 0.5 ? -1 : 1, czs = Math.random() < 0.5 ? -1 : 1;
        chips.push({ x: wx + cxs * 5.7, y: 0.3 + Math.random() * 1.6, z: wz + czs * 5.7, s: 0.4 + Math.random() * 0.5 });
        if (Math.random() < 0.5) rubble.push({ x: wx + cxs * 6.1 + (Math.random() - 0.5), y: 0.11, z: wz + czs * 6.1 + (Math.random() - 0.5), r: Math.random() * Math.PI });
    }
    if (chips.length) {
        const chipMesh = new THREE.InstancedMesh(chipGeo, matDarkMetal, chips.length);
        const d = new THREE.Object3D();
        chips.forEach((c, idx) => {
            d.position.set(c.x, c.y, c.z);
            d.rotation.set(Math.random(), Math.random(), Math.random());
            d.scale.set(c.s, c.s * 0.8, c.s);
            d.updateMatrix();
            chipMesh.setMatrixAt(idx, d.matrix);
        });
        chipMesh.instanceMatrix.needsUpdate = true;
        chipMesh.castShadow = true;
        scene.add(chipMesh);
    }
    if (rubble.length) {
        const rubMesh = new THREE.InstancedMesh(rubGeo, matRusty, rubble.length);
        const d2 = new THREE.Object3D();
        rubble.forEach((r, idx) => {
            d2.position.set(r.x, r.y, r.z);
            d2.rotation.y = r.r;
            d2.updateMatrix();
            rubMesh.setMatrixAt(idx, d2.matrix);
        });
        rubMesh.instanceMatrix.needsUpdate = true;
        scene.add(rubMesh);
    }
}

// --- LANDMARK ROOM: tint the walls around the first carved room ---
if (rooms.length) {
    const lm = rooms[0];
    const landmarkMat = new THREE.MeshStandardMaterial({ map: matWall.map, color: 0x6a3a20, roughness: 0.9 });
    const cells = [];
    for (let i = lm.x - 3; i <= lm.x + 3; i++) for (let j = lm.z - 3; j <= lm.z + 3; j++)
        if (i > 0 && i < MAZE_SIZE - 1 && j > 0 && j < MAZE_SIZE - 1 && maze[i][j] === 1) cells.push(getPos(i, j));
    if (cells.length) {
        const lmMesh = new THREE.InstancedMesh(iWallGeo, landmarkMat, cells.length);
        const d3 = new THREE.Object3D();
        cells.forEach((p, idx) => { d3.position.set(p.x, 7.02, p.z); d3.scale.set(1.005, 1.005, 1.005); d3.updateMatrix(); lmMesh.setMatrixAt(idx, d3.matrix); });
        lmMesh.instanceMatrix.needsUpdate = true;
        scene.add(lmMesh);
    }
}

// --- DEAD-END PROPS: crates/barrels marking unexplored-feeling dead ends ---
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
        m.position.set(p.x + (Math.random() - 0.5) * 3, useCrate ? 0.8 : 0.85, p.z + (Math.random() - 0.5) * 3);
        m.rotation.y = Math.random() * Math.PI;
        m.castShadow = true;
        scene.add(m);
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
        duct.position.set(p.x, 10.6, p.z);
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
    const startG = { x: 1, z: 1 };
    const path = bfsPath(startG.x, startG.z, exitGridX, exitGridZ);
    path.forEach(node => {
        const p = getPos(node.x, node.z);
        const w = new THREE.Mesh(new THREE.PlaneGeometry(TILE_SIZE * 0.85, TILE_SIZE * 0.85), wearMat);
        w.rotation.x = -Math.PI / 2;
        w.position.set(p.x, 0.012, p.z);
        scene.add(w);
    });
}