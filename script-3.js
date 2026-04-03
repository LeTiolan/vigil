
        import * as THREE from 'three';

        // ================================================================
        // MAZE GENERATION  (original — untouched)
        // ================================================================
        const MAZE_SIZE = 25; const TILE_SIZE = 12;
        const maze = Array(MAZE_SIZE).fill(null).map(() => Array(MAZE_SIZE).fill(1));
        const emptyCells = [];

        function carveMaze(x, y) {
            maze[x][y] = 0;
            const dirs = [[0,-1],[0,1],[-1,0],[1,0]].sort(() => Math.random() - 0.5);
            for (let [dx, dy] of dirs) {
                const nx = x + dx * 2; const ny = y + dy * 2;
                if (nx > 0 && nx < MAZE_SIZE - 1 && ny > 0 && ny < MAZE_SIZE - 1 && maze[nx][ny] === 1) {
                    maze[x + dx][y + dy] = 0; carveMaze(nx, ny);
                }
            }
        }
        carveMaze(1, 1);

        for (let i = 1; i < MAZE_SIZE - 1; i++) {
            for (let j = 1; j < MAZE_SIZE - 1; j++) {
                if (maze[i][j] === 1 && ((maze[i-1][j] === 0 && maze[i+1][j] === 0) || (maze[i][j-1] === 0 && maze[i][j+1] === 0)) && Math.random() < 0.25) maze[i][j] = 0;
            }
        }

        const exitGridX = Math.floor(MAZE_SIZE / 2); const exitGridZ = MAZE_SIZE - 1;
        for (let i = -1; i <= 1; i++) { for (let j = -3; j <= -1; j++) { maze[exitGridX + i][exitGridZ + j] = 0; } }
        maze[exitGridX][exitGridZ] = 0;

        for (let i = 0; i < MAZE_SIZE; i++) { for (let j = 0; j < MAZE_SIZE; j++) { if (maze[i][j] === 0) emptyCells.push({x: i, z: j}); } }

        // ================================================================
        // PATHFINDING UTILITIES  (new — parent-map BFS, O(n) memory)
        // ================================================================
        function worldToGrid(wx, wz) {
            const o = Math.floor(MAZE_SIZE / 2);
            return { x: Math.max(0, Math.min(MAZE_SIZE-1, Math.round(wx / TILE_SIZE) + o)), z: Math.max(0, Math.min(MAZE_SIZE-1, Math.round(wz / TILE_SIZE) + o)) };
        }

        function bfsPath(sx, sz, gx, gz) {
            if (sx === gx && sz === gz) return [];
            const queue = [{x: sx, z: sz}];
            const parent = new Map();
            parent.set(`${sx},${sz}`, null);
            let iters = 0;
            while (queue.length && iters++ < 2000) {
                const {x, z} = queue.shift();
                for (const [dx, dz] of [[0,-1],[0,1],[-1,0],[1,0]]) {
                    const nx = x + dx, nz = z + dz;
                    const key = `${nx},${nz}`;
                    if (nx < 0 || nx >= MAZE_SIZE || nz < 0 || nz >= MAZE_SIZE) continue;
                    if (maze[nx][nz] !== 0 || parent.has(key)) continue;
                    parent.set(key, `${x},${z}`);
                    if (nx === gx && nz === gz) {
                        // Reconstruct path from goal to start using parent map
                        const path = [];
                        let cur = key;
                        while (cur !== null) {
                            const [px, pz] = cur.split(',').map(Number);
                            path.unshift({x: px, z: pz});
                            cur = parent.get(cur);
                        }
                        if (path.length > 0 && path[0].x === sx && path[0].z === sz) path.shift();
                        return path;
                    }
                    queue.push({x: nx, z: nz});
                }
            }
            return [];
        }

        function hasLineOfSight(ax, az, bx, bz) {
            const g0 = worldToGrid(ax, az), g1 = worldToGrid(bx, bz);
            const steps = Math.max(Math.abs(g1.x - g0.x), Math.abs(g1.z - g0.z));
            if (steps === 0) return true;
            for (let i = 1; i < steps; i++) {
                const t = i / steps;
                const cx = Math.round(g0.x + (g1.x - g0.x) * t), cz = Math.round(g0.z + (g1.z - g0.z) * t);
                if (cx >= 0 && cx < MAZE_SIZE && cz >= 0 && cz < MAZE_SIZE && maze[cx][cz] === 1) return false;
            }
            return true;
        }

        // ================================================================
        // GAME CONSTANTS
        // ================================================================
        const totalOrbs = 12;
        const MAX_STAMINA = 200;
        // AI
        const ALERT_DURATION       = 11.0;
        const LIGHT_DETECT_RANGE   = 36;
        const FLASHLIGHT_CONE_COS  = Math.cos(62 * Math.PI / 180); // flashlight half-angle
        const SPRINT_ALERT_RADIUS  = 26;
        const ENEMY_NAMES = ['REVENANT','UNIT-07','SPECTER-X','THE HOLLOW','SHADE-03','ECHO-NULL'];

        // ================================================================
        // GAME STATE
        // ================================================================
        let orbsCollected = 0; let gameActive = false; let gameWon = false;
        let startTime = 0; let accumulatedTime = 0; let hasPlayedSting = false; let prevTime = performance.now();
        let yaw = Math.PI; let pitch = 0; const SENSITIVITY = 0.002;
        let introShown = false;
        let lastFootstepCycle = 0;
        let sprintAlertCooldown = 0;
        let currentlySprinting = false;
        // Explored cells for radar minimap outlines
        const exploredCells = new Set();

        document.getElementById('totalOrbsUI').innerText = totalOrbs;

        const player = {
            height: 2.1, radius: 0.8, walkSpeed: 0.22, runSpeed: 0.48,
            stamina: MAX_STAMINA, isExhausted: false,
            velocity: new THREE.Vector2(0, 0), headBobTimer: 0
        };
        const keys = {};

        // ================================================================
        // INJECTED DOM ELEMENTS  (avoids touching HTML/CSS files)
        // ================================================================
        // Sprint/threat vignette overlay
        const vignetteEl = document.createElement('div');
        vignetteEl.style.cssText = 'position:fixed;top:0;left:0;width:100%;height:100%;pointer-events:none;z-index:4;opacity:0;transition:opacity 0.3s ease;background:radial-gradient(ellipse at center,transparent 38%,rgba(0,0,0,0.93) 100%);';
        document.body.appendChild(vignetteEl);

        // Terminal interaction prompt (shows near terminal when all orbs collected)
        const termPromptEl = document.createElement('div');
        termPromptEl.style.cssText = `
            position:fixed;bottom:175px;left:50%;transform:translateX(-50%);
            background:linear-gradient(135deg,#1a1511 0%,#0c0a07 100%);
            border:3px ridge #8b6b4a;color:#d4c4a8;
            padding:10px 24px;font-family:'Courier New',monospace;
            font-size:14px;letter-spacing:2px;text-transform:uppercase;
            display:none;z-index:10;pointer-events:none;
            box-shadow:4px 4px 10px rgba(0,0,0,0.8);
        `;
        termPromptEl.innerHTML = '[ <span style="color:#00eeff;font-weight:bold;font-size:1.2em;">E</span> ] &mdash; ACTIVATE TERMINAL';
        document.body.appendChild(termPromptEl);

        // Door locked message (shows when near door but orbs missing)
        const doorLockedEl = document.createElement('div');
        doorLockedEl.style.cssText = `
            position:fixed;bottom:175px;left:50%;transform:translateX(-50%);
            background:linear-gradient(135deg,#2a0a0a 0%,#110505 100%);
            border:3px ridge #8b2a2a;color:#cc6666;
            padding:10px 24px;font-family:'Courier New',monospace;
            font-size:13px;letter-spacing:2px;text-transform:uppercase;
            display:none;z-index:10;pointer-events:none;
            box-shadow:4px 4px 10px rgba(0,0,0,0.8);
        `;
        doorLockedEl.innerHTML = '⚠ BREACH SEALED &mdash; <span id="orbsNeededCount">0</span> ORBS REQUIRED';
        document.body.appendChild(doorLockedEl);

        // ================================================================
        // RADAR CANVAS
        // ================================================================
        const radarCanvas = document.getElementById('radar'); const rCtx = radarCanvas.getContext('2d');
        const rCenter = radarCanvas.width / 2; const radarMaxDist = 120; const radarScale = (rCenter - 10) / radarMaxDist;

        // ================================================================
        // AUDIO ENGINE  (original + footstep function)
        // ================================================================
        const audioCtx = new (window.AudioContext || window.webkitAudioContext)();
        let klaxonOsc, klaxonGain, vaultOsc, vaultGain, latchOsc, latchGain, pistonOsc, pistonGain, gearOsc, gearGain, hissSrc, hissGain;

        function initIndustrialAudio() {
            if (audioCtx.state === 'suspended') audioCtx.resume();
            klaxonOsc = audioCtx.createOscillator(); klaxonOsc.type = 'triangle'; klaxonOsc.frequency.value = 450;
            const klaxonLFO = audioCtx.createOscillator(); klaxonLFO.frequency.value = 2;
            const klaxonMod = audioCtx.createGain(); klaxonMod.gain.value = 150;
            klaxonLFO.connect(klaxonMod); klaxonMod.connect(klaxonOsc.frequency); klaxonLFO.start();
            klaxonGain = audioCtx.createGain(); klaxonGain.gain.value = 0;
            klaxonOsc.connect(klaxonGain); klaxonGain.connect(audioCtx.destination); klaxonOsc.start();
            vaultOsc = audioCtx.createOscillator(); vaultOsc.type = 'sawtooth'; vaultOsc.frequency.value = 180;
            vaultGain = audioCtx.createGain(); vaultGain.gain.value = 0;
            vaultOsc.connect(vaultGain); vaultGain.connect(audioCtx.destination); vaultOsc.start();
            latchOsc = audioCtx.createOscillator(); latchOsc.type = 'sawtooth'; latchOsc.frequency.value = 90;
            latchGain = audioCtx.createGain(); latchGain.gain.value = 0;
            latchOsc.connect(latchGain); latchGain.connect(audioCtx.destination); latchOsc.start();
            pistonOsc = audioCtx.createOscillator(); pistonOsc.type = 'square'; pistonOsc.frequency.value = 35;
            pistonGain = audioCtx.createGain(); pistonGain.gain.value = 0;
            const filter = audioCtx.createBiquadFilter(); filter.type = 'lowpass'; filter.frequency.value = 150;
            pistonOsc.connect(filter); filter.connect(pistonGain); pistonGain.connect(audioCtx.destination); pistonOsc.start();
            gearOsc = audioCtx.createOscillator(); gearOsc.type = 'square'; gearOsc.frequency.value = 18;
            gearGain = audioCtx.createGain(); gearGain.gain.value = 0;
            gearOsc.connect(gearGain); gearGain.connect(audioCtx.destination); gearOsc.start();
            const bufferSize = audioCtx.sampleRate * 2;
            const noiseBuffer = audioCtx.createBuffer(1, bufferSize, audioCtx.sampleRate);
            const output = noiseBuffer.getChannelData(0);
            for (let i = 0; i < bufferSize; i++) output[i] = Math.random() * 2 - 1;
            hissSrc = audioCtx.createBufferSource(); hissSrc.buffer = noiseBuffer; hissSrc.loop = true;
            const hissFilter = audioCtx.createBiquadFilter(); hissFilter.type = 'highpass'; hissFilter.frequency.value = 1000;
            hissGain = audioCtx.createGain(); hissGain.gain.value = 0;
            hissSrc.connect(hissFilter); hissFilter.connect(hissGain); hissGain.connect(audioCtx.destination); hissSrc.start();
        }

        function playSting() {
            if (audioCtx.state === 'suspended') audioCtx.resume();
            const osc = audioCtx.createOscillator(); const gain = audioCtx.createGain();
            osc.type = 'sawtooth'; osc.frequency.setValueAtTime(120, audioCtx.currentTime); osc.frequency.exponentialRampToValueAtTime(30, audioCtx.currentTime + 1);
            gain.gain.setValueAtTime(0.2, audioCtx.currentTime); gain.gain.exponentialRampToValueAtTime(0.01, audioCtx.currentTime + 1);
            osc.connect(gain); gain.connect(audioCtx.destination); osc.start(); osc.stop(audioCtx.currentTime + 1);
        }

        // NEW: Footstep sound — filtered noise burst, distinct for walk vs sprint
        function playFootstep(isSprint) {
            if (audioCtx.state === 'suspended') audioCtx.resume();
            const sz = Math.floor(audioCtx.sampleRate * 0.042);
            const buf = audioCtx.createBuffer(1, sz, audioCtx.sampleRate);
            const d = buf.getChannelData(0);
            for (let i = 0; i < sz; i++) d[i] = (Math.random() * 2 - 1) * Math.pow(1 - i / sz, 5);
            const src = audioCtx.createBufferSource(); src.buffer = buf;
            const f = audioCtx.createBiquadFilter();
            f.type = 'lowpass';
            f.frequency.value = isSprint ? 720 : 390; // sprint = higher freq = harder thud
            const g = audioCtx.createGain();
            g.gain.value = isSprint ? 0.52 : 0.28;
            src.connect(f); f.connect(g); g.connect(audioCtx.destination); src.start();
        }

        // NEW: Orb collect chime
        function playOrbChime(isGold) {
            if (audioCtx.state === 'suspended') audioCtx.resume();
            const freqs = isGold ? [440, 660, 880, 1100] : [440, 660, 880];
            freqs.forEach((freq, i) => {
                const o = audioCtx.createOscillator(); const g = audioCtx.createGain();
                o.type = isGold ? 'sine' : 'triangle'; o.frequency.value = freq;
                const t = audioCtx.currentTime + i * 0.08;
                g.gain.setValueAtTime(0, t); g.gain.linearRampToValueAtTime(0.22, t + 0.01); g.gain.exponentialRampToValueAtTime(0.001, t + 0.2);
                o.connect(g); g.connect(audioCtx.destination); o.start(t); o.stop(t + 0.22);
            });
        }

        // NEW: Enemy alert screech
        function playAlertScreech() {
            if (audioCtx.state === 'suspended') audioCtx.resume();
            const o = audioCtx.createOscillator(); const g = audioCtx.createGain();
            o.type = 'sawtooth';
            o.frequency.setValueAtTime(260, audioCtx.currentTime); o.frequency.exponentialRampToValueAtTime(55, audioCtx.currentTime + 0.45);
            g.gain.setValueAtTime(0.16, audioCtx.currentTime); g.gain.exponentialRampToValueAtTime(0.001, audioCtx.currentTime + 0.45);
            o.connect(g); g.connect(audioCtx.destination); o.start(); o.stop(audioCtx.currentTime + 0.45);
        }

        function playUISound(freq, vol, dur, type = 'triangle') {
            if (audioCtx.state === 'suspended') audioCtx.resume();
            const osc = audioCtx.createOscillator(); const gain = audioCtx.createGain();
            osc.type = type; osc.frequency.setValueAtTime(freq, audioCtx.currentTime); osc.frequency.exponentialRampToValueAtTime(freq / 2, audioCtx.currentTime + dur);
            gain.gain.setValueAtTime(vol, audioCtx.currentTime); gain.gain.exponentialRampToValueAtTime(0.001, audioCtx.currentTime + dur);
            osc.connect(gain); gain.connect(audioCtx.destination); osc.start(); osc.stop(audioCtx.currentTime + dur);
        }

        // ================================================================
        // PROCEDURAL TEXTURES  (original — untouched)
        // ================================================================
        function createGrimeTexture() {
            const c = document.createElement('canvas'); c.width = 512; c.height = 512; const ctx = c.getContext('2d');
            ctx.fillStyle = '#2a2a2a'; ctx.fillRect(0, 0, 512, 512);
            for (let i = 0; i < 10000; i++) {
                ctx.fillStyle = Math.random() > 0.5 ? 'rgba(0,0,0,0.1)' : 'rgba(80,60,40,0.1)';
                ctx.beginPath(); ctx.arc(Math.random() * 512, Math.random() * 512, Math.random() * 4, 0, Math.PI * 2); ctx.fill();
            }
            const tex = new THREE.CanvasTexture(c); tex.wrapS = tex.wrapT = THREE.RepeatWrapping; tex.repeat.set(2, 2); return tex;
        }
        function createHazardTexture() {
            const c = document.createElement('canvas'); c.width = 256; c.height = 256; const ctx = c.getContext('2d');
            ctx.fillStyle = '#d4af37'; ctx.fillRect(0, 0, 256, 256); ctx.fillStyle = '#111';
            for (let i = -256; i < 512; i += 64) { ctx.beginPath(); ctx.moveTo(i, 0); ctx.lineTo(i + 32, 0); ctx.lineTo(i + 288, 256); ctx.lineTo(i + 256, 256); ctx.fill(); }
            const tex = new THREE.CanvasTexture(c); tex.wrapS = tex.wrapT = THREE.RepeatWrapping; return tex;
        }

        // NEW: Ceiling texture (darker version of grime)
        function createCeilingTexture() {
            const c = document.createElement('canvas'); c.width = 512; c.height = 512; const ctx = c.getContext('2d');
            ctx.fillStyle = '#1a1a1a'; ctx.fillRect(0, 0, 512, 512);
            // Panel grid lines
            ctx.strokeStyle = '#111'; ctx.lineWidth = 2;
            for (let i = 0; i < 512; i += 64) { ctx.beginPath(); ctx.moveTo(i, 0); ctx.lineTo(i, 512); ctx.stroke(); ctx.beginPath(); ctx.moveTo(0, i); ctx.lineTo(512, i); ctx.stroke(); }
            // Grime dots
            for (let i = 0; i < 6000; i++) {
                ctx.fillStyle = `rgba(0,0,0,${Math.random() * 0.15})`;
                ctx.beginPath(); ctx.arc(Math.random() * 512, Math.random() * 512, Math.random() * 3, 0, Math.PI * 2); ctx.fill();
            }
            const tex = new THREE.CanvasTexture(c); tex.wrapS = tex.wrapT = THREE.RepeatWrapping; tex.repeat.set(4, 4); return tex;
        }

        // ================================================================
        // SCENE, CAMERA, RENDERER  (original)
        // ================================================================
        const scene = new THREE.Scene(); scene.background = new THREE.Color(0x0c121a); scene.fog = new THREE.Fog(0x0c121a, 15, 120);
        const camera = new THREE.PerspectiveCamera(75, window.innerWidth / window.innerHeight, 0.1, 1000); camera.rotation.order = 'YXZ';
        const renderer = new THREE.WebGLRenderer({ antialias: true }); renderer.setSize(window.innerWidth, window.innerHeight);
        renderer.shadowMap.enabled = true; renderer.shadowMap.type = THREE.PCFSoftShadowMap; document.body.appendChild(renderer.domElement);

        const hemiLight = new THREE.HemisphereLight(0xffffff, 0x444444, 0.6); scene.add(hemiLight);
        const flashLight = new THREE.SpotLight(0xffffe6, 50.0, 500, Math.PI / 5, 0.6, 1.0);
        flashLight.position.set(0, 0, 0); flashLight.castShadow = true; flashLight.shadow.bias = -0.001;
        camera.add(flashLight); camera.add(flashLight.target); flashLight.target.position.set(0, 0, -1); scene.add(camera);

        // ================================================================
        // MATERIALS  (original)
        // ================================================================
        const matDarkMetal = new THREE.MeshStandardMaterial({ map: createGrimeTexture(), metalness: 0.8, roughness: 0.7 });
        const matRustyFrame = new THREE.MeshStandardMaterial({ color: 0x3d352b, metalness: 0.9, roughness: 0.9 });
        const matBrightSteel = new THREE.MeshStandardMaterial({ color: 0xaaaaaa, metalness: 1.0, roughness: 0.2 });
        const matHazard = new THREE.MeshStandardMaterial({ map: createHazardTexture(), metalness: 0.3, roughness: 0.8 });
        const matWarningYellow = new THREE.MeshStandardMaterial({ color: 0xffaa00, metalness: 0.4, roughness: 0.7 });
        const matBlackHole = new THREE.MeshStandardMaterial({ color: 0x030303, roughness: 1.0 });
        const matGlassRed = new THREE.MeshStandardMaterial({ color: 0xff0000, emissive: 0x550000, transparent: true, opacity: 0.8 });
        const matIndicator = new THREE.MeshBasicMaterial({ color: 0xff0000 });

        // ================================================================
        // PARTICLES  (original — untouched)
        // ================================================================
        const particles = [];
        const sparkGeo = new THREE.BoxGeometry(0.1, 0.1, 0.1);
        const sparkMat = new THREE.MeshBasicMaterial({ color: 0xffaa00 });
        const steamGeo = new THREE.PlaneGeometry(1.5, 1.5);
        const steamMat = new THREE.MeshBasicMaterial({ color: 0xdddddd, transparent: true, opacity: 0.5, depthWrite: false });

        function emitSpark(x, y, z) {
            const spark = new THREE.Mesh(sparkGeo, sparkMat); spark.position.set(x, y, z);
            spark.userData = { vel: new THREE.Vector3((Math.random() - 0.5) * 5, Math.random() * 5 + 2, (Math.random() - 0.5) * 5), life: 1.0, type: 'spark' };
            scene.add(spark); particles.push(spark);
        }
        function emitSteam(x, y, z) {
            const steam = new THREE.Mesh(steamGeo, steamMat.clone()); steam.position.set(x, y, z);
            steam.userData = { vel: new THREE.Vector3((Math.random() - 0.5) * 2, Math.random() * 3 + 1, (Math.random() - 0.5) * 2), life: 1.0, type: 'steam', mat: steam.material };
            scene.add(steam); particles.push(steam);
        }

        // ================================================================
        // COLLISION & LEVEL BUILDING  (original)
        // ================================================================
        const solidDoorParts = []; const partBoxHelper = new THREE.Box3();
        function registerSolid(mesh) { solidDoorParts.push(mesh); }

        function createGearMesh(radius, depth, teethCount) {
            const gearGroup = new THREE.Group();
            const core = new THREE.Mesh(new THREE.CylinderGeometry(radius * 0.85, radius * 0.85, depth, 16), matBrightSteel);
            core.rotation.x = Math.PI / 2; core.castShadow = true; gearGroup.add(core);
            const toothGeo = new THREE.BoxGeometry((Math.PI * radius * 2) / (teethCount * 2), radius * 0.25, depth);
            for (let i = 0; i < teethCount; i++) {
                const angle = (i / teethCount) * Math.PI * 2; const tooth = new THREE.Mesh(toothGeo, matBrightSteel);
                tooth.position.set(Math.cos(angle) * radius * 0.95, Math.sin(angle) * radius * 0.95, 0);
                tooth.rotation.z = angle + Math.PI / 2; tooth.castShadow = true; gearGroup.add(tooth);
            }
            const axle = new THREE.Mesh(new THREE.CylinderGeometry(radius * 0.3, radius * 0.3, depth + 0.2, 12), matDarkMetal);
            axle.rotation.x = Math.PI / 2; gearGroup.add(axle);
            const hitBox = new THREE.Mesh(new THREE.BoxGeometry(radius * 2, radius * 2, depth), new THREE.MeshBasicMaterial({ visible: false }));
            gearGroup.add(hitBox); registerSolid(hitBox); return gearGroup;
        }

        function getPos(i, j) { return { x: (i - Math.floor(MAZE_SIZE / 2)) * TILE_SIZE, z: (j - Math.floor(MAZE_SIZE / 2)) * TILE_SIZE }; }

        // Floor (original)
        const floor = new THREE.Mesh(new THREE.PlaneGeometry(MAZE_SIZE * TILE_SIZE, MAZE_SIZE * TILE_SIZE), new THREE.MeshStandardMaterial({ color: 0x222222, roughness: 0.9 }));
        floor.rotation.x = -Math.PI / 2; floor.receiveShadow = true; scene.add(floor);

        // NEW: Ceiling at y=14, matching floor size, grime texture
        const ceiling = new THREE.Mesh(
            new THREE.PlaneGeometry(MAZE_SIZE * TILE_SIZE, MAZE_SIZE * TILE_SIZE),
            new THREE.MeshStandardMaterial({ map: createCeilingTexture(), roughness: 1.0, metalness: 0.1 })
        );
        ceiling.rotation.x = Math.PI / 2;
        ceiling.position.y = 14;
        ceiling.receiveShadow = true;
        scene.add(ceiling);

        // Walls (original)
        const wallGeo = new THREE.BoxGeometry(TILE_SIZE, 14, TILE_SIZE);
        const wallMat = new THREE.MeshStandardMaterial({ color: 0x1e3f1e, roughness: 0.8 });
        for (let i = 0; i < MAZE_SIZE; i++) {
            for (let j = 0; j < MAZE_SIZE; j++) {
                if (maze[i][j] === 1) {
                    const wall = new THREE.Mesh(wallGeo, wallMat); const pos = getPos(i, j);
                    wall.position.set(pos.x, 7, pos.z); wall.castShadow = true; wall.receiveShadow = true; scene.add(wall);
                }
            }
        }

        // NEW: Corridor ceiling lights — luminescent, some flickering
        const corridorLights = [];
        {
            let added = 0;
            const startP = getPos(1, 1);
            for (const cell of emptyCells) {
                if (added >= 10) break;
                const pos = getPos(cell.x, cell.z);
                if (Math.hypot(pos.x - startP.x, pos.z - startP.z) < 12) continue;
                if (Math.random() > 0.93) {
                    // Light strip geometry at ceiling
                    const stripMat = new THREE.MeshBasicMaterial({ color: 0x88aacc });
                    const strip = new THREE.Mesh(new THREE.BoxGeometry(1.5, 0.1, 0.4), stripMat);
                    strip.position.set(pos.x, 13.8, pos.z);
                    scene.add(strip);
                    const cl = new THREE.PointLight(0x7799cc, 1.2, 28);
                    cl.position.set(pos.x, 13.5, pos.z);
                    scene.add(cl);
                    corridorLights.push({
                        light: cl, strip: stripMat,
                        seed: Math.random() * 100,
                        baseIntensity: 0.9 + Math.random() * 0.6,
                        // Some lights flicker fast (broken), others breathe slowly
                        flickerRate: Math.random() > 0.4 ? 0.8 + Math.random() * 1.5 : 12 + Math.random() * 8,
                        isBroken: Math.random() > 0.6
                    });
                    added++;
                }
            }
        }

        const startPos = getPos(1, 1); camera.position.set(startPos.x, player.height, startPos.z); camera.rotation.set(0, yaw, 0);

        // ================================================================
        // CINEMATIC TITAN DOOR  (original — untouched)
        // ================================================================
        let doorState = 'closed';
        const doorStartWorldPos = getPos(exitGridX, exitGridZ);
        const doorGroup = new THREE.Group(); doorGroup.position.set(doorStartWorldPos.x, 0, doorStartWorldPos.z);

        const frameHeight = 16; const frameZ = -1.5; const doorZPos = 0.5; const panelWidth = 5.0;

        const lintel = new THREE.Mesh(new THREE.BoxGeometry(16, 4, 2), matRustyFrame); lintel.position.set(0, frameHeight - 2, frameZ); lintel.castShadow = true; lintel.receiveShadow = true; doorGroup.add(lintel); registerSolid(lintel);
        const leftPillar = new THREE.Mesh(new THREE.BoxGeometry(4, frameHeight, 2), matRustyFrame); leftPillar.position.set(-6, frameHeight / 2, frameZ); leftPillar.castShadow = true; leftPillar.receiveShadow = true; doorGroup.add(leftPillar); registerSolid(leftPillar);
        const rightPillar = new THREE.Mesh(new THREE.BoxGeometry(4, frameHeight, 2), matRustyFrame); rightPillar.position.set(6, frameHeight / 2, frameZ); rightPillar.castShadow = true; rightPillar.receiveShadow = true; doorGroup.add(rightPillar); registerSolid(rightPillar);

        const sirens = [];
        const createSiren = (x, z) => {
            const sGroup = new THREE.Group(); sGroup.position.set(x, frameHeight - 4, z);
            const bulb = new THREE.Mesh(new THREE.CylinderGeometry(0.5, 0.5, 1, 16), matGlassRed); sGroup.add(bulb);
            const spot = new THREE.SpotLight(0xff0000, 0, 40, Math.PI / 6, 0.5, 1);
            spot.position.set(0, 0, 0); spot.target.position.set(0, -10, 10);
            spot.castShadow = true; spot.shadow.mapSize.width = 512; spot.shadow.mapSize.height = 512;
            spot.shadow.camera.near = 1; spot.shadow.camera.far = 40; spot.shadow.bias = -0.001;
            sGroup.add(spot); sGroup.add(spot.target);
            doorGroup.add(sGroup); sirens.push({ group: sGroup, light: spot });
        };
        createSiren(-6, frameZ - 1); createSiren(6, frameZ - 1); createSiren(-6, frameZ + 1); createSiren(6, frameZ + 1);

        const indL = new THREE.Mesh(new THREE.BoxGeometry(0.2, 6, 0.2), matIndicator); indL.position.set(-4.1, 7, frameZ); doorGroup.add(indL);
        const indR = new THREE.Mesh(new THREE.BoxGeometry(0.2, 6, 0.2), matIndicator); indR.position.set(4.1, 7, frameZ); doorGroup.add(indR);

        const doorHalfLeftGroup = new THREE.Group(); doorHalfLeftGroup.position.set(-panelWidth / 2, 7, doorZPos);
        const doorHalfRightGroup = new THREE.Group(); doorHalfRightGroup.position.set(panelWidth / 2, 7, doorZPos);
        doorGroup.add(doorHalfLeftGroup, doorHalfRightGroup);

        const panelGeo = new THREE.BoxGeometry(panelWidth, 14, 1.0);
        const panelLeft = new THREE.Mesh(panelGeo, matDarkMetal); panelLeft.castShadow = true;
        const panelRight = new THREE.Mesh(panelGeo, matDarkMetal); panelRight.castShadow = true;
        doorHalfLeftGroup.add(panelLeft); doorHalfRightGroup.add(panelRight); registerSolid(panelLeft); registerSolid(panelRight);

        const deadboltsLeft = []; const deadboltsRight = [];
        const boltGeo = new THREE.CylinderGeometry(0.3, 0.3, 3, 16); boltGeo.rotateZ(Math.PI / 2);
        for (let y of [-3, -1, 1, 3]) {
            const bL = new THREE.Mesh(boltGeo, matBrightSteel); bL.position.set(1.5, y, 0); doorHalfLeftGroup.add(bL); deadboltsLeft.push(bL);
            const bR = new THREE.Mesh(boltGeo, matBrightSteel); bR.position.set(-1.5, y, 0); doorHalfRightGroup.add(bR); deadboltsRight.push(bR);
        }

        const vaultWheelGroup = new THREE.Group(); vaultWheelGroup.position.set(panelWidth / 2, 0, -0.7); doorHalfLeftGroup.add(vaultWheelGroup);
        const vaultCore = createGearMesh(2.5, 0.8, 16); vaultWheelGroup.add(vaultCore);
        const vaultSocket = new THREE.Mesh(new THREE.CylinderGeometry(2.6, 2.6, 0.2, 16), matBlackHole); vaultSocket.rotation.x = Math.PI / 2; vaultSocket.position.set(-panelWidth / 2, 0, -0.6); doorHalfRightGroup.add(vaultSocket);

        const valves = [];
        for (let py of [-3, 3]) {
            const valve = new THREE.Mesh(new THREE.TorusGeometry(0.6, 0.15, 8, 16), matWarningYellow); valve.position.set(-1.0, py, -0.7); doorHalfRightGroup.add(valve); valves.push(valve);
        }

        const latchGeo = new THREE.BoxGeometry(2, 1.5, 1.5);
        const latchL = new THREE.Mesh(latchGeo, matHazard); latchL.position.set(-4.5, 7, -0.6); latchL.castShadow = true; doorGroup.add(latchL); registerSolid(latchL);
        const latchR = new THREE.Mesh(latchGeo, matHazard); latchR.position.set(4.5, 7, -0.6); latchR.castShadow = true; doorGroup.add(latchR); registerSolid(latchR);

        const rackGeo = new THREE.BoxGeometry(panelWidth - 0.5, 0.8, 0.5);
        const rackL = new THREE.Mesh(rackGeo, matBrightSteel); rackL.position.set(0, 4, -0.8); doorHalfLeftGroup.add(rackL);
        const rackR = new THREE.Mesh(rackGeo, matBrightSteel); rackR.position.set(0, 4, -0.8); doorHalfRightGroup.add(rackR);

        const gearRadius = 1.6;
        const mainGearLeft = createGearMesh(gearRadius, 0.6, 12); mainGearLeft.position.set(-3, 11 + gearRadius, -0.8); doorGroup.add(mainGearLeft);
        const mainGearRight = createGearMesh(gearRadius, 0.6, 12); mainGearRight.position.set(3, 11 + gearRadius, -0.8); doorGroup.add(mainGearRight);

        const helperGearRadius = 0.8;
        const helperGearLeft = createGearMesh(helperGearRadius, 0.6, 6); helperGearLeft.position.set(-3 - gearRadius - helperGearRadius + 0.2, 11 + gearRadius + 1, -0.8); doorGroup.add(helperGearLeft);
        const helperGearRight = createGearMesh(helperGearRadius, 0.6, 6); helperGearRight.position.set(3 + gearRadius + helperGearRadius - 0.2, 11 + gearRadius + 1, -0.8); doorGroup.add(helperGearRight);

        const pistonGroup = new THREE.Group(); doorGroup.add(pistonGroup);
        const pistonGeo = new THREE.BoxGeometry(1.5, 6, 1.5);
        const pistonL = new THREE.Mesh(pistonGeo, matHazard); pistonL.position.set(-3.5, 7, -0.8); pistonL.castShadow = true; pistonGroup.add(pistonL); registerSolid(pistonL);
        const pistonR = new THREE.Mesh(pistonGeo, matHazard); pistonR.position.set(3.5, 7, -0.8); pistonR.castShadow = true; pistonGroup.add(pistonR); registerSolid(pistonR);
        scene.add(doorGroup);

        // ================================================================
        // NEW: TERMINAL PANEL  — player must press E here to open the door
        // ================================================================
        // Placed to the left of the door approach corridor
        const terminalWX = doorStartWorldPos.x - 9;
        const terminalWZ = doorStartWorldPos.z - 4;

        const terminalGroup = new THREE.Group();
        terminalGroup.position.set(terminalWX, 0, terminalWZ);
        terminalGroup.rotation.y = Math.PI * 0.5; // face player approaching from south

        // Panel body
        const termBodyMat = new THREE.MeshStandardMaterial({ color: 0x1a1208, metalness: 0.6, roughness: 0.6 });
        const termBody = new THREE.Mesh(new THREE.BoxGeometry(3, 5, 0.5), termBodyMat);
        termBody.position.set(0, 2.5, 0); termBody.castShadow = true; terminalGroup.add(termBody);

        // Screen (glowing green)
        const termScreenMat = new THREE.MeshBasicMaterial({ color: 0x003300 });
        const termScreen = new THREE.Mesh(new THREE.BoxGeometry(2.2, 2.8, 0.05), termScreenMat);
        termScreen.position.set(0, 3.0, 0.28); terminalGroup.add(termScreen);

        // Activate button (red, round)
        const termBtnMat = new THREE.MeshBasicMaterial({ color: 0x880000 });
        const termBtn = new THREE.Mesh(new THREE.CylinderGeometry(0.28, 0.28, 0.12, 16), termBtnMat);
        termBtn.rotation.x = Math.PI / 2; termBtn.position.set(0, 1.1, 0.28); terminalGroup.add(termBtn);

        // Frame border
        const termFrameMat = new THREE.MeshStandardMaterial({ color: 0x3a2a0a, metalness: 0.9, roughness: 0.5 });
        const termFrame = new THREE.Mesh(new THREE.BoxGeometry(3.2, 5.2, 0.3), termFrameMat);
        termFrame.position.set(0, 2.5, -0.12); terminalGroup.add(termFrame);

        // Glow light on terminal
        const termLight = new THREE.PointLight(0x00aa44, 0, 10); // starts dark, activates when ready
        termLight.position.set(0, 2.5, 1.5); terminalGroup.add(termLight);

        scene.add(terminalGroup);

        // ================================================================
        // ORBS  (original + gold orb variety)
        // ================================================================
        const orbs = []; const SAFE_ZONE_FROM_PLAYER = 20;
        let orbAttempts = 0;
        while (orbs.length < totalOrbs && orbAttempts < 2000) {
            orbAttempts++;
            const cell = emptyCells[Math.floor(Math.random() * emptyCells.length)];
            const pos = getPos(cell.x, cell.z);
            if (Math.hypot(pos.x - startPos.x, pos.z - startPos.z) < SAFE_ZONE_FROM_PLAYER) continue;
            let tooClose = false;
            for (let existingOrb of orbs) { if (Math.hypot(pos.x - existingOrb.position.x, pos.z - existingOrb.position.z) < 20) { tooClose = true; break; } }
            if (!tooClose) {
                const orbMesh = new THREE.Mesh(new THREE.SphereGeometry(0.5), new THREE.MeshBasicMaterial({ color: 0x00eeff }));
                orbMesh.position.set(pos.x, 1.5, pos.z);
                const orbLight = new THREE.PointLight(0x00eeff, 1, 10); orbMesh.add(orbLight);
                orbMesh.userData = { isGold: false };
                scene.add(orbMesh); orbs.push(orbMesh);
            }
        }
        // Mark 3 random orbs as gold (restores stamina on collect)
        const goldIndices = new Set();
        while (goldIndices.size < Math.min(3, orbs.length)) goldIndices.add(Math.floor(Math.random() * orbs.length));
        for (const idx of goldIndices) {
            const o = orbs[idx];
            o.material.color.setHex(0xffaa00);
            o.children[0].color?.setHex(0xffaa00); // point light if exists
            if (o.children[0] && o.children[0].isLight) o.children[0].color.setHex(0xffaa00);
            o.userData.isGold = true;
        }

        // ================================================================
        // ENEMIES  (original structure + AI state fields)
        // ================================================================
        const ghostGeo = new THREE.SphereGeometry(1.2, 20, 20);
        const ghostMat = new THREE.MeshBasicMaterial({ color: 0xff0000, transparent: true, opacity: 0.7 });
        const enemies = []; let enemyAttempts = 0;

        while (enemies.length < 8 && enemyAttempts < 2000) {
            enemyAttempts++;
            const eCell = emptyCells[Math.floor(Math.random() * emptyCells.length)];
            const ePos = getPos(eCell.x, eCell.z);
            if (Math.hypot(ePos.x - startPos.x, ePos.z - startPos.z) < 40) continue;
            let tooClose = false;
            for (let e of enemies) { if (Math.hypot(ePos.x - e.position.x, ePos.z - e.position.z) < 30) { tooClose = true; break; } }
            if (!tooClose) {
                const enemy = new THREE.Mesh(ghostGeo, ghostMat.clone()); // clone mat so each can be tinted
                enemy.position.set(ePos.x, 2.0, ePos.z);
                const pLight = new THREE.PointLight(0xff0000, 2, 20); enemy.add(pLight);
                enemy.userData = {
                    // Original fields
                    targetPos: new THREE.Vector3(ePos.x, 2.0, ePos.z),
                    lastGrid: { x: eCell.x, z: eCell.z },
                    // AI fields
                    state: 'patrol',          // 'patrol' | 'alerted' | 'searching'
                    alertTimer: 0,
                    pathQueue: [],
                    pathUpdateTimer: 0,
                    lastKnownGrid: null,
                    name: ENEMY_NAMES[enemies.length % ENEMY_NAMES.length],
                    light: pLight,
                    spikeGroup: null,         // neon spike visual, added on alert
                    afterimageTimer: 0
                };
                scene.add(enemy); enemies.push(enemy);
            }
        }

        // ================================================================
        // NEW: ALERT SPIKE VISUAL — neon ferrofluid spikes on alerted enemies
        // ================================================================
        const spikeMat = new THREE.MeshBasicMaterial({ color: 0xff0832 });

        function addSpikes(enemy) {
            if (enemy.userData.spikeGroup) return; // already has spikes
            const sg = new THREE.Group();
            const NUM = 8;
            for (let i = 0; i < NUM; i++) {
                const angle = (i / NUM) * Math.PI * 2;
                const geo = new THREE.ConeGeometry(0.1, 1.1, 6);
                const spike = new THREE.Mesh(geo, spikeMat);
                // Point outward from sphere centre in XZ plane
                const dir = new THREE.Vector3(Math.cos(angle), 0, Math.sin(angle));
                spike.position.copy(dir.clone().multiplyScalar(1.4));
                spike.quaternion.setFromUnitVectors(new THREE.Vector3(0, 1, 0), dir);
                spike.userData = { angle, phase: Math.random() * Math.PI * 2, baseLen: 1.1 };
                sg.add(spike);
            }
            // Top + bottom spikes
            const topSpike = new THREE.Mesh(new THREE.ConeGeometry(0.1, 1.3, 6), spikeMat);
            topSpike.position.set(0, 1.5, 0); topSpike.userData = { phase: Math.random() * Math.PI * 2, isVertical: true };
            sg.add(topSpike);
            const botSpike = new THREE.Mesh(new THREE.ConeGeometry(0.09, 0.9, 6), spikeMat);
            botSpike.position.set(0, -1.5, 0); botSpike.rotation.z = Math.PI;
            botSpike.userData = { phase: Math.random() * Math.PI * 2, isVertical: true };
            sg.add(botSpike);
            enemy.add(sg);
            enemy.userData.spikeGroup = sg;
        }

        function removeSpikes(enemy) {
            if (!enemy.userData.spikeGroup) return;
            enemy.remove(enemy.userData.spikeGroup);
            enemy.userData.spikeGroup = null;
        }

        function animateSpikes(spikeGroup, now) {
            spikeGroup.children.forEach(spike => {
                const phase = spike.userData.phase || 0;
                const pulse = 0.65 + 0.5 * Math.abs(Math.sin(now * 0.007 + phase));
                spike.scale.setScalar(pulse);
                if (!spike.userData.isVertical) {
                    const ang = spike.userData.angle;
                    const wobble = 0.15 * Math.sin(now * 0.009 + phase);
                    const r = 1.4 + wobble;
                    spike.position.set(Math.cos(ang) * r, Math.sin(now * 0.004 + phase) * 0.25, Math.sin(ang) * r);
                }
            });
        }

        // ================================================================
        // NEW: ALERT SYSTEM — trigger on light cone + LOS, or sprint sound
        // ================================================================
        function triggerAlert(enemy) {
            const ud = enemy.userData;
            if (ud.state === 'alerted') { ud.alertTimer = ALERT_DURATION; return; }
            ud.state = 'alerted';
            ud.alertTimer = ALERT_DURATION;
            ud.pathUpdateTimer = 0;
            ud.light.intensity = 10;
            enemy.material.color.setHex(0xff3333);
            addSpikes(enemy);
            playAlertScreech();
        }

        function alertEnemiesInRadius(wx, wz, radius) {
            enemies.forEach(e => {
                if (e.userData.state !== 'alerted' && Math.hypot(e.position.x - wx, e.position.z - wz) < radius)
                    triggerAlert(e);
            });
        }

        // ================================================================
        // INPUT & MECHANICAL UI LOGIC  (original + E-key handler)
        // ================================================================
        const uiContainer = document.getElementById('main-ui');
        const engageBtn = document.getElementById('engage-btn');
        const nameInput = document.getElementById('name-input');
        const bgText = document.getElementById('input-bg-text');

        const quotes = ["The corridors are wide, but the paths are many.", "Do not trust the geometry.", "Cyan light is a guide, but also a trap."];
        document.getElementById('lore-text').innerText = `"${quotes[Math.floor(Math.random() * quotes.length)]}"`;

        nameInput.addEventListener('focus', () => { if (nameInput.value === "") { bgText.innerHTML = '<div class="dots"><span>.</span><span>.</span><span>.</span></div>'; bgText.style.opacity = "1"; } });
        nameInput.addEventListener('blur', () => { if (nameInput.value === "") { bgText.innerHTML = 'NAMETAG'; bgText.style.opacity = "1"; } });
        nameInput.addEventListener('input', (e) => {
            playUISound(90, 1.2, 0.25, 'triangle');
            e.target.value = e.target.value.replace(/[^A-Za-z]/g, '').toUpperCase();
            if (nameInput.value.length > 0) bgText.style.opacity = "0";
            else { bgText.style.opacity = "1"; bgText.innerHTML = '<div class="dots"><span>.</span><span>.</span><span>.</span></div>'; }
        });
        nameInput.addEventListener('keydown', (e) => e.stopPropagation());
        nameInput.addEventListener('keyup', (e) => e.stopPropagation());

        document.querySelectorAll('#main-ui button, #main-ui input').forEach(el => {
            el.addEventListener('mouseenter', () => playUISound(500, 0.5, 0.08, 'triangle'));
            if (el !== engageBtn) el.addEventListener('mousedown', () => playUISound(180, 1.5, 0.2, 'sine'));
            else el.addEventListener('mousedown', () => playUISound(100, 2.0, 0.4, 'sine'));
        });

        engageBtn.addEventListener('mousedown', () => {
            const grid = document.querySelector('.grid-container');
            grid.classList.remove('shake-active'); void grid.offsetWidth;
            grid.classList.add('shake-active');
            document.body.requestPointerLock();
        });

        document.addEventListener('pointerlockchange', () => {
            if (document.pointerLockElement === document.body) {
                uiContainer.style.display = 'none';
                gameActive = true;
                if (startTime === 0) startTime = Date.now();
                prevTime = performance.now();

                // NEW: Intro fade sequence — show operative name then fade out
                if (!introShown) {
                    introShown = true;
                    const fb = document.getElementById('fade-black');
                    const operativeName = nameInput.value || 'OPERATIVE';
                    // Override fade-black for intro text
                    fb.style.cssText = 'position:fixed;top:0;left:0;width:100%;height:100%;background:#000;z-index:200;display:flex;align-items:center;justify-content:center;opacity:1;transition:none;pointer-events:none;';
                    fb.innerHTML = `<div style="text-align:center;font-family:'Courier New',monospace;letter-spacing:4px;color:#d4c4a8;">
                        <div style="color:#d4af37;font-size:1.8em;font-weight:bold;margin-bottom:10px;">OPERATIVE: ${operativeName}</div>
                        <div style="color:#5e4835;font-size:0.9em;letter-spacing:6px;">SIGNAL LOCKED — DEPLOYING</div>
                    </div>`;
                    setTimeout(() => {
                        fb.style.transition = 'opacity 1.6s ease-in-out';
                        fb.style.opacity = '0';
                        setTimeout(() => {
                            fb.style.cssText = 'position:fixed;top:0;left:0;width:100%;height:100%;background:#000;z-index:105;opacity:0;transition:opacity 3s ease-in-out;pointer-events:none;';
                            fb.innerHTML = '';
                        }, 1700);
                    }, 1400);
                }
            } else if (!gameWon) {
                uiContainer.style.display = 'flex';
                document.getElementById('main-title').innerText = "SYSTEM PAUSED";
                engageBtn.innerText = "RESUME";
                gameActive = false;
                accumulatedTime += (Date.now() - startTime) / 1000;
                document.getElementById('menuOrbCount').innerText = orbsCollected;
                // Hide in-game prompts
                termPromptEl.style.display = 'none';
                doorLockedEl.style.display = 'none';
            }
        });

        document.addEventListener('mousemove', (e) => {
            if (document.pointerLockElement === document.body) {
                yaw -= e.movementX * SENSITIVITY; pitch -= e.movementY * SENSITIVITY;
                pitch = Math.max(-Math.PI / 2, Math.min(Math.PI / 2, pitch));
                camera.rotation.set(pitch, yaw, 0);
            }
        });

        document.addEventListener('keydown', (e) => {
            keys[e.code] = true;
            // NEW: E-key terminal activation
            if (e.code === 'KeyE' && gameActive && doorState === 'ready_for_terminal') {
                const dx = camera.position.x - (terminalWX + 1.5); // account for rotation
                const dz = camera.position.z - terminalWZ;
                if (Math.hypot(camera.position.x - terminalWX, camera.position.z - terminalWZ) < 9) {
                    doorState = 'valves_pressure';
                    initIndustrialAudio();
                    sirens.forEach(s => s.light.intensity = 50);
                    klaxonGain.gain.setTargetAtTime(0.015, audioCtx.currentTime, 0.1);
                    hissGain.gain.setTargetAtTime(0.1, audioCtx.currentTime, 0.1);
                    termScreenMat.color.setHex(0xff4400);
                    termBtnMat.color.setHex(0x00ff44);
                    termLight.color.setHex(0xff4400);
                    termLight.intensity = 3;
                    termPromptEl.style.display = 'none';
                    playUISound(220, 1.5, 0.6, 'sawtooth');
                }
            }
        });
        document.addEventListener('keyup', (e) => keys[e.code] = false);

        // ================================================================
        // COLLISION CHECK  (original — untouched)
        // ================================================================
        function isWall(x, z, radius) {
            const offset = Math.floor(MAZE_SIZE / 2);
            const minGridX = Math.floor((x - radius + TILE_SIZE / 2) / TILE_SIZE) + offset - 1;
            const maxGridX = Math.floor((x + radius + TILE_SIZE / 2) / TILE_SIZE) + offset + 1;
            const minGridZ = Math.floor((z - radius + TILE_SIZE / 2) / TILE_SIZE) + offset - 1;
            const maxGridZ = Math.floor((z + radius + TILE_SIZE / 2) / TILE_SIZE) + offset + 1;
            for (let i = minGridX; i <= maxGridX; i++) {
                for (let j = minGridZ; j <= maxGridZ; j++) {
                    if (i >= 0 && i < MAZE_SIZE && j >= 0 && j < MAZE_SIZE && maze[i][j] === 1) {
                        const wallCenterX = (i - offset) * TILE_SIZE; const wallCenterZ = (j - offset) * TILE_SIZE;
                        const closestX = Math.max(wallCenterX - TILE_SIZE / 2, Math.min(x, wallCenterX + TILE_SIZE / 2));
                        const closestZ = Math.max(wallCenterZ - TILE_SIZE / 2, Math.min(z, wallCenterZ + TILE_SIZE / 2));
                        if (((x - closestX) * (x - closestX) + (z - closestZ) * (z - closestZ)) < (radius * radius)) return true;
                    }
                }
            }
            if (Math.abs(x - doorGroup.position.x) < TILE_SIZE && Math.abs(z - doorGroup.position.z) < TILE_SIZE) {
                const playerBox = new THREE.Box3(new THREE.Vector3(x - radius, 0, z - radius), new THREE.Vector3(x + radius, player.height, z + radius));
                for (let i = 0; i < solidDoorParts.length; i++) { partBoxHelper.setFromObject(solidDoorParts[i]); if (playerBox.intersectsBox(partBoxHelper)) return true; }
            }
            return false;
        }

        // ================================================================
        // UPDATE LOOP
        // ================================================================
        function update() {
            if (!gameActive) return;

            const now = performance.now();
            const delta = Math.min((now - prevTime) / 1000, 0.05); // clamp delta so pausing doesn't cause huge jumps
            prevTime = now;
            const totalElapsed = (accumulatedTime + (Date.now() - startTime) / 1000).toFixed(1);
            if (!gameWon) document.getElementById('timeVal').innerText = totalElapsed;

            // Track explored cells for radar minimap outlines
            const pg = worldToGrid(camera.position.x, camera.position.z);
            exploredCells.add(`${pg.x},${pg.z}`);

            // ---- PLAYER MOVEMENT (original logic preserved) ----
            if (!gameWon) {
                const input = new THREE.Vector2(0, 0);
                if (keys['KeyW']) input.y -= 1; if (keys['KeyS']) input.y += 1;
                if (keys['KeyA']) input.x -= 1; if (keys['KeyD']) input.x += 1;
                if (input.length() > 0) input.normalize();

                const isTryingToMove = input.length() > 0;
                const isSprinting = keys['ShiftLeft'] && isTryingToMove && !player.isExhausted;
                currentlySprinting = isSprinting;

                // Stamina
                if (isSprinting) {
                    player.stamina -= 0.4;
                    if (player.stamina <= 0) player.isExhausted = true;
                } else {
                    player.stamina = Math.min(MAX_STAMINA, player.stamina + 0.9);
                    if (player.stamina >= MAX_STAMINA * 0.25) player.isExhausted = false;
                }
                const staminaPercent = (player.stamina / MAX_STAMINA) * 100;
                document.getElementById('stamina-bar').style.width = staminaPercent + '%';
                document.getElementById('stamina-bar').style.background = player.isExhausted ? '#8b0000' : 'linear-gradient(to bottom, #d4af37, #997a00)';

                // NEW: Flashlight flickers when stamina < 28%
                if (staminaPercent < 28) {
                    const flicker = 0.7 + 0.3 * Math.abs(Math.sin(now * 0.028 + Math.sin(now * 0.007) * 4));
                    flashLight.intensity = 50 * flicker;
                } else {
                    flashLight.intensity = 50;
                }

                // Movement
                const targetSpeed = isSprinting ? player.runSpeed : (isTryingToMove ? player.walkSpeed : 0);
                const targetVelocity = input.clone().multiplyScalar(targetSpeed);
                player.velocity.lerp(targetVelocity, 0.15);
                const moveX = player.velocity.x * Math.cos(yaw) + player.velocity.y * Math.sin(yaw);
                const moveZ = -player.velocity.x * Math.sin(yaw) + player.velocity.y * Math.cos(yaw);

                let tempX = camera.position.x; let tempZ = camera.position.z;
                if (!isWall(tempX + moveX, tempZ, player.radius)) tempX += moveX;
                if (!isWall(tempX, tempZ + moveZ, player.radius)) tempZ += moveZ;
                camera.position.x = tempX; camera.position.z = tempZ;

                const currentSpeed = player.velocity.length();
                if (currentSpeed > 0.02) {
                    const targetHz = isSprinting ? 3.5 : 1.5; const bobAmp = isSprinting ? 0.12 : 0.08;
                    player.headBobTimer += delta * targetHz * Math.PI * 2;
                    camera.position.y = player.height + Math.sin(player.headBobTimer) * bobAmp;

                    // NEW: Footstep sounds — triggered per half-bob cycle
                    const cycle = Math.floor(player.headBobTimer / Math.PI);
                    if (cycle > lastFootstepCycle) {
                        lastFootstepCycle = cycle;
                        playFootstep(isSprinting);
                    }

                    // NEW: Sprint sound alert to nearby enemies (throttled)
                    if (isSprinting) {
                        sprintAlertCooldown -= delta;
                        if (sprintAlertCooldown <= 0) {
                            sprintAlertCooldown = 0.6;
                            alertEnemiesInRadius(camera.position.x, camera.position.z, SPRINT_ALERT_RADIUS);
                        }
                    }
                } else {
                    camera.position.y += (player.height - camera.position.y) * 0.1;
                    player.headBobTimer += delta;
                }

                // NEW: FOV expands when sprinting (tunnel effect)
                const targetFOV = isSprinting ? 86 : 75;
                camera.fov += (targetFOV - camera.fov) * 0.08;
                camera.updateProjectionMatrix();
            }

            // NEW: Sprint/proximity vignette
            {
                const sprintI = currentlySprinting ? 0.42 : 0.0;
                vignetteEl.style.opacity = String(Math.min(0.9, sprintI));
                vignetteEl.style.background = currentlySprinting
                    ? 'radial-gradient(ellipse at center,transparent 30%,rgba(18,5,0,0.95) 100%)'
                    : 'radial-gradient(ellipse at center,transparent 38%,rgba(0,0,0,0.93) 100%)';
            }

            // ---- PARTICLES (original) ----
            for (let i = particles.length - 1; i >= 0; i--) {
                const p = particles[i]; p.position.addScaledVector(p.userData.vel, delta); p.userData.life -= delta;
                if (p.userData.type === 'steam') { p.userData.mat.opacity = (p.userData.life / 1.0) * 0.5; p.scale.setScalar(2.0 - p.userData.life); }
                else if (p.userData.type === 'spark') { p.userData.vel.y -= delta * 15; if (p.position.y < 0.1) { p.position.y = 0.1; p.userData.vel.y *= -0.5; } }
                if (p.userData.life <= 0) { scene.remove(p); if (p.userData.type === 'steam') p.userData.mat.dispose(); particles.splice(i, 1); }
            }

            // NEW: Corridor light flickering animation
            corridorLights.forEach(cl => {
                if (cl.isBroken) {
                    // Rapid irregular stutter
                    const t = now * 0.001 * cl.flickerRate + cl.seed;
                    const flicker = Math.abs(Math.sin(t * 7.3) * Math.sin(t * 3.1));
                    cl.light.intensity = Math.random() > 0.03 ? cl.baseIntensity * flicker : 0;
                    const c = cl.light.intensity > 0.3 ? 0x88aacc : 0x223344;
                    cl.strip.color.setHex(c);
                } else {
                    // Slow sinusoidal breathing
                    cl.light.intensity = cl.baseIntensity * (0.7 + 0.3 * Math.sin(now * 0.001 * cl.flickerRate + cl.seed));
                }
            });

            // ---- RADAR ----
            rCtx.clearRect(0, 0, radarCanvas.width, radarCanvas.height);

            // NEW: Draw explored cell outlines as faint dots
            rCtx.fillStyle = 'rgba(100, 85, 60, 0.25)';
            exploredCells.forEach(key => {
                const [gx, gz] = key.split(',').map(Number);
                const wp = getPos(gx, gz);
                const dx = wp.x - camera.position.x, dz = wp.z - camera.position.z;
                if (Math.hypot(dx, dz) > radarMaxDist) return;
                const lr = dx * Math.cos(yaw) - dz * Math.sin(yaw);
                const lf = -dx * Math.sin(yaw) - dz * Math.cos(yaw);
                rCtx.fillRect(rCenter + lr * radarScale - 1.5, rCenter - lf * radarScale - 1.5, 3, 3);
            });

            // Crosshair lines
            rCtx.strokeStyle = 'rgba(212, 196, 168, 0.2)'; rCtx.lineWidth = 1;
            rCtx.beginPath(); rCtx.moveTo(rCenter, 0); rCtx.lineTo(rCenter, radarCanvas.height);
            rCtx.moveTo(0, rCenter); rCtx.lineTo(radarCanvas.width, rCenter); rCtx.stroke();
            // Player arrow
            rCtx.fillStyle = '#d4c4a8';
            rCtx.beginPath(); rCtx.moveTo(rCenter, rCenter - 8); rCtx.lineTo(rCenter - 5, rCenter + 5); rCtx.lineTo(rCenter + 5, rCenter + 5); rCtx.fill();

            function drawBlip(worldX, worldZ, color, size, isRect) {
                const dx = worldX - camera.position.x; const dz = worldZ - camera.position.z;
                const localRight = dx * Math.cos(yaw) - dz * Math.sin(yaw);
                const localForward = -dx * Math.sin(yaw) - dz * Math.cos(yaw);
                const dist = Math.sqrt(localRight * localRight + localForward * localForward);
                let drawRight = localRight, drawForward = localForward;
                if (dist > radarMaxDist) { drawRight = (localRight / dist) * radarMaxDist; drawForward = (localForward / dist) * radarMaxDist; }
                const rx = rCenter + drawRight * radarScale; const ry = rCenter - drawForward * radarScale;
                rCtx.fillStyle = color;
                if (isRect) rCtx.fillRect(rx - size, ry - size, size * 2, size * 2);
                else { rCtx.beginPath(); rCtx.arc(rx, ry, size, 0, Math.PI * 2); rCtx.fill(); }
                return { rx, ry };
            }

            // Door blip (original)
            const dxDoor = doorGroup.position.x - camera.position.x; const dzDoor = doorGroup.position.z - camera.position.z;
            const lRight = dxDoor * Math.cos(yaw) - dzDoor * Math.sin(yaw);
            const lForward = -dxDoor * Math.sin(yaw) - dzDoor * Math.cos(yaw);
            let distToMapDoor = Math.sqrt(lRight * lRight + lForward * lForward);
            let rx = rCenter + lRight * radarScale; let ry = rCenter - lForward * radarScale;
            if (distToMapDoor > radarMaxDist) { rx = rCenter + (lRight / distToMapDoor) * radarMaxDist * radarScale; ry = rCenter - (lForward / distToMapDoor) * radarMaxDist * radarScale; }
            rCtx.fillStyle = '#55aa55'; rCtx.fillRect(rx - 5, ry - 7, 10, 14);
            rCtx.fillStyle = '#112211'; rCtx.fillRect(rx - 3, ry - 5, 6, 12);
            rCtx.fillStyle = '#d4af37'; rCtx.beginPath(); rCtx.arc(rx + 1, ry + 1, 1.5, 0, Math.PI * 2); rCtx.fill();

            // Orb blips
            orbs.forEach(orb => {
                if (orb.position.y > 0) drawBlip(orb.position.x, orb.position.z, orb.userData.isGold ? '#ffaa00' : '#d4af37', 2.5, false);
            });

            // ---- ENEMY AI STATE MACHINE ----
            let closestDist = 100;
            enemies.forEach((enemy, index) => {
                const ud = enemy.userData;
                const distToPlayer = camera.position.distanceTo(enemy.position);
                if (distToPlayer < closestDist) closestDist = distToPlayer;

                // ------ LIGHT DETECTION ------
                // Only check if not already alerted and within range
                if (ud.state !== 'alerted' && distToPlayer < LIGHT_DETECT_RANGE) {
                    const camFwd = new THREE.Vector3(0, 0, -1).applyQuaternion(camera.quaternion);
                    const camToEnemy = new THREE.Vector3().subVectors(enemy.position, camera.position).normalize();
                    const dotProduct = camFwd.dot(camToEnemy);
                    if (dotProduct > FLASHLIGHT_CONE_COS) {
                        // Enemy is inside flashlight cone — check wall occlusion
                        if (hasLineOfSight(camera.position.x, camera.position.z, enemy.position.x, enemy.position.z)) {
                            triggerAlert(enemy);
                        }
                    }
                }

                // ------ STATE TRANSITIONS ------
                if (ud.state === 'alerted') {
                    ud.alertTimer -= delta;
                    if (ud.alertTimer <= 0) {
                        // Expire to searching
                        ud.state = 'searching';
                        ud.pathUpdateTimer = 0;
                        ud.light.intensity = 3;
                    } else {
                        // Refresh BFS to player position (throttled every 1.4s)
                        ud.pathUpdateTimer -= delta;
                        if (ud.pathUpdateTimer <= 0) {
                            ud.pathUpdateTimer = 1.4;
                            const pg2 = worldToGrid(camera.position.x, camera.position.z);
                            const eg = worldToGrid(enemy.position.x, enemy.position.z);
                            const path = bfsPath(eg.x, eg.z, pg2.x, pg2.z);
                            if (path.length > 0) {
                                ud.pathQueue = path;
                                ud.lastKnownGrid = pg2;
                            }
                        }
                    }
                    ud.light.intensity = 7 + Math.sin(now * 0.01) * 2;
                } else if (ud.state === 'searching') {
                    ud.light.intensity = 3;
                    if (ud.lastKnownGrid) {
                        const lkPos = getPos(ud.lastKnownGrid.x, ud.lastKnownGrid.z);
                        const distToLK = Math.hypot(enemy.position.x - lkPos.x, enemy.position.z - lkPos.z);
                        if (distToLK < TILE_SIZE * 0.6) {
                            // Reached last known — return to patrol
                            ud.state = 'patrol';
                            ud.lastKnownGrid = null;
                            ud.pathQueue = [];
                            ud.light.intensity = 2;
                            enemy.material.color.setHex(0xff0000);
                            removeSpikes(enemy);
                        } else {
                            // Keep navigating to last known pos
                            ud.pathUpdateTimer -= delta;
                            if (ud.pathUpdateTimer <= 0) {
                                ud.pathUpdateTimer = 2.0;
                                const eg = worldToGrid(enemy.position.x, enemy.position.z);
                                ud.pathQueue = bfsPath(eg.x, eg.z, ud.lastKnownGrid.x, ud.lastKnownGrid.z);
                            }
                        }
                    } else {
                        ud.state = 'patrol';
                        removeSpikes(enemy);
                    }
                }

                // ------ MOVEMENT ------
                const moveSpeed = ud.state === 'alerted' ? 0.20 : ud.state === 'searching' ? 0.10 : 0.12;

                if ((ud.state === 'alerted' || ud.state === 'searching') && ud.pathQueue.length > 0) {
                    // Follow BFS path
                    const nextCell = ud.pathQueue[0];
                    const nextWorld = getPos(nextCell.x, nextCell.z);
                    const nextPos = new THREE.Vector3(nextWorld.x, 2.0, nextWorld.z);
                    if (enemy.position.distanceTo(nextPos) < TILE_SIZE * 0.45) ud.pathQueue.shift();
                    else ud.targetPos.copy(nextPos);
                } else if (ud.state === 'patrol') {
                    // Original random wander logic
                    if (!gameWon && enemy.position.distanceTo(ud.targetPos) < 0.5) {
                        const cx = Math.round(ud.targetPos.x / TILE_SIZE) + Math.floor(MAZE_SIZE / 2);
                        const cz = Math.round(ud.targetPos.z / TILE_SIZE) + Math.floor(MAZE_SIZE / 2);
                        const neighbors = [];
                        [[0,-1],[0,1],[-1,0],[1,0]].forEach(([dx2, dz2]) => {
                            const nx = cx + dx2, nz = cz + dz2;
                            if (nx >= 0 && nx < MAZE_SIZE && nz >= 0 && nz < MAZE_SIZE && maze[nx][nz] === 0) {
                                if (!(nx === ud.lastGrid.x && nz === ud.lastGrid.z)) neighbors.push({x: nx, z: nz});
                            }
                        });
                        if (neighbors.length === 0 && maze[ud.lastGrid.x][ud.lastGrid.z] === 0) neighbors.push(ud.lastGrid);
                        ud.lastGrid = {x: cx, z: cz};
                        const nextCell2 = neighbors.length > 0 ? neighbors[Math.floor(Math.random() * neighbors.length)] : ud.lastGrid;
                        ud.targetPos.set(getPos(nextCell2.x, nextCell2.z).x, 2.0, getPos(nextCell2.x, nextCell2.z).z);
                    }
                }

                const dir = new THREE.Vector3().subVectors(ud.targetPos, enemy.position);
                dir.y = 0;
                if (dir.length() > 0.01) { dir.normalize(); enemy.position.addScaledVector(dir, moveSpeed); }
                enemy.position.y = 2.0 + Math.sin(now * 0.003 + index) * 0.4;

                // NEW: Animate spikes when alerted or searching
                if (ud.spikeGroup) animateSpikes(ud.spikeGroup, now);

                // Radar blip — alerted enemies show brighter/larger
                if (ud.state === 'alerted') {
                    drawBlip(enemy.position.x, enemy.position.z, '#ff2222', 4, false);
                } else if (ud.state === 'searching') {
                    drawBlip(enemy.position.x, enemy.position.z, '#ff7722', 3, false);
                } else {
                    drawBlip(enemy.position.x, enemy.position.z, '#ff5555', 2.5, false);
                }

                // Death check (original)
                if (!gameWon && distToPlayer < 3.0 && gameActive) {
                    gameActive = false;
                    document.exitPointerLock();
                    const totalElapsedDeath = (accumulatedTime + (Date.now() - startTime) / 1000).toFixed(1);
                    document.getElementById('time-stat').innerText = totalElapsedDeath + 's';
                    document.getElementById('orb-stat').innerText = `${orbsCollected} / 12`;
                    document.getElementById('death-screen-ui').style.display = 'block';
                }
            });

            // Proximity shake + sting (original)
            if (!gameWon && closestDist < 12) {
                camera.position.x += (Math.random() - 0.5) * ((12 - closestDist) * 0.02);
                if (!hasPlayedSting) { playSting(); hasPlayedSting = true; }
            } else { hasPlayedSting = false; }

            // ---- ORB COLLECTION ----
            orbs.forEach(orb => {
                if (!gameWon && orb.position.y > 0 && camera.position.distanceTo(orb.position) < 3) {
                    orb.position.y = -1000;
                    orbsCollected++;
                    document.getElementById('orbCount').innerText = orbsCollected;
                    // NEW: Gold orb restores stamina + different chime
                    if (orb.userData.isGold) {
                        player.stamina = Math.min(MAX_STAMINA, player.stamina + MAX_STAMINA * 0.55);
                        player.isExhausted = false;
                        playOrbChime(true);
                    } else {
                        playOrbChime(false);
                    }
                    // NEW: Orb pickup alerts nearby enemies via sound
                    alertEnemiesInRadius(orb.position.x, orb.position.z, 20);

                    if (orbsCollected === totalOrbs && doorState === 'closed') {
                        // NEW: Gate door behind terminal — player must press E at terminal
                        doorState = 'ready_for_terminal';
                        termLight.intensity = 2.5; // Terminal glows green to signal readiness
                        termScreenMat.color.setHex(0x00ff44);
                    }
                }
            });

            // ---- TERMINAL PROXIMITY PROMPT ----
            if (gameActive && !gameWon) {
                const distToTerm = Math.hypot(camera.position.x - terminalWX, camera.position.z - terminalWZ);
                if (doorState === 'ready_for_terminal' && distToTerm < 9) {
                    termPromptEl.style.display = 'block';
                    doorLockedEl.style.display = 'none';
                } else {
                    termPromptEl.style.display = 'none';
                    // Show door locked message if player near door but needs orbs
                    const distToDoor = camera.position.distanceTo(doorGroup.position);
                    if (distToDoor < 18 && doorState === 'closed' && orbsCollected < totalOrbs) {
                        doorLockedEl.style.display = 'block';
                        const el = document.getElementById('orbsNeededCount');
                        if (el) el.innerText = totalOrbs - orbsCollected;
                    } else {
                        doorLockedEl.style.display = 'none';
                    }
                }
            }

            // ---- MULTI-STAGE DOOR ANIMATION (original — untouched) ----
            if (!gameWon) camera.rotation.z = 0;
            if (doorState !== 'closed' && doorState !== 'open' && doorState !== 'ready_for_terminal') {
                const distToDoor = camera.position.distanceTo(doorGroup.position);
                const volScale = Math.max(0, 1 - (distToDoor / 50));

                sirens.forEach((s, idx) => { s.group.rotation.y += delta * (idx % 2 === 0 ? 2 : -2); });
                if (klaxonGain) klaxonGain.gain.setTargetAtTime(volScale * 0.015, audioCtx.currentTime, 0.1);
                if (!gameWon && distToDoor < 45) { const shakeIntensity = (45 - distToDoor) * 0.0015; camera.rotation.z = (Math.random() - 0.5) * shakeIntensity; }

                if (doorState === 'valves_pressure') {
                    if (valves[0].rotation.z < Math.PI * 4) {
                        valves.forEach(v => v.rotation.z += delta * Math.PI);
                        if (Math.random() > 0.5) emitSteam(doorGroup.position.x, 1, doorGroup.position.z);
                        if (hissGain) hissGain.gain.setTargetAtTime(volScale * 0.1, audioCtx.currentTime, 0.1);
                    } else {
                        doorState = 'vault_unlock';
                        if (hissGain) hissGain.gain.setTargetAtTime(0, audioCtx.currentTime, 0.1);
                        if (vaultGain) vaultGain.gain.setTargetAtTime(volScale * 0.04, audioCtx.currentTime, 0.1);
                    }
                } else if (doorState === 'vault_unlock') {
                    if (vaultWheelGroup.rotation.z < Math.PI) {
                        vaultWheelGroup.rotation.z += delta * (Math.PI / 5); vaultWheelGroup.position.x -= delta * 0.2;
                        if (vaultGain) vaultGain.gain.setTargetAtTime(volScale * 0.04, audioCtx.currentTime, 0.1);
                    } else {
                        doorState = 'unlatching';
                        matIndicator.color.setHex(0x00ff00);
                        if (vaultGain) vaultGain.gain.setTargetAtTime(0, audioCtx.currentTime, 0.1);
                        if (latchGain) latchGain.gain.setTargetAtTime(volScale * 0.06, audioCtx.currentTime, 0.1);
                    }
                } else if (doorState === 'unlatching') {
                    if (latchL.position.x > -6) {
                        const latchSpeed = delta * 0.5; latchL.position.x -= latchSpeed; latchR.position.x += latchSpeed;
                        deadboltsLeft.forEach(b => b.position.x -= latchSpeed * 3); deadboltsRight.forEach(b => b.position.x += latchSpeed * 3);
                        if (latchGain) latchGain.gain.setTargetAtTime(volScale * 0.06, audioCtx.currentTime, 0.1);
                    } else {
                        doorState = 'retracting_pistons';
                        if (latchGain) latchGain.gain.setTargetAtTime(0, audioCtx.currentTime, 0.1);
                        if (pistonGain) pistonGain.gain.setTargetAtTime(volScale * 0.15, audioCtx.currentTime, 0.1);
                    }
                } else if (doorState === 'retracting_pistons') {
                    if (pistonGroup.position.y < 5) {
                        pistonGroup.position.y += delta * 1.0;
                        if (pistonGain) pistonGain.gain.setTargetAtTime(volScale * 0.15, audioCtx.currentTime, 0.1);
                    } else {
                        doorState = 'sliding';
                        if (pistonGain) pistonGain.gain.setTargetAtTime(0, audioCtx.currentTime, 0.1);
                        if (gearGain) gearGain.gain.setTargetAtTime(volScale * 0.08, audioCtx.currentTime, 0.1);
                    }
                } else if (doorState === 'sliding') {
                    if (doorHalfLeftGroup.position.x > -panelWidth - 2) {
                        const slideAmount = delta * 0.444;
                        doorHalfLeftGroup.position.x -= slideAmount; doorHalfRightGroup.position.x += slideAmount;
                        const gearRotation = slideAmount / gearRadius;
                        mainGearLeft.rotation.z -= gearRotation; mainGearRight.rotation.z += gearRotation;
                        const helperRatio = gearRadius / helperGearRadius;
                        helperGearLeft.rotation.z += gearRotation * helperRatio; helperGearRight.rotation.z -= gearRotation * helperRatio;
                        if (Math.random() > 0.4) emitSpark(doorGroup.position.x - 3, 11 + gearRadius, doorGroup.position.z - 0.8);
                        if (Math.random() > 0.4) emitSpark(doorGroup.position.x + 3, 11 + gearRadius, doorGroup.position.z - 0.8);
                        if (gearGain) gearGain.gain.setTargetAtTime(volScale * 0.08, audioCtx.currentTime, 0.1);
                    } else {
                        doorState = 'open';
                        sirens.forEach(s => s.light.intensity = 0); matGlassRed.emissive.setHex(0x110000);
                        const fadeOutTime = audioCtx.currentTime + 1.5;
                        if (klaxonGain) klaxonGain.gain.linearRampToValueAtTime(0, fadeOutTime);
                        if (gearGain) gearGain.gain.linearRampToValueAtTime(0, fadeOutTime);
                    }
                }
            }

            // ---- WIN CONDITION (original) ----
            if (doorState === 'open' && camera.position.z > doorGroup.position.z + 1.5 && !gameWon) {
                gameWon = true;
                document.exitPointerLock();
                const winScreen = document.getElementById('win-screen');
                const fadeBlack = document.getElementById('fade-black');
                winScreen.style.display = 'flex';
                setTimeout(() => { fadeBlack.style.opacity = '1'; winScreen.style.opacity = '1'; }, 50);
                document.getElementById('finalTime').innerText = `FINAL TIME: ${totalElapsed}s`;
                termPromptEl.style.display = 'none'; doorLockedEl.style.display = 'none';
                try { if (klaxonOsc) klaxonOsc.stop(); if (latchOsc) latchOsc.stop(); if (pistonOsc) pistonOsc.stop(); if (gearOsc) gearOsc.stop(); if (vaultOsc) vaultOsc.stop(); if (hissSrc) hissSrc.stop(); } catch (e) {}
            }
        }

        function animate() { requestAnimationFrame(animate); update(); renderer.render(scene, camera); }
        animate();

        window.addEventListener('resize', () => {
            camera.aspect = window.innerWidth / window.innerHeight;
            camera.updateProjectionMatrix();
            renderer.setSize(window.innerWidth, window.innerHeight);
        });

        document.getElementById('reboot-btn').addEventListener('click', () => {
            const deathUI = document.getElementById('death-screen-ui');
            deathUI.style.transition = 'opacity 0.5s';
            deathUI.style.opacity = '0';
            setTimeout(() => { location.reload(); }, 500);
        });
