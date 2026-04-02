
        import * as THREE from 'three';

        // --- Maze Generation ---
        const MAZE_SIZE = 25; const TILE_SIZE = 12; 
        const maze = Array(MAZE_SIZE).fill(null).map(() => Array(MAZE_SIZE).fill(1));
        const emptyCells = [];

        function carveMaze(x, y) {
            maze[x][y] = 0;
            const dirs = [[0,-1], [0,1], [-1,0], [1,0]].sort(() => Math.random() - 0.5);
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
        for(let i = -1; i <= 1; i++) { for(let j = -3; j <= -1; j++) { maze[exitGridX + i][exitGridZ + j] = 0; } }
        maze[exitGridX][exitGridZ] = 0; 

        for(let i=0; i<MAZE_SIZE; i++) { for(let j=0; j<MAZE_SIZE; j++) { if(maze[i][j] === 0) emptyCells.push({x: i, z: j}); } }

        // --- Game Logic ---
        const totalOrbs = 12; let orbsCollected = 0; let gameActive = false; let gameWon = false;
        let startTime = 0; let accumulatedTime = 0; let hasPlayedSting = false; let prevTime = performance.now(); 

        document.getElementById('totalOrbsUI').innerText = totalOrbs;

        let yaw = Math.PI; let pitch = 0; const SENSITIVITY = 0.002;

        // Track sprint state for vignette (accessible outside movement block)
        let currentlySprinting = false;

        // --- STAMINA ---
        const MAX_STAMINA = 200;
        const player = {
            height: 2.1, radius: 0.8, walkSpeed: 0.22, runSpeed: 0.48,
            stamina: MAX_STAMINA, isExhausted: false,
            velocity: new THREE.Vector2(0, 0), headBobTimer: 0,
            lastFootstepCycle: 0   // NEW: footstep tracking
        };
        const keys = {};

        const radarCanvas = document.getElementById('radar'); const rCtx = radarCanvas.getContext('2d');
        const rCenter = radarCanvas.width / 2; const radarMaxDist = 120; const radarScale = (rCenter - 10) / radarMaxDist;

        // =============================================
        // AUDIO ENGINE
        // =============================================
        const audioCtx = new (window.AudioContext || window.webkitAudioContext)();
        let klaxonOsc, klaxonGain, vaultOsc, vaultGain, latchOsc, latchGain, pistonOsc, pistonGain, gearOsc, gearGain, hissSrc, hissGain;

        // NEW: Ambient audio refs
        let ambientGainNode, proximityBreathGain, ambientStarted = false;

        // --- Door sequence industrial audio (unchanged) ---
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
            const bufferSize = audioCtx.sampleRate * 2; const noiseBuffer = audioCtx.createBuffer(1, bufferSize, audioCtx.sampleRate);
            const output = noiseBuffer.getChannelData(0); for (let i = 0; i < bufferSize; i++) output[i] = Math.random() * 2 - 1;
            hissSrc = audioCtx.createBufferSource(); hissSrc.buffer = noiseBuffer; hissSrc.loop = true;
            const hissFilter = audioCtx.createBiquadFilter(); hissFilter.type = 'highpass'; hissFilter.frequency.value = 1000;
            hissGain = audioCtx.createGain(); hissGain.gain.value = 0;
            hissSrc.connect(hissFilter); hissFilter.connect(hissGain); hissGain.connect(audioCtx.destination); hissSrc.start();
        }

        // --- NEW: Ambient drone + proximity breathing, starts on game entry ---
        function startAmbientAudio() {
            if (ambientStarted) return;
            ambientStarted = true;
            if (audioCtx.state === 'suspended') audioCtx.resume();

            // Three layered detuned sine waves (deep sub-bass drone)
            ambientGainNode = audioCtx.createGain();
            ambientGainNode.gain.setValueAtTime(0, audioCtx.currentTime);

            [40.0, 41.4, 80.7].forEach(freq => {
                const osc = audioCtx.createOscillator();
                osc.type = 'sine'; osc.frequency.value = freq;
                osc.connect(ambientGainNode); osc.start();
            });

            // Slow breathing LFO (0.07 Hz swell)
            const swell = audioCtx.createOscillator(); swell.frequency.value = 0.07;
            const swellGain = audioCtx.createGain(); swellGain.gain.value = 0.007;
            swell.connect(swellGain); swellGain.connect(ambientGainNode.gain); swell.start();

            ambientGainNode.connect(audioCtx.destination);
            // Fade drone in over 4 seconds so it isn't jarring
            ambientGainNode.gain.linearRampToValueAtTime(0.045, audioCtx.currentTime + 4);

            // --- Proximity breathing: bandpass noise modulated by fast tremolo ---
            const bufSize = audioCtx.sampleRate * 2;
            const nBuf = audioCtx.createBuffer(1, bufSize, audioCtx.sampleRate);
            const nData = nBuf.getChannelData(0);
            for (let i = 0; i < bufSize; i++) nData[i] = Math.random() * 2 - 1;

            const nSrc = audioCtx.createBufferSource();
            nSrc.buffer = nBuf; nSrc.loop = true;

            const bandpass = audioCtx.createBiquadFilter();
            bandpass.type = 'bandpass'; bandpass.frequency.value = 260; bandpass.Q.value = 4;

            // Tremolo LFO at ~5.5 Hz gives an anxious flutter
            const tremolo = audioCtx.createOscillator(); tremolo.frequency.value = 5.5;
            const tremoloGain = audioCtx.createGain(); tremoloGain.gain.value = 0;
            tremolo.connect(tremoloGain);

            proximityBreathGain = audioCtx.createGain(); proximityBreathGain.gain.value = 0;
            // Connect tremolo to modulate the master gain on the breath
            tremoloGain.connect(proximityBreathGain.gain);

            tremolo.start(); nSrc.start();
            nSrc.connect(bandpass); bandpass.connect(proximityBreathGain);
            proximityBreathGain.connect(audioCtx.destination);
        }

        // --- NEW: Footstep sound — filtered noise burst ---
        function playFootstep(isSprinting) {
            if (!audioCtx || audioCtx.state === 'suspended') return;
            const bufSize = Math.floor(audioCtx.sampleRate * 0.045);
            const buf = audioCtx.createBuffer(1, bufSize, audioCtx.sampleRate);
            const data = buf.getChannelData(0);
            // Decaying noise envelope — exponential tail gives a solid "thud"
            for (let i = 0; i < bufSize; i++) {
                data[i] = (Math.random() * 2 - 1) * Math.pow(1 - i / bufSize, 5);
            }
            const src = audioCtx.createBufferSource(); src.buffer = buf;
            const lpf = audioCtx.createBiquadFilter();
            lpf.type = 'lowpass'; lpf.frequency.value = isSprinting ? 750 : 460;
            const gain = audioCtx.createGain(); gain.gain.value = isSprinting ? 0.55 : 0.32;
            src.connect(lpf); lpf.connect(gain); gain.connect(audioCtx.destination);
            src.start();
        }

        // --- NEW: Orb collection chime — ascending triangle-wave triplet ---
        function playOrbCollect() {
            if (!audioCtx || audioCtx.state === 'suspended') return;
            [440, 660, 880].forEach((freq, i) => {
                const osc = audioCtx.createOscillator();
                const g = audioCtx.createGain();
                osc.type = 'triangle'; osc.frequency.value = freq;
                const t = audioCtx.currentTime + i * 0.09;
                g.gain.setValueAtTime(0, t);
                g.gain.linearRampToValueAtTime(0.28, t + 0.01);
                g.gain.exponentialRampToValueAtTime(0.001, t + 0.22);
                osc.connect(g); g.connect(audioCtx.destination);
                osc.start(t); osc.stop(t + 0.22);
            });
        }

        // --- Sting (unchanged) ---
        function playSting() {
            if (audioCtx.state === 'suspended') audioCtx.resume();
            const osc = audioCtx.createOscillator(); const gain = audioCtx.createGain();
            osc.type = 'sawtooth'; osc.frequency.setValueAtTime(120, audioCtx.currentTime); osc.frequency.exponentialRampToValueAtTime(30, audioCtx.currentTime + 1);
            gain.gain.setValueAtTime(0.2, audioCtx.currentTime); gain.gain.exponentialRampToValueAtTime(0.01, audioCtx.currentTime + 1);
            osc.connect(gain); gain.connect(audioCtx.destination); osc.start(); osc.stop(audioCtx.currentTime + 1);
        }

        // =============================================
        // PROCEDURAL TEXTURES
        // =============================================

        // --- NEW: Stone block wall texture ---
        function createStoneBlockTexture() {
            const c = document.createElement('canvas'); c.width = 512; c.height = 512;
            const ctx = c.getContext('2d');
            const blockW = 128, blockH = 64;

            // Base dark stone fill
            ctx.fillStyle = '#1b2d1b'; ctx.fillRect(0, 0, 512, 512);

            // Draw individual stone blocks (alternating offset rows like brickwork)
            for (let row = 0; row < 8; row++) {
                for (let col = -1; col < 5; col++) {
                    const offsetX = (row % 2 === 0) ? 0 : blockW / 2;
                    const bx = col * blockW + offsetX;
                    const by = row * blockH;

                    // Varied per-stone tone
                    const shade = Math.floor(Math.random() * 16);
                    ctx.fillStyle = `rgb(${24 + shade}, ${44 + shade}, ${24 + shade})`;
                    ctx.fillRect(bx + 3, by + 3, blockW - 6, blockH - 6);

                    // Grime noise specks
                    for (let i = 0; i < 70; i++) {
                        ctx.fillStyle = `rgba(0,0,0,${Math.random() * 0.2})`;
                        ctx.fillRect(
                            bx + 3 + Math.random() * (blockW - 6),
                            by + 3 + Math.random() * (blockH - 6),
                            Math.random() * 7 + 1, Math.random() * 7 + 1
                        );
                    }
                    // Rust / moisture streak (random per-block)
                    if (Math.random() > 0.55) {
                        const sx = bx + 10 + Math.random() * (blockW - 20);
                        const grad = ctx.createLinearGradient(sx, by, sx + 2, by + blockH);
                        grad.addColorStop(0,   'rgba(90,42,8,0)');
                        grad.addColorStop(0.3, 'rgba(95,46,8,0.4)');
                        grad.addColorStop(1,   'rgba(70,32,5,0)');
                        ctx.fillStyle = grad; ctx.fillRect(sx, by, 4, blockH);
                    }
                    // Highlight edge (top) for a slight 3D look
                    ctx.fillStyle = 'rgba(255,255,255,0.03)';
                    ctx.fillRect(bx + 3, by + 3, blockW - 6, 3);
                }
            }

            // Mortar lines — dark grid
            ctx.strokeStyle = '#091209'; ctx.lineWidth = 3;
            for (let row = 0; row <= 8; row++) {
                ctx.beginPath(); ctx.moveTo(0, row * blockH); ctx.lineTo(512, row * blockH); ctx.stroke();
            }
            for (let row = 0; row < 8; row++) {
                const offsetX = (row % 2 === 0) ? 0 : blockW / 2;
                for (let col = -1; col <= 5; col++) {
                    const bx = col * blockW + offsetX;
                    ctx.beginPath(); ctx.moveTo(bx, row * blockH); ctx.lineTo(bx, (row + 1) * blockH); ctx.stroke();
                }
            }

            const tex = new THREE.CanvasTexture(c);
            tex.wrapS = tex.wrapT = THREE.RepeatWrapping;
            tex.repeat.set(1, 1.2);
            return tex;
        }

        // --- NEW: Metal floor plate texture ---
        function createFloorTexture() {
            const c = document.createElement('canvas'); c.width = 512; c.height = 512;
            const ctx = c.getContext('2d');
            ctx.fillStyle = '#161616'; ctx.fillRect(0, 0, 512, 512);
            const plateSize = 128;

            for (let row = 0; row < 4; row++) {
                for (let col = 0; col < 4; col++) {
                    const shade = Math.floor(Math.random() * 14);
                    ctx.fillStyle = `rgb(${26 + shade}, ${26 + shade}, ${28 + shade})`;
                    ctx.fillRect(col * plateSize + 2, row * plateSize + 2, plateSize - 4, plateSize - 4);

                    // Screw bolts at each corner
                    const screws = [
                        [col * plateSize + 9,              row * plateSize + 9],
                        [col * plateSize + plateSize - 9,  row * plateSize + 9],
                        [col * plateSize + 9,              row * plateSize + plateSize - 9],
                        [col * plateSize + plateSize - 9,  row * plateSize + plateSize - 9],
                    ];
                    screws.forEach(([sx, sy]) => {
                        ctx.fillStyle = '#272727'; ctx.beginPath(); ctx.arc(sx, sy, 5.5, 0, Math.PI * 2); ctx.fill();
                        ctx.fillStyle = '#0f0f0f'; ctx.beginPath(); ctx.arc(sx, sy, 2.8, 0, Math.PI * 2); ctx.fill();
                        // Phillips cross on bolt head
                        ctx.strokeStyle = '#333'; ctx.lineWidth = 1.2;
                        ctx.beginPath(); ctx.moveTo(sx - 3, sy); ctx.lineTo(sx + 3, sy); ctx.stroke();
                        ctx.beginPath(); ctx.moveTo(sx, sy - 3); ctx.lineTo(sx, sy + 3); ctx.stroke();
                    });

                    // Horizontal grime streaks across plate
                    for (let i = 0; i < 22; i++) {
                        ctx.fillStyle = `rgba(0,0,0,${Math.random() * 0.13})`;
                        ctx.fillRect(
                            col * plateSize + Math.random() * plateSize,
                            row * plateSize + Math.random() * plateSize,
                            Math.random() * 25 + 2, Math.random() * 2 + 1
                        );
                    }
                    // Subtle highlight on top edge of each plate
                    ctx.fillStyle = 'rgba(255,255,255,0.025)';
                    ctx.fillRect(col * plateSize + 2, row * plateSize + 2, plateSize - 4, 2);
                }
            }

            // Plate divider seams
            ctx.strokeStyle = '#0d0d0d'; ctx.lineWidth = 3;
            for (let i = 0; i <= 4; i++) {
                ctx.beginPath(); ctx.moveTo(i * plateSize, 0); ctx.lineTo(i * plateSize, 512); ctx.stroke();
                ctx.beginPath(); ctx.moveTo(0, i * plateSize); ctx.lineTo(512, i * plateSize); ctx.stroke();
            }

            const tex = new THREE.CanvasTexture(c);
            tex.wrapS = tex.wrapT = THREE.RepeatWrapping;
            tex.repeat.set(7, 7);
            return tex;
        }

        // --- Original grime texture (kept for door panels) ---
        function createGrimeTexture() {
            const c = document.createElement('canvas'); c.width = 512; c.height = 512; const ctx = c.getContext('2d');
            ctx.fillStyle = '#2a2a2a'; ctx.fillRect(0,0,512,512);
            for(let i=0; i<10000; i++) {
                ctx.fillStyle = Math.random() > 0.5 ? 'rgba(0,0,0,0.1)' : 'rgba(80,60,40,0.1)';
                ctx.beginPath(); ctx.arc(Math.random()*512, Math.random()*512, Math.random()*4, 0, Math.PI*2); ctx.fill();
            }
            const tex = new THREE.CanvasTexture(c); tex.wrapS = tex.wrapT = THREE.RepeatWrapping; tex.repeat.set(2, 2); return tex;
        }

        function createHazardTexture() {
            const c = document.createElement('canvas'); c.width = 256; c.height = 256; const ctx = c.getContext('2d');
            ctx.fillStyle = '#d4af37'; ctx.fillRect(0,0,256,256); ctx.fillStyle = '#111';
            for(let i=-256; i<512; i+=64) { ctx.beginPath(); ctx.moveTo(i, 0); ctx.lineTo(i+32, 0); ctx.lineTo(i+288, 256); ctx.lineTo(i+256, 256); ctx.fill(); }
            const tex = new THREE.CanvasTexture(c); tex.wrapS = tex.wrapT = THREE.RepeatWrapping; return tex;
        }

        // =============================================
        // SCENE & LIGHTING
        // =============================================
        const scene = new THREE.Scene(); scene.background = new THREE.Color(0x0c121a); scene.fog = new THREE.Fog(0x0c121a, 15, 120); 
        const camera = new THREE.PerspectiveCamera(75, window.innerWidth / window.innerHeight, 0.1, 1000); camera.rotation.order = 'YXZ';
        
        const renderer = new THREE.WebGLRenderer({ antialias: true }); renderer.setSize(window.innerWidth, window.innerHeight);
        renderer.shadowMap.enabled = true; renderer.shadowMap.type = THREE.PCFSoftShadowMap; document.body.appendChild(renderer.domElement);

        const hemiLight = new THREE.HemisphereLight(0xffffff, 0x444444, 0.6); scene.add(hemiLight);
        const flashLight = new THREE.SpotLight(0xffffe6, 50.0, 500, Math.PI / 5, 0.6, 1.0);
        flashLight.position.set(0, 0, 0); flashLight.castShadow = true; flashLight.shadow.bias = -0.001;
        camera.add(flashLight); camera.add(flashLight.target); flashLight.target.position.set(0, 0, -1); scene.add(camera);

        // =============================================
        // MATERIALS
        // =============================================
        const matDarkMetal = new THREE.MeshStandardMaterial({ map: createGrimeTexture(), metalness: 0.8, roughness: 0.7 });
        const matRustyFrame = new THREE.MeshStandardMaterial({ color: 0x3d352b, metalness: 0.9, roughness: 0.9 });
        const matBrightSteel = new THREE.MeshStandardMaterial({ color: 0xaaaaaa, metalness: 1.0, roughness: 0.2 }); 
        const matHazard = new THREE.MeshStandardMaterial({ map: createHazardTexture(), metalness: 0.3, roughness: 0.8 });
        const matWarningYellow = new THREE.MeshStandardMaterial({ color: 0xffaa00, metalness: 0.4, roughness: 0.7 });
        const matBlackHole = new THREE.MeshStandardMaterial({ color: 0x030303, roughness: 1.0 });
        const matGlassRed = new THREE.MeshStandardMaterial({ color: 0xff0000, emissive: 0x550000, transparent: true, opacity: 0.8 });
        const matIndicator = new THREE.MeshBasicMaterial({ color: 0xff0000 }); 

        // =============================================
        // PARTICLE SYSTEMS
        // =============================================
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

        // =============================================
        // COLLISION & LEVEL BUILDING
        // =============================================
        const solidDoorParts = []; const partBoxHelper = new THREE.Box3(); 
        function registerSolid(mesh) { solidDoorParts.push(mesh); }

        function createGearMesh(radius, depth, teethCount) {
            const gearGroup = new THREE.Group();
            const core = new THREE.Mesh(new THREE.CylinderGeometry(radius * 0.85, radius * 0.85, depth, 16), matBrightSteel);
            core.rotation.x = Math.PI / 2; core.castShadow = true; gearGroup.add(core);
            const toothGeo = new THREE.BoxGeometry((Math.PI * radius * 2)/(teethCount * 2), radius * 0.25, depth);
            for(let i = 0; i < teethCount; i++) {
                const angle = (i / teethCount) * Math.PI * 2; const tooth = new THREE.Mesh(toothGeo, matBrightSteel);
                tooth.position.set(Math.cos(angle) * radius * 0.95, Math.sin(angle) * radius * 0.95, 0);
                tooth.rotation.z = angle + Math.PI/2; tooth.castShadow = true; gearGroup.add(tooth);
            }
            const axle = new THREE.Mesh(new THREE.CylinderGeometry(radius * 0.3, radius * 0.3, depth + 0.2, 12), matDarkMetal);
            axle.rotation.x = Math.PI / 2; gearGroup.add(axle);
            const hitBox = new THREE.Mesh(new THREE.BoxGeometry(radius * 2, radius * 2, depth), new THREE.MeshBasicMaterial({visible: false}));
            gearGroup.add(hitBox); registerSolid(hitBox); return gearGroup;
        }

        function getPos(i, j) { return { x: (i - Math.floor(MAZE_SIZE / 2)) * TILE_SIZE, z: (j - Math.floor(MAZE_SIZE / 2)) * TILE_SIZE }; }

        // --- Floor: now with metal plate texture ---
        const floor = new THREE.Mesh(
            new THREE.PlaneGeometry(MAZE_SIZE * TILE_SIZE, MAZE_SIZE * TILE_SIZE),
            new THREE.MeshStandardMaterial({ map: createFloorTexture(), roughness: 0.85, metalness: 0.4 })
        );
        floor.rotation.x = -Math.PI / 2; floor.receiveShadow = true; scene.add(floor);

        // --- Walls: now with stone block texture ---
        const wallGeo = new THREE.BoxGeometry(TILE_SIZE, 14, TILE_SIZE);
        const wallMat = new THREE.MeshStandardMaterial({ map: createStoneBlockTexture(), roughness: 0.85, metalness: 0.1 });
        for (let i = 0; i < MAZE_SIZE; i++) {
            for (let j = 0; j < MAZE_SIZE; j++) {
                if (maze[i][j] === 1) {
                    const wall = new THREE.Mesh(wallGeo, wallMat); const pos = getPos(i, j); wall.position.set(pos.x, 7, pos.z);
                    wall.castShadow = true; wall.receiveShadow = true; scene.add(wall);
                }
            }
        }

        const startPos = getPos(1, 1); camera.position.set(startPos.x, player.height, startPos.z); camera.rotation.set(0, yaw, 0);

        // =============================================
        // CINEMATIC TITAN DOOR (unchanged)
        // =============================================
        let doorState = 'closed'; const doorStartWorldPos = getPos(exitGridX, exitGridZ);
        const doorGroup = new THREE.Group(); doorGroup.position.set(doorStartWorldPos.x, 0, doorStartWorldPos.z); 

        const frameHeight = 16; const frameZ = -1.5; const doorZPos = 0.5; const panelWidth = 5.0; 

        const lintel = new THREE.Mesh(new THREE.BoxGeometry(16, 4, 2), matRustyFrame); lintel.position.set(0, frameHeight - 2, frameZ); lintel.castShadow = true; lintel.receiveShadow = true; doorGroup.add(lintel); registerSolid(lintel);
        const leftPillar = new THREE.Mesh(new THREE.BoxGeometry(4, frameHeight, 2), matRustyFrame); leftPillar.position.set(-6, frameHeight / 2, frameZ); leftPillar.castShadow = true; leftPillar.receiveShadow = true; doorGroup.add(leftPillar); registerSolid(leftPillar);
        const rightPillar = new THREE.Mesh(new THREE.BoxGeometry(4, frameHeight, 2), matRustyFrame); rightPillar.position.set(6, frameHeight / 2, frameZ); rightPillar.castShadow = true; rightPillar.receiveShadow = true; doorGroup.add(rightPillar); registerSolid(rightPillar);

        const sirens = [];
        const createSiren = (x, z) => {
            const sGroup = new THREE.Group(); sGroup.position.set(x, frameHeight - 4, z);
            const bulb = new THREE.Mesh(new THREE.CylinderGeometry(0.5, 0.5, 1, 16), matGlassRed); sGroup.add(bulb);
            const spot = new THREE.SpotLight(0xff0000, 0, 40, Math.PI/6, 0.5, 1);
            spot.position.set(0,0,0); spot.target.position.set(0, -10, 10);
            spot.castShadow = true; spot.shadow.mapSize.width = 512; spot.shadow.mapSize.height = 512;
            spot.shadow.camera.near = 1; spot.shadow.camera.far = 40; spot.shadow.bias = -0.001;
            sGroup.add(spot); sGroup.add(spot.target);
            doorGroup.add(sGroup); sirens.push({group: sGroup, light: spot});
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
        const boltGeo = new THREE.CylinderGeometry(0.3, 0.3, 3, 16); boltGeo.rotateZ(Math.PI/2);
        for(let y of [-3, -1, 1, 3]) {
            const bL = new THREE.Mesh(boltGeo, matBrightSteel); bL.position.set(1.5, y, 0); doorHalfLeftGroup.add(bL); deadboltsLeft.push(bL);
            const bR = new THREE.Mesh(boltGeo, matBrightSteel); bR.position.set(-1.5, y, 0); doorHalfRightGroup.add(bR); deadboltsRight.push(bR);
        }

        const vaultWheelGroup = new THREE.Group(); vaultWheelGroup.position.set(panelWidth/2, 0, -0.7); doorHalfLeftGroup.add(vaultWheelGroup);
        const vaultCore = createGearMesh(2.5, 0.8, 16); vaultWheelGroup.add(vaultCore);
        const vaultSocket = new THREE.Mesh(new THREE.CylinderGeometry(2.6, 2.6, 0.2, 16), matBlackHole); vaultSocket.rotation.x = Math.PI/2; vaultSocket.position.set(-panelWidth/2, 0, -0.6); doorHalfRightGroup.add(vaultSocket);

        const valves = [];
        for(let py of [-3, 3]) {
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

        const pistonGroup = new THREE.Group(); doorGroup.add(pistonGroup); const pistonGeo = new THREE.BoxGeometry(1.5, 6, 1.5);
        const pistonL = new THREE.Mesh(pistonGeo, matHazard); pistonL.position.set(-3.5, 7, -0.8); pistonL.castShadow = true; pistonGroup.add(pistonL); registerSolid(pistonL);
        const pistonR = new THREE.Mesh(pistonGeo, matHazard); pistonR.position.set(3.5, 7, -0.8); pistonR.castShadow = true; pistonGroup.add(pistonR); registerSolid(pistonR);
        scene.add(doorGroup);

        // =============================================
        // ITEMS & ENEMIES
        // =============================================
        const orbs = []; const enemies = []; const SAFE_ZONE_FROM_PLAYER = 20;

        // --- Orbs: upgraded to StandardMaterial with emissive glow ---
        let orbAttempts = 0;
        while (orbs.length < totalOrbs && orbAttempts < 2000) {
            orbAttempts++;
            const cell = emptyCells[Math.floor(Math.random() * emptyCells.length)];
            const pos = getPos(cell.x, cell.z);
            if (Math.hypot(pos.x - startPos.x, pos.z - startPos.z) < SAFE_ZONE_FROM_PLAYER) continue;
            let tooClose = false;
            for (let existingOrb of orbs) { if (Math.hypot(pos.x - existingOrb.position.x, pos.z - existingOrb.position.z) < 20) { tooClose = true; break; } }
            if (!tooClose) {
                // NEW: MeshStandardMaterial with cyan emissive for proper glow
                const orbMesh = new THREE.Mesh(
                    new THREE.SphereGeometry(0.5, 16, 16),
                    new THREE.MeshStandardMaterial({
                        color: 0x00eeff,
                        emissive: new THREE.Color(0x00eeff),
                        emissiveIntensity: 0.9,
                        roughness: 0.15,
                        metalness: 0.6
                    })
                );
                orbMesh.position.set(pos.x, 1.5, pos.z);
                const orbLight = new THREE.PointLight(0x00eeff, 1.5, 12);
                orbMesh.add(orbLight); scene.add(orbMesh); orbs.push(orbMesh);
            }
        }

        // --- Enemies: red sphere + NEW pulsing aura ---
        const ghostGeo = new THREE.SphereGeometry(1.2, 20, 20);
        const ghostMat = new THREE.MeshBasicMaterial({ color: 0xff0000, transparent: true, opacity: 0.7 });
        // NEW: Shared aura geometry and material
        const auraGeo = new THREE.SphereGeometry(1.9, 12, 12);

        let enemyAttempts = 0;
        while (enemies.length < 8 && enemyAttempts < 2000) {
            enemyAttempts++;
            const eCell = emptyCells[Math.floor(Math.random() * emptyCells.length)];
            const ePos = getPos(eCell.x, eCell.z);
            if (Math.hypot(ePos.x - startPos.x, ePos.z - startPos.z) < 40) continue;
            let tooClose = false;
            for (let existingEnemy of enemies) { if (Math.hypot(ePos.x - existingEnemy.position.x, ePos.z - existingEnemy.position.z) < 30) { tooClose = true; break; } }
            if (!tooClose) {
                const enemy = new THREE.Mesh(ghostGeo, ghostMat.clone());
                enemy.position.set(ePos.x, 2.0, ePos.z);

                // NEW: Per-enemy aura mesh (cloned material for individual opacity animation)
                const auraMat = new THREE.MeshBasicMaterial({ color: 0xff1100, transparent: true, opacity: 0.12, depthWrite: false });
                const aura = new THREE.Mesh(auraGeo, auraMat);
                enemy.add(aura);
                enemy.userData.auraMat = auraMat;

                const pLight = new THREE.PointLight(0xff0000, 2, 20); enemy.add(pLight);
                enemy.userData.targetPos = new THREE.Vector3(ePos.x, 2.0, ePos.z);
                enemy.userData.lastGrid = {x: eCell.x, z: eCell.z};
                scene.add(enemy); enemies.push(enemy);
            }
        }

        // =============================================
        // INPUT & MENU LOGIC
        // =============================================
        const uiContainer = document.getElementById('main-ui');
        const engageBtn = document.getElementById('engage-btn');
        const nameInput = document.getElementById('name-input');
        const bgText = document.getElementById('input-bg-text');

        const quotes = ["The corridors are wide, but the paths are many.", "Do not trust the geometry.", "Cyan light is a guide, but also a trap."];
        document.getElementById('lore-text').innerText = `"${quotes[Math.floor(Math.random() * quotes.length)]}"`;

        function playUISound(freq, vol, dur, type='triangle') {
            if (typeof audioCtx !== 'undefined') {
                if (audioCtx.state === 'suspended') audioCtx.resume();
                const osc = audioCtx.createOscillator(); const gain = audioCtx.createGain();
                osc.type = type; osc.frequency.setValueAtTime(freq, audioCtx.currentTime); osc.frequency.exponentialRampToValueAtTime(freq/2, audioCtx.currentTime + dur);
                gain.gain.setValueAtTime(vol, audioCtx.currentTime); gain.gain.exponentialRampToValueAtTime(0.001, audioCtx.currentTime + dur);
                osc.connect(gain); gain.connect(audioCtx.destination); osc.start(); osc.stop(audioCtx.currentTime + dur);
            }
        }

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
            grid.classList.remove('shake-active');
            void grid.offsetWidth;
            grid.classList.add('shake-active');
            document.body.requestPointerLock();
        });

        document.addEventListener('pointerlockchange', () => {
            if (document.pointerLockElement === document.body) {
                uiContainer.style.display = 'none';
                gameActive = true;
                if (startTime === 0) startTime = Date.now();
                prevTime = performance.now();
                // NEW: Start ambient drone on first game entry
                startAmbientAudio();
            } else if (!gameWon) {
                uiContainer.style.display = 'flex';
                document.getElementById('main-title').innerText = "SYSTEM PAUSED";
                engageBtn.innerText = "RESUME";
                gameActive = false;
                accumulatedTime += (Date.now() - startTime) / 1000;
                document.getElementById('menuOrbCount').innerText = orbsCollected;
            }
        });

        document.addEventListener('mousemove', (e) => {
            if (document.pointerLockElement === document.body) {
                yaw -= e.movementX * SENSITIVITY; pitch -= e.movementY * SENSITIVITY; pitch = Math.max(-Math.PI/2, Math.min(Math.PI/2, pitch)); camera.rotation.set(pitch, yaw, 0);
            }
        });
        document.addEventListener('keydown', (e) => keys[e.code] = true);
        document.addEventListener('keyup', (e) => keys[e.code] = false);

        // =============================================
        // COLLISION CHECK
        // =============================================
        function isWall(x, z, radius) {
            const offset = Math.floor(MAZE_SIZE / 2);
            const minGridX = Math.floor((x - radius + TILE_SIZE / 2) / TILE_SIZE) + offset - 1; const maxGridX = Math.floor((x + radius + TILE_SIZE / 2) / TILE_SIZE) + offset + 1;
            const minGridZ = Math.floor((z - radius + TILE_SIZE / 2) / TILE_SIZE) + offset - 1; const maxGridZ = Math.floor((z + radius + TILE_SIZE / 2) / TILE_SIZE) + offset + 1;
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

        // =============================================
        // UPDATE LOOP
        // =============================================
        // Cache DOM refs for HUD elements updated every frame
        const elOrbCount    = document.getElementById('orbCount');
        const elTimeVal     = document.getElementById('timeVal');
        const elStaminaBar  = document.getElementById('stamina-bar');
        const elStaminaCont = document.getElementById('stamina-container');
        const elCrosshair   = document.getElementById('crosshair');
        const elThreatFill  = document.getElementById('threat-fill');
        const elVignette    = document.getElementById('vignette');

        function update() {
            if (!gameActive) return;

            const now = performance.now(); const delta = (now - prevTime) / 1000; prevTime = now;
            const totalElapsed = (accumulatedTime + (Date.now() - startTime) / 1000).toFixed(1); 

            if (!gameWon) elTimeVal.innerText = totalElapsed;

            // --- Player Movement ---
            if (!gameWon) {
                const input = new THREE.Vector2(0, 0);
                if (keys['KeyW']) input.y -= 1; if (keys['KeyS']) input.y += 1; if (keys['KeyA']) input.x -= 1; if (keys['KeyD']) input.x += 1;
                if (input.length() > 0) input.normalize();

                const isTryingToMove = input.length() > 0;
                const isSprinting = keys['ShiftLeft'] && isTryingToMove && !player.isExhausted;
                currentlySprinting = isSprinting; // expose for vignette

                if (isSprinting) { 
                    player.stamina -= 0.4; 
                    if (player.stamina <= 0) player.isExhausted = true; 
                } else { 
                    player.stamina = Math.min(MAX_STAMINA, player.stamina + 0.9);
                    if (player.stamina >= MAX_STAMINA * 0.25) player.isExhausted = false; 
                }

                const staminaPercent = (player.stamina / MAX_STAMINA) * 100;
                elStaminaBar.style.width = staminaPercent + '%'; 
                elStaminaBar.style.background = player.isExhausted
                    ? '#8b0000'
                    : 'linear-gradient(to bottom, #d4af37, #997a00)';
                // NEW: Toggle exhausted pulse on container
                elStaminaCont.classList.toggle('exhausted', player.isExhausted);

                const targetSpeed = isSprinting ? player.runSpeed : (isTryingToMove ? player.walkSpeed : 0);
                const targetVelocity = input.clone().multiplyScalar(targetSpeed); player.velocity.lerp(targetVelocity, 0.15);
                const moveX = player.velocity.x * Math.cos(yaw) + player.velocity.y * Math.sin(yaw); const moveZ = -player.velocity.x * Math.sin(yaw) + player.velocity.y * Math.cos(yaw);

                let tempX = camera.position.x; let tempZ = camera.position.z;
                if (!isWall(tempX + moveX, tempZ, player.radius)) tempX += moveX; if (!isWall(tempX, tempZ + moveZ, player.radius)) tempZ += moveZ;
                camera.position.x = tempX; camera.position.z = tempZ;

                const currentSpeed = player.velocity.length();
                if (currentSpeed > 0.02) {
                    const targetHz = isSprinting ? 3.5 : 1.5; const bobAmp = isSprinting ? 0.12 : 0.08; 
                    player.headBobTimer += delta * targetHz * Math.PI * 2;
                    camera.position.y = player.height + Math.sin(player.headBobTimer) * bobAmp;

                    // NEW: Footstep trigger — fires once per half-bob cycle (at each "step")
                    const bobCycle = Math.floor(player.headBobTimer / Math.PI);
                    if (bobCycle > player.lastFootstepCycle) {
                        player.lastFootstepCycle = bobCycle;
                        playFootstep(isSprinting);
                    }
                } else {
                    camera.position.y += (player.height - camera.position.y) * 0.1;
                    player.headBobTimer += delta;
                }
            }

            // --- Orb Animation & Collection ---
            let nearbyOrb = false;
            orbs.forEach(orb => {
                if (orb.position.y > 0) {
                    // Gentle float animation + slow rotation
                    orb.position.y = 1.5 + Math.sin(now * 0.002 + orb.position.x) * 0.18;
                    orb.rotation.y += delta * 1.2;

                    const distToOrb = camera.position.distanceTo(orb.position);
                    if (distToOrb < 6) nearbyOrb = true; // NEW: crosshair proximity

                    if (!gameWon && distToOrb < 3) {
                        orb.position.y = -1000; orbsCollected++;
                        elOrbCount.innerText = orbsCollected;
                        playOrbCollect(); // NEW: collection chime
                        if (orbsCollected === totalOrbs && doorState === 'closed') {
                            doorState = 'valves_pressure'; initIndustrialAudio();
                            sirens.forEach(s => s.light.intensity = 50);
                            klaxonGain.gain.setTargetAtTime(0.015, audioCtx.currentTime, 0.1);
                            hissGain.gain.setTargetAtTime(0.1, audioCtx.currentTime, 0.1);
                        }
                    }
                }
            });

            // NEW: Crosshair reacts to nearby orbs
            elCrosshair.classList.toggle('nearby', nearbyOrb);

            // --- Update Particles ---
            for(let i = particles.length - 1; i >= 0; i--) {
                const p = particles[i]; p.position.addScaledVector(p.userData.vel, delta); p.userData.life -= delta;
                if(p.userData.type === 'steam') { p.userData.mat.opacity = (p.userData.life / 1.0) * 0.5; p.scale.setScalar(2.0 - p.userData.life); } 
                else if (p.userData.type === 'spark') { p.userData.vel.y -= delta * 15; if(p.position.y < 0.1) { p.position.y = 0.1; p.userData.vel.y *= -0.5; } }
                if(p.userData.life <= 0) { scene.remove(p); if(p.userData.type === 'steam') p.userData.mat.dispose(); particles.splice(i, 1); }
            }

            // --- Radar ---
            rCtx.clearRect(0, 0, radarCanvas.width, radarCanvas.height);
            rCtx.strokeStyle = 'rgba(212, 196, 168, 0.2)'; rCtx.lineWidth = 1;
            rCtx.beginPath(); rCtx.moveTo(rCenter, 0); rCtx.lineTo(rCenter, radarCanvas.height); rCtx.moveTo(0, rCenter); rCtx.lineTo(radarCanvas.width, rCenter); rCtx.stroke();
            rCtx.fillStyle = '#d4c4a8'; rCtx.beginPath(); rCtx.moveTo(rCenter, rCenter - 8); rCtx.lineTo(rCenter - 5, rCenter + 5); rCtx.lineTo(rCenter + 5, rCenter + 5); rCtx.fill();

            function drawBlip(worldX, worldZ, color, size, isRect) {
                const dx = worldX - camera.position.x; const dz = worldZ - camera.position.z;
                const localRight = dx * Math.cos(yaw) - dz * Math.sin(yaw); const localForward = -dx * Math.sin(yaw) - dz * Math.cos(yaw);
                const dist = Math.sqrt(localRight * localRight + localForward * localForward);
                let drawRight = localRight; let drawForward = localForward;
                if (dist > radarMaxDist) { drawRight = (localRight / dist) * radarMaxDist; drawForward = (localForward / dist) * radarMaxDist; }
                const rx = rCenter + drawRight * radarScale; const ry = rCenter - drawForward * radarScale;
                rCtx.fillStyle = color; if (isRect) rCtx.fillRect(rx - size, ry - size, size * 2, size * 2); else { rCtx.beginPath(); rCtx.arc(rx, ry, size, 0, Math.PI * 2); rCtx.fill(); }
            }

            const dxDoor = doorGroup.position.x - camera.position.x; const dzDoor = doorGroup.position.z - camera.position.z;
            const lRight = dxDoor * Math.cos(yaw) - dzDoor * Math.sin(yaw); const lForward = -dxDoor * Math.sin(yaw) - dzDoor * Math.cos(yaw);
            let distToMapDoor = Math.sqrt(lRight * lRight + lForward * lForward); let rx = rCenter + lRight * radarScale; let ry = rCenter - lForward * radarScale;
            if (distToMapDoor > radarMaxDist) { rx = rCenter + (lRight / distToMapDoor) * radarMaxDist * radarScale; ry = rCenter - (lForward / distToMapDoor) * radarMaxDist * radarScale; }
            rCtx.fillStyle = '#55aa55'; rCtx.fillRect(rx - 5, ry - 7, 10, 14); rCtx.fillStyle = '#112211'; rCtx.fillRect(rx - 3, ry - 5, 6, 12); rCtx.fillStyle = '#d4af37'; rCtx.beginPath(); rCtx.arc(rx + 1, ry + 1, 1.5, 0, Math.PI * 2); rCtx.fill();

            orbs.forEach(orb => { if (orb.position.y > 0) drawBlip(orb.position.x, orb.position.z, '#d4af37', 2.5, false); });

            // --- Enemies ---
            let closestDist = 100;
            enemies.forEach((enemy, index) => {
                drawBlip(enemy.position.x, enemy.position.z, '#ff5555', 3, false);

                if (!gameWon && enemy.position.distanceTo(enemy.userData.targetPos) < 0.5) {
                    const cx = Math.round(enemy.userData.targetPos.x / TILE_SIZE) + Math.floor(MAZE_SIZE / 2); const cz = Math.round(enemy.userData.targetPos.z / TILE_SIZE) + Math.floor(MAZE_SIZE / 2);
                    const neighbors = []; const dirs = [[0,-1], [0,1], [-1,0], [1,0]];
                    dirs.forEach(([dx, dz]) => { const nx = cx + dx; const nz = cz + dz; if (nx >= 0 && nx < MAZE_SIZE && nz >= 0 && nz < MAZE_SIZE && maze[nx][nz] === 0) { if (!(nx === enemy.userData.lastGrid.x && nz === enemy.userData.lastGrid.z)) neighbors.push({x: nx, z: nz}); } });
                    if (neighbors.length === 0 && maze[enemy.userData.lastGrid.x][enemy.userData.lastGrid.z] === 0) neighbors.push(enemy.userData.lastGrid);
                    enemy.userData.lastGrid = {x: cx, z: cz}; let nextCell = neighbors.length > 0 ? neighbors[Math.floor(Math.random() * neighbors.length)] : enemy.userData.lastGrid;
                    enemy.userData.targetPos.set(getPos(nextCell.x, nextCell.z).x, 2.0, getPos(nextCell.x, nextCell.z).z);
                }

                const dir = new THREE.Vector3().subVectors(enemy.userData.targetPos, enemy.position).normalize(); 
                enemy.position.addScaledVector(dir, 0.12); 
                enemy.position.y = 2.0 + Math.sin(now * 0.003 + index) * 0.4;

                // NEW: Pulse enemy aura (opacity + scale)
                if (enemy.userData.auraMat) {
                    enemy.userData.auraMat.opacity = 0.08 + Math.sin(now * 0.0025 + index * 1.7) * 0.07;
                    const aura = enemy.children.find(c => c.geometry === auraGeo);
                    if (aura) aura.scale.setScalar(1 + Math.sin(now * 0.002 + index) * 0.12);
                }

                const dist = camera.position.distanceTo(enemy.position); 
                if (dist < closestDist) closestDist = dist;

                if (!gameWon && dist < 3.0 && gameActive) { 
                    gameActive = false; 
                    document.exitPointerLock(); 
                    const totalElapsedDeath = (accumulatedTime + (Date.now() - startTime) / 1000).toFixed(1);
                    document.getElementById('time-stat').innerText = totalElapsedDeath + 's';
                    document.getElementById('orb-stat').innerText = `${orbsCollected} / 12`;
                    document.getElementById('death-screen-ui').style.display = 'block';
                }
            });

            // --- NEW: Threat bar — fills based on closest enemy distance ---
            if (elThreatFill) {
                const threatLevel = closestDist < 30 ? Math.max(0, (30 - closestDist) / 30) : 0;
                elThreatFill.style.width = (threatLevel * 100) + '%';
                const isClose = closestDist < 12;
                const isMedium = closestDist < 22;
                elThreatFill.style.background = isClose
                    ? 'linear-gradient(to right, #cc0000, #ff0000)'
                    : isMedium
                    ? 'linear-gradient(to right, #cc4400, #ff6600)'
                    : 'linear-gradient(to right, #886600, #ffaa00)';
                elThreatFill.style.boxShadow = threatLevel > 0.3
                    ? `0 0 ${Math.round(threatLevel * 14)}px rgba(255,${isClose ? 0 : 100},0,0.8)`
                    : 'none';
            }

            // --- NEW: Vignette — combines sprint darkness + enemy proximity ---
            if (elVignette) {
                const sprintIntensity  = currentlySprinting ? 0.38 : 0;
                const enemyIntensity   = closestDist < 18 ? ((18 - closestDist) / 18) * 0.52 : 0;
                const totalIntensity   = Math.min(0.92, sprintIntensity + enemyIntensity);
                elVignette.style.opacity = totalIntensity;
            }

            // --- NEW: Proximity breathing audio ---
            if (proximityBreathGain) {
                const intensity = closestDist < 20 ? Math.max(0, (20 - closestDist) / 20) : 0;
                proximityBreathGain.gain.setTargetAtTime(intensity * 0.07, audioCtx.currentTime, 0.4);
                // Also slightly boost ambient drone when threatened
                if (ambientGainNode) {
                    ambientGainNode.gain.setTargetAtTime(0.045 + intensity * 0.03, audioCtx.currentTime, 0.6);
                }
            }

            // --- Single-sting proximity warning (unchanged) ---
            if (!gameWon && closestDist < 12) {
                camera.position.x += (Math.random() - 0.5) * ((12 - closestDist) * 0.02);
                if (!hasPlayedSting) { playSting(); hasPlayedSting = true; }
            } else { hasPlayedSting = false; }

            // --- Camera roll (win safety) ---
            if (!gameWon) camera.rotation.z = 0;

            // --- Door sequence animation (unchanged) ---
            if (doorState !== 'closed' && doorState !== 'open') {
                const distToDoor = camera.position.distanceTo(doorGroup.position); const volScale = Math.max(0, 1 - (distToDoor / 50)); 
                sirens.forEach((s, idx) => { s.group.rotation.y += delta * (idx % 2 === 0 ? 2 : -2); });
                if (klaxonGain) klaxonGain.gain.setTargetAtTime(volScale * 0.015, audioCtx.currentTime, 0.1);
                if (!gameWon && distToDoor < 45) { const shakeIntensity = (45 - distToDoor) * 0.0015; camera.rotation.z = (Math.random() - 0.5) * shakeIntensity; }

                if (doorState === 'valves_pressure') {
                    if (valves[0].rotation.z < Math.PI * 4) { 
                        valves.forEach(v => v.rotation.z += delta * Math.PI);
                        if(Math.random() > 0.5) emitSteam(doorGroup.position.x, 1, doorGroup.position.z);
                        if(hissGain) hissGain.gain.setTargetAtTime(volScale * 0.1, audioCtx.currentTime, 0.1);
                    } else {
                        doorState = 'vault_unlock';
                        if(hissGain) hissGain.gain.setTargetAtTime(0, audioCtx.currentTime, 0.1);
                        if(vaultGain) vaultGain.gain.setTargetAtTime(volScale * 0.04, audioCtx.currentTime, 0.1);
                    }
                }
                else if (doorState === 'vault_unlock') {
                    if (vaultWheelGroup.rotation.z < Math.PI) {
                        vaultWheelGroup.rotation.z += delta * (Math.PI / 5); vaultWheelGroup.position.x -= delta * 0.2; 
                        if(vaultGain) vaultGain.gain.setTargetAtTime(volScale * 0.04, audioCtx.currentTime, 0.1);
                    } else {
                        doorState = 'unlatching';
                        matIndicator.color.setHex(0x00ff00);
                        if(vaultGain) vaultGain.gain.setTargetAtTime(0, audioCtx.currentTime, 0.1);
                        if(latchGain) latchGain.gain.setTargetAtTime(volScale * 0.06, audioCtx.currentTime, 0.1);
                    }
                }
                else if (doorState === 'unlatching') {
                    if (latchL.position.x > -6) {
                        const latchSpeed = delta * 0.5; latchL.position.x -= latchSpeed; latchR.position.x += latchSpeed;
                        deadboltsLeft.forEach(b => b.position.x -= latchSpeed * 3); deadboltsRight.forEach(b => b.position.x += latchSpeed * 3);
                        if (latchGain) latchGain.gain.setTargetAtTime(volScale * 0.06, audioCtx.currentTime, 0.1);
                    } else {
                        doorState = 'retracting_pistons';
                        if(latchGain) latchGain.gain.setTargetAtTime(0, audioCtx.currentTime, 0.1);
                        if(pistonGain) pistonGain.gain.setTargetAtTime(volScale * 0.15, audioCtx.currentTime, 0.1);
                    }
                } 
                else if (doorState === 'retracting_pistons') {
                    if (pistonGroup.position.y < 5) {
                        pistonGroup.position.y += delta * 1.0; 
                        if (pistonGain) pistonGain.gain.setTargetAtTime(volScale * 0.15, audioCtx.currentTime, 0.1);
                    } else {
                        doorState = 'sliding';
                        if(pistonGain) pistonGain.gain.setTargetAtTime(0, audioCtx.currentTime, 0.1);
                        if(gearGain) gearGain.gain.setTargetAtTime(volScale * 0.08, audioCtx.currentTime, 0.1);
                    }
                } 
                else if (doorState === 'sliding') {
                    if (doorHalfLeftGroup.position.x > -panelWidth - 2) {
                        const slideAmount = delta * 0.444; 
                        doorHalfLeftGroup.position.x -= slideAmount; doorHalfRightGroup.position.x += slideAmount;
                        const gearRotation = slideAmount / gearRadius; mainGearLeft.rotation.z -= gearRotation; mainGearRight.rotation.z += gearRotation;
                        const helperRatio = gearRadius / helperGearRadius; helperGearLeft.rotation.z += gearRotation * helperRatio; helperGearRight.rotation.z -= gearRotation * helperRatio;
                        if(Math.random() > 0.4) emitSpark(doorGroup.position.x - 3, 11 + gearRadius, doorGroup.position.z - 0.8);
                        if(Math.random() > 0.4) emitSpark(doorGroup.position.x + 3, 11 + gearRadius, doorGroup.position.z - 0.8);
                        if(gearGain) gearGain.gain.setTargetAtTime(volScale * 0.08, audioCtx.currentTime, 0.1);
                    } else {
                        doorState = 'open';
                        sirens.forEach(s => s.light.intensity = 0); matGlassRed.emissive.setHex(0x110000);
                        const fadeOutTime = audioCtx.currentTime + 1.5;
                        if(klaxonGain) klaxonGain.gain.linearRampToValueAtTime(0, fadeOutTime); if(gearGain) gearGain.gain.linearRampToValueAtTime(0, fadeOutTime);
                    }
                }
            }

            // --- Win Condition ---
            if (doorState === 'open' && camera.position.z > doorGroup.position.z + 1.5 && !gameWon) { 
                gameWon = true; 
                document.exitPointerLock(); 
                const winScreen = document.getElementById('win-screen');
                const fadeBlack = document.getElementById('fade-black');
                winScreen.style.display = 'flex';
                setTimeout(() => { fadeBlack.style.opacity = '1'; winScreen.style.opacity = '1'; }, 50);
                document.getElementById('finalTime').innerText = `FINAL TIME: ${totalElapsed}s`;
                if(klaxonOsc) klaxonOsc.stop(); if(latchOsc) latchOsc.stop(); if(pistonOsc) pistonOsc.stop(); if(gearOsc) gearOsc.stop(); if(vaultOsc) vaultOsc.stop(); if(hissSrc) hissSrc.stop();
            }
        }

        function animate() { requestAnimationFrame(animate); update(); renderer.render(scene, camera); } animate();

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
