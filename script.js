
        import * as THREE from 'three';

     // ================================================================
        //  MAZE GENERATION
        // ================================================================
        const MAZE_SIZE=25, TILE_SIZE=12;
        
        // --- ADD THESE TWO LINES HERE ---
        let corridorLights = [];
        let cullableMeshes = [];
        // --------------------------------
        
        const maze=Array(MAZE_SIZE).fill(null).map(()=>Array(MAZE_SIZE).fill(1));
        const emptyCells=[];
        function carveMaze(x,y){
            maze[x][y]=0;
            const dirs=[[0,-1],[0,1],[-1,0],[1,0]].sort(()=>Math.random()-0.5);
            for(const[dx,dy]of dirs){const nx=x+dx*2,ny=y+dy*2;if(nx>0&&nx<MAZE_SIZE-1&&ny>0&&ny<MAZE_SIZE-1&&maze[nx][ny]===1){maze[x+dx][y+dy]=0;carveMaze(nx,ny);}}
        }
        carveMaze(1,1);
        for(let i=1;i<MAZE_SIZE-1;i++)for(let j=1;j<MAZE_SIZE-1;j++)
            if(maze[i][j]===1&&((maze[i-1][j]===0&&maze[i+1][j]===0)||(maze[i][j-1]===0&&maze[i][j+1]===0))&&Math.random()<0.25)maze[i][j]=0;
        const exitGridX=Math.floor(MAZE_SIZE/2),exitGridZ=MAZE_SIZE-1;
        for(let i=-1;i<=1;i++)for(let j=-3;j<=-1;j++)maze[exitGridX+i][exitGridZ+j]=0;
        maze[exitGridX][exitGridZ]=0;
        for(let i=0;i<MAZE_SIZE;i++)for(let j=0;j<MAZE_SIZE;j++)if(maze[i][j]===0)emptyCells.push({x:i,z:j});

        function getPos(i,j){return{x:(i-Math.floor(MAZE_SIZE/2))*TILE_SIZE,z:(j-Math.floor(MAZE_SIZE/2))*TILE_SIZE};}

        // ================================================================
        //  PATHFINDING — parent-map BFS, O(n) memory
        // ================================================================
        function worldToGrid(wx,wz){const o=Math.floor(MAZE_SIZE/2);return{x:Math.max(0,Math.min(MAZE_SIZE-1,Math.round(wx/TILE_SIZE)+o)),z:Math.max(0,Math.min(MAZE_SIZE-1,Math.round(wz/TILE_SIZE)+o))};}
      function bfsPath(sx, sz, gx, gz) {
            if(sx === gx && sz === gz) return [];
            
            // OPTIMIZATION: Flat typed arrays are blisteringly fast and O(1) complexity.
            // This prevents the JS engine from choking or creating circular reference loops.
            const visited = new Uint8Array(MAZE_SIZE * MAZE_SIZE);
            const parent = new Int16Array(MAZE_SIZE * MAZE_SIZE);
            parent.fill(-1);
            
            const startIdx = sx + sz * MAZE_SIZE;
            const targetIdx = gx + gz * MAZE_SIZE;
            
            const q = [startIdx];
            visited[startIdx] = 1;
            
            let head = 0;
            let it = 0;
            
            // Loop limit protects against unexpected grid lockups
            while(head < q.length && it++ < 3000) {
                const curr = q[head++]; 
                const cx = curr % MAZE_SIZE;
                const cz = Math.floor(curr / MAZE_SIZE);
                
                // If we reached the target, trace back safely
                if(curr === targetIdx) {
                    const path = [];
                    let p = curr;
                    let failsafe = 0; // Absolute protection against infinite while-loops
                    
                    while(p !== -1 && parent[p] !== -1 && failsafe++ < 1000) {
                        path.unshift({x: p % MAZE_SIZE, z: Math.floor(p / MAZE_SIZE)});
                        p = parent[p];
                    }
                    // Remove the very first node so they don't stutter in place
                    if(path.length) path.shift();
                    return path;
                }
                
                // Strictly 4-directional movement to prevent clipping corners and walls
                const neighbors = [];
                if (cz > 0) neighbors.push(curr - MAZE_SIZE); // Up
                if (cz < MAZE_SIZE - 1) neighbors.push(curr + MAZE_SIZE); // Down
                if (cx > 0) neighbors.push(curr - 1); // Left
                if (cx < MAZE_SIZE - 1) neighbors.push(curr + 1); // Right
                
                for(let i = 0; i < neighbors.length; i++) {
                    const n = neighbors[i];
                    const nx = n % MAZE_SIZE;
                    const nz = Math.floor(n / MAZE_SIZE);
                    
                    // Only traverse if it is an empty corridor (0) and hasn't been visited
                    if(maze[nx][nz] === 0 && visited[n] === 0) {
                        visited[n] = 1;
                        parent[n] = curr;
                        q.push(n);
                    }
                }
            }
            return [];
        }

        // Failsafe alias: If the AI code is still calling aStarPath anywhere, 
        // it will harmlessly route it through the fixed, crash-proof BFS.
        function aStarPath(sx, sz, gx, gz) { 
            return bfsPath(sx, sz, gx, gz); 
        }
        function hasLOS(ax,az,bx,bz){
            const g0=worldToGrid(ax,az),g1=worldToGrid(bx,bz),steps=Math.max(Math.abs(g1.x-g0.x),Math.abs(g1.z-g0.z));
            if(!steps)return true;
            for(let i=1;i<steps;i++){const t=i/steps,cx=Math.round(g0.x+(g1.x-g0.x)*t),cz=Math.round(g0.z+(g1.z-g0.z)*t);if(cx>=0&&cx<MAZE_SIZE&&cz>=0&&cz<MAZE_SIZE&&maze[cx][cz]===1)return false;}
            return true;
        }

        // ================================================================
        //  CONSTANTS & STATE
        // ================================================================
    const TOTAL_ORBS=12, MAX_STAMINA=120; // Lower stamina
        // AI tuning
        const ALERT_DUR=11.0, HUNT_DUR=8.0, SEARCH_DUR=14.0;
        const LIGHT_RANGE=36, CONE_COS=Math.cos(58*Math.PI/180);
        const SPRINT_ALERT_R=22, PATROL_SPD=0.15, ALERT_SPD=0.32, HUNT_SPD=0.40, SEARCH_SPD=0.12; // Much faster enemies
        const ENEMY_NAMES=['REVENANT','UNIT-07','SPECTER-X','THE HOLLOW','SHADE-03','ECHO-NULL','WRAITH','ABSENCE'];

        let orbsCollected=0, gameActive=false, gameWon=false;
        let startTime=0, accumulatedTime=0, hasPlayedSting=false, prevTime=performance.now();
  let yaw=Math.PI, pitch=0; const SENSITIVITY=0.002;
        let introShown=false, sprintAlertCD=0, lastFootCycle=0;
        let terminalActivated=false, terminalBtnT=0, currentlySprinting=false;
// ================================================================
        //  PUZZLE STATE
        // ================================================================
        // How many wall puzzles the player must solve (3 panels)
        const TOTAL_PUZZLES = 6;
        let puzzlesSolved = 0;      // increments on each panel solve
        let activePuzzle = null;    // {type, panelObj, solved}
        let puzzleOpen = false;

        // -- Power Routing (Puzzle A) state --
       const PR_SIZE = 5;    // 5x5 power routing grid
        const FUSE_SIZE = 5;  // 5x5 fuse sliding grid
        let soLastDelta = 0.016; // used by sequence puzzle draw
        let prGrid = [];


        // -- Fuse Box (Puzzle B) state --
        let fuseGrid = [];      // 4x4 array of values (0=empty, 1=normal, 2=master)
        let fuseEmpty = {r:0,c:0}; // position of empty slot

        // -- Frequency Tuner (Puzzle C) state --
        let ftFreqDial = 0;   // 0–11 steps (0–165 degrees)
        let ftAmpDial  = 0;   // 0–11 steps
        let ftTarget   = {freq:5, amp:4}; // randomised per panel
        let ftLockTimer = 0;  // counts up when matched

        // -- Sequence Override (Puzzle D) state --
        let soSequence  = [];    // master sequence (up to 4)
        let soPlayerSeq = [];    // what player has input so far
        let soRound     = 0;     // 0-indexed, how many buttons in current sub-sequence
        let soFlashing  = [];    // [{btnIdx, timer}] — buttons flashing their display
        let soState     = 'watching'; // 'watching' | 'input' | 'failed'
        let soFlashTimer = 0;    // countdown between flashes during show phase

        // Dial drag state for Frequency Tuner
        let dialDragActive = false, dialDragId = -1, dialDragStartX = 0, dialDragStartVal = 0;

        // 3D panel objects for each wall puzzle (filled after placement)
        const wallPanels = []; // [{worldX, worldZ, type, solved, screenMat, emissiveLine, light}]
        const exploredCells=new Set();
        
        // --- BULLETPROOF KEYBOARD TRACKER ---
        const keys={};
        window.addEventListener('keydown', (e) => { keys[e.code] = true; });
        window.addEventListener('keyup', (e) => { keys[e.code] = false; });
        const player={height:2.1,radius:0.8,walkSpeed:0.22,runSpeed:0.46,stamina:MAX_STAMINA,isExhausted:false,velocity:new THREE.Vector2(0,0),headBobTimer:0};

        document.getElementById('totalOrbsUI').innerText=TOTAL_ORBS;

        // DOM refs
        const elOrbCount=document.getElementById('orbCount');
        const elTimeVal=document.getElementById('timeVal');
        const elStBar=document.getElementById('stamina-bar');
        const elStCont=document.getElementById('stamina-container');
        const elCross=document.getElementById('crosshair');
        const elPrompt=document.getElementById('interact-prompt');
        const radarCanvas=document.getElementById('radar');
        const rCtx=radarCanvas.getContext('2d');
        const RC=radarCanvas.width/2, R_MAX=105, R_SCL=(RC-12)/R_MAX;
// Puzzle overlay DOM refs
        const elPuzzleOverlay = document.getElementById('puzzle-overlay');
        const elPuzzleCanvas  = document.getElementById('puzzle-canvas');
        const elPuzzleTitle   = document.getElementById('puzzle-title');
        const elPuzzleStatus  = document.getElementById('puzzle-status');
        const pCtx = elPuzzleCanvas.getContext('2d');
const elPromptText = document.getElementById('prompt-text');

        // ================================================================
        //  SCENE — PSX style: low pixel ratio, nearest filter, no AA
        // ================================================================
        const scene=new THREE.Scene();
        scene.background=new THREE.Color(0x040508);
        scene.fog=new THREE.FogExp2(0x040508,0.022);

        const camera=new THREE.PerspectiveCamera(75,innerWidth/innerHeight,0.1,100);
        camera.rotation.order='YXZ';

       const renderer = new THREE.WebGLRenderer({ antialias: false });
renderer.setPixelRatio(Math.min(devicePixelRatio, 1) * 0.3);
renderer.setSize(innerWidth, innerHeight);

// Enable Shadows
renderer.shadowMap.enabled = true;
// CHANGE THIS LINE for the smooth look:
renderer.shadowMap.type = THREE.PCFShadowMap;
document.body.appendChild(renderer.domElement);
// Bodycam flashlight — Bigger, detailed, and toggleable
        let flashlightOn = true;
        const flash1=new THREE.SpotLight(0xfffdd8,150,80,Math.PI/4,0.1,1.8); 
        flash1.castShadow=true; flash1.shadow.mapSize.setScalar(256); flash1.shadow.bias=-0.001;
        
        const flash2=new THREE.SpotLight(0xffe8c0,30,45,Math.PI/2.5,0.8,2.2); 
        flash2.castShadow=false;

        flash1.position.set(0, 0, 0);
        flash2.position.set(0, 0, 0);

        camera.add(flash1); camera.add(flash1.target); flash1.target.position.set(0,0,-1);
        camera.add(flash2); camera.add(flash2.target); flash2.target.position.set(0,0,-1);

     
        
        // Add the camera (and its attached lights) to the scene
        scene.add(camera);

        const hemi=new THREE.HemisphereLight(0x14181c,0x08090a,0.35); scene.add(hemi);

// ================================================================
        //  AMBIENT DUST PARTICLES (ZERO PERFORMANCE HIT)
        // ================================================================
        const dustCount = 800; 
        const dustGeo = new THREE.BufferGeometry();
        const dustPos = new Float32Array(dustCount * 3);
        const dustVel = [];

        for (let i = 0; i < dustCount; i++) {
            // Scatter randomly across the 300x300 maze
            dustPos[i * 3] = (Math.random() - 0.5) * 300; 
            // Scatter from the floor (0) to the ceiling (14)
            dustPos[i * 3 + 1] = Math.random() * 14;      
            dustPos[i * 3 + 2] = (Math.random() - 0.5) * 300;

            // Give each particle a random drift speed
            dustVel.push({
                x: (Math.random() - 0.5) * 0.015,
                y: (Math.random() - 0.5) * 0.01 - 0.005, // Slight gravity pull down
                z: (Math.random() - 0.5) * 0.015
            });
        }

        dustGeo.setAttribute('position', new THREE.BufferAttribute(dustPos, 3));

        const dustMat = new THREE.PointsMaterial({
            color: 0x99aaaf,     // Dirty, pale grey/blue
            size: 0.25,          // Size of the pixel dust
            transparent: true,
            opacity: 0.4,
            depthWrite: false    // CRITICAL: Prevents dust from creating weird black outlines
        });

        const dustParticles = new THREE.Points(dustGeo, dustMat);
        scene.add(dustParticles);

        // ================================================================
        //  AUDIO
        // ================================================================
        const audioCtx=new(window.AudioContext||window.webkitAudioContext)();
        let klaxonOsc,klaxonGain,vaultOsc,vaultGain,latchOsc,latchGain,pistonOsc,pistonGain,gearOsc,gearGain,hissSrc,hissGain;

        function resume(){if(audioCtx.state==='suspended')audioCtx.resume();}

        function initIndustrialAudio(){
            resume();
            klaxonOsc=audioCtx.createOscillator();klaxonOsc.type='triangle';klaxonOsc.frequency.value=450;
            const kL=audioCtx.createOscillator();kL.frequency.value=2;const kM=audioCtx.createGain();kM.gain.value=150;kL.connect(kM);kM.connect(klaxonOsc.frequency);kL.start();
            klaxonGain=audioCtx.createGain();klaxonGain.gain.value=0;klaxonOsc.connect(klaxonGain);klaxonGain.connect(audioCtx.destination);klaxonOsc.start();
            vaultOsc=audioCtx.createOscillator();vaultOsc.type='sawtooth';vaultOsc.frequency.value=160;
            vaultGain=audioCtx.createGain();vaultGain.gain.value=0;vaultOsc.connect(vaultGain);vaultGain.connect(audioCtx.destination);vaultOsc.start();
            latchOsc=audioCtx.createOscillator();latchOsc.type='sawtooth';latchOsc.frequency.value=80;
            latchGain=audioCtx.createGain();latchGain.gain.value=0;latchOsc.connect(latchGain);latchGain.connect(audioCtx.destination);latchOsc.start();
            pistonOsc=audioCtx.createOscillator();pistonOsc.type='square';pistonOsc.frequency.value=28;
            pistonGain=audioCtx.createGain();pistonGain.gain.value=0;
            const pf=audioCtx.createBiquadFilter();pf.type='lowpass';pf.frequency.value=120;
            pistonOsc.connect(pf);pf.connect(pistonGain);pistonGain.connect(audioCtx.destination);pistonOsc.start();
            gearOsc=audioCtx.createOscillator();gearOsc.type='square';gearOsc.frequency.value=15;
            gearGain=audioCtx.createGain();gearGain.gain.value=0;gearOsc.connect(gearGain);gearGain.connect(audioCtx.destination);gearOsc.start();
            const bsz=audioCtx.sampleRate*2,nb=audioCtx.createBuffer(1,bsz,audioCtx.sampleRate);
            const nd=nb.getChannelData(0);for(let i=0;i<bsz;i++)nd[i]=Math.random()*2-1;
            hissSrc=audioCtx.createBufferSource();hissSrc.buffer=nb;hissSrc.loop=true;
            const hf=audioCtx.createBiquadFilter();hf.type='highpass';hf.frequency.value=800;
            hissGain=audioCtx.createGain();hissGain.gain.value=0;
            hissSrc.connect(hf);hf.connect(hissGain);hissGain.connect(audioCtx.destination);hissSrc.start();
        }

        function playSting(){
            resume();const o=audioCtx.createOscillator(),g=audioCtx.createGain();o.type='sawtooth';
            o.frequency.setValueAtTime(110,audioCtx.currentTime);o.frequency.exponentialRampToValueAtTime(25,audioCtx.currentTime+1.2);
            g.gain.setValueAtTime(0.18,audioCtx.currentTime);g.gain.exponentialRampToValueAtTime(0.001,audioCtx.currentTime+1.2);
            o.connect(g);g.connect(audioCtx.destination);o.start();o.stop(audioCtx.currentTime+1.2);
        }

        // Realistic footstep: soft multi-band noise burst with a short reverb tail
        let _footBuf=null;
        function buildFootBuf(sprint){
            const dur=sprint?0.06:0.09;
            const sz=Math.floor(audioCtx.sampleRate*dur);
            const b=audioCtx.createBuffer(1,sz,audioCtx.sampleRate);
            const d=b.getChannelData(0);
            for(let i=0;i<sz;i++)d[i]=(Math.random()*2-1)*Math.pow(1-i/sz,sprint?3:4.5);
            return b;
        }
        function playFootstep(sprint){
            resume();
            const buf=buildFootBuf(sprint);
        // Low thud component (LOUDER)
            const s1=audioCtx.createBufferSource();s1.buffer=buf;
            const lp=audioCtx.createBiquadFilter();lp.type='lowpass';lp.frequency.value=sprint?100:70;
            const g1=audioCtx.createGain();g1.gain.value=sprint?0.35:0.20;
            s1.connect(lp);lp.connect(g1);g1.connect(audioCtx.destination);s1.start();
            // Mid body (LOUDER)
            const s2=audioCtx.createBufferSource();s2.buffer=buf;
            const bp=audioCtx.createBiquadFilter();bp.type='bandpass';bp.frequency.value=sprint?240:160;bp.Q.value=1.8;
            const g2=audioCtx.createGain();g2.gain.value=sprint?0.15:0.08;
            s2.connect(bp);bp.connect(g2);g2.connect(audioCtx.destination);s2.start();
            // Short reverb tail
            const s3=audioCtx.createBufferSource();s3.buffer=buf;
            const lp2=audioCtx.createBiquadFilter();lp2.type='lowpass';lp2.frequency.value=50;
            const g3=audioCtx.createGain();g3.gain.value=sprint?0.04:0.025;
            s3.connect(lp2);lp2.connect(g3);g3.connect(audioCtx.destination);
            s3.start(audioCtx.currentTime+0.07);
        }

        // Orb collect chime — warm ascending tones
        function playOrbChime(){
            resume();
            [330,528,792,1056].forEach((f,i)=>{
                const o=audioCtx.createOscillator(),g=audioCtx.createGain();o.type='sine';o.frequency.value=f;
                const t=audioCtx.currentTime+i*0.085;
                g.gain.setValueAtTime(0,t);g.gain.linearRampToValueAtTime(0.2,t+0.015);g.gain.exponentialRampToValueAtTime(0.001,t+0.28);
                o.connect(g);g.connect(audioCtx.destination);o.start(t);o.stop(t+0.3);
            });
        }

        function playScreech(){
            resume();const o=audioCtx.createOscillator(),g=audioCtx.createGain();o.type='sawtooth';
            o.frequency.setValueAtTime(240,audioCtx.currentTime);o.frequency.exponentialRampToValueAtTime(45,audioCtx.currentTime+0.5);
            g.gain.setValueAtTime(0.12,audioCtx.currentTime);g.gain.exponentialRampToValueAtTime(0.001,audioCtx.currentTime+0.5);
            o.connect(g);g.connect(audioCtx.destination);o.start();o.stop(audioCtx.currentTime+0.5);
        }
function playFlashlightClick() {
            if (!audioCtx) return;
            const t = audioCtx.currentTime;

            // Metallic 'snap'
            const snapOsc = audioCtx.createOscillator();
            const snapGain = audioCtx.createGain();
            snapOsc.type = 'square';
            snapOsc.frequency.setValueAtTime(1200, t);
            snapOsc.frequency.exponentialRampToValueAtTime(100, t + 0.03);
            snapGain.gain.setValueAtTime(0.3, t);
            snapGain.gain.exponentialRampToValueAtTime(0.01, t + 0.03);
            snapOsc.connect(snapGain);
            snapGain.connect(audioCtx.destination);
            snapOsc.start(t);
            snapOsc.stop(t + 0.04);

            // Hollow 'clack'
            const clackOsc = audioCtx.createOscillator();
            const clackGain = audioCtx.createGain();
            clackOsc.type = 'triangle';
            clackOsc.frequency.setValueAtTime(400, t);
            clackOsc.frequency.exponentialRampToValueAtTime(50, t + 0.06);
            clackGain.gain.setValueAtTime(0.5, t);
            clackGain.gain.exponentialRampToValueAtTime(0.01, t + 0.06);
            clackOsc.connect(clackGain);
            clackGain.connect(audioCtx.destination);
            clackOsc.start(t);
            clackOsc.stop(t + 0.07);
        }

        function playTerminalClick(){
            resume();
            [200,140,90,60].forEach((f,i)=>{
                const o=audioCtx.createOscillator(),g=audioCtx.createGain();o.type='square';o.frequency.value=f;
                const t=audioCtx.currentTime+i*0.07;
                g.gain.setValueAtTime(0.16,t);g.gain.exponentialRampToValueAtTime(0.001,t+0.12);
                o.connect(g);g.connect(audioCtx.destination);o.start(t);o.stop(t+0.13);
            });
        }

        function playUISound(freq,vol,dur,type='triangle'){
            resume();const o=audioCtx.createOscillator(),g=audioCtx.createGain();o.type=type;
            o.frequency.setValueAtTime(freq,audioCtx.currentTime);o.frequency.exponentialRampToValueAtTime(freq/2,audioCtx.currentTime+dur);
            g.gain.setValueAtTime(vol,audioCtx.currentTime);g.gain.exponentialRampToValueAtTime(0.001,audioCtx.currentTime+dur);
            o.connect(g);g.connect(audioCtx.destination);o.start();o.stop(audioCtx.currentTime+dur);
        }
function playPuzzleTick() {
            resume();
            const o=audioCtx.createOscillator(),g=audioCtx.createGain();
            o.type='square'; o.frequency.value=1200;
            g.gain.setValueAtTime(0.06,audioCtx.currentTime);
            g.gain.exponentialRampToValueAtTime(0.001,audioCtx.currentTime+0.04);
            o.connect(g); g.connect(audioCtx.destination); o.start(); o.stop(audioCtx.currentTime+0.04);
        }
        function playPuzzleSuccess() {
            resume();
            [440,550,660,880].forEach((f,i)=>{
                const o=audioCtx.createOscillator(),g=audioCtx.createGain();
                o.type='sine'; o.frequency.value=f;
                const t=audioCtx.currentTime+i*0.1;
                g.gain.setValueAtTime(0,t); g.gain.linearRampToValueAtTime(0.18,t+0.02);
                g.gain.exponentialRampToValueAtTime(0.001,t+0.35);
                o.connect(g); g.connect(audioCtx.destination); o.start(t); o.stop(t+0.36);
            });
        }
        function playPuzzleFail() {
            resume();
            const o=audioCtx.createOscillator(),g=audioCtx.createGain();
            o.type='sawtooth'; o.frequency.setValueAtTime(180,audioCtx.currentTime);
            o.frequency.exponentialRampToValueAtTime(60,audioCtx.currentTime+0.3);
            g.gain.setValueAtTime(0.14,audioCtx.currentTime);
            g.gain.exponentialRampToValueAtTime(0.001,audioCtx.currentTime+0.3);
            o.connect(g); g.connect(audioCtx.destination); o.start(); o.stop(audioCtx.currentTime+0.3);
        }
        function playDialClick() {
            resume();
            const o=audioCtx.createOscillator(),g=audioCtx.createGain();
            o.type='square'; o.frequency.value=300;
            g.gain.setValueAtTime(0.08,audioCtx.currentTime);
            g.gain.exponentialRampToValueAtTime(0.001,audioCtx.currentTime+0.05);
            o.connect(g); g.connect(audioCtx.destination); o.start(); o.stop(audioCtx.currentTime+0.05);
        }

        // ================================================================
        //  TEXTURES — 256x256 NearestFilter PSX style
        // ================================================================
        function makeTex(c,ru,rv){
            const t=new THREE.CanvasTexture(c);
            t.magFilter=THREE.NearestFilter; t.minFilter=THREE.NearestFilter; t.generateMipmaps=false;
            t.wrapS=t.wrapT=THREE.RepeatWrapping; if(ru)t.repeat.set(ru,rv||ru); return t;
        }

        // Stone wall — mortar lines, varied blocks, cracks, moisture stains
        function mkWallTex(){
            const c=document.createElement('canvas');c.width=256;c.height=256;const ctx=c.getContext('2d');
            ctx.fillStyle='#0d160d';ctx.fillRect(0,0,256,256);
            const bW=64,bH=48;
            for(let row=0;row<6;row++)for(let col=-1;col<5;col++){
                const ox=(row%2===0)?0:bW/2,bx=col*bW+ox,by=row*bH;
                const sh=Math.floor(Math.random()*22),g=28+sh,gv=46+sh;
                ctx.fillStyle=`rgb(${g},${gv},${g})`;ctx.fillRect(bx+2,by+2,bW-4,bH-4);
                // Surface noise — lots of it for PSX crunch
                for(let i=0;i<80;i++){ctx.fillStyle=`rgba(0,0,0,${Math.random()*0.22})`;ctx.fillRect(bx+2+Math.random()*(bW-4),by+2+Math.random()*(bH-4),Math.random()*6+1,Math.random()*5+1);}
                // Lighter highlight flecks
                for(let i=0;i<15;i++){ctx.fillStyle=`rgba(255,255,200,${Math.random()*0.04})`;ctx.fillRect(bx+2+Math.random()*(bW-4),by+2+Math.random()*(bH-4),Math.random()*3+1,Math.random()*2+1);}
                // Moisture streak
                if(Math.random()>0.45){const sx=bx+6+Math.random()*(bW-12);const gr=ctx.createLinearGradient(sx,by,sx+3,by+bH);gr.addColorStop(0,'rgba(40,20,5,0)');gr.addColorStop(0.3,'rgba(55,28,4,0.55)');gr.addColorStop(1,'rgba(35,15,2,0)');ctx.fillStyle=gr;ctx.fillRect(sx,by,4,bH);}
                // Crack (random 30% chance)
                if(Math.random()>0.7){ctx.strokeStyle=`rgba(0,0,0,0.7)`;ctx.lineWidth=1;ctx.beginPath();const cx2=bx+8+Math.random()*(bW-16),cy2=by+4+Math.random()*(bH-8);ctx.moveTo(cx2,cy2);ctx.lineTo(cx2+Math.random()*12-6,cy2+Math.random()*14+4);ctx.stroke();}
                // Top highlight
                ctx.fillStyle='rgba(255,255,255,0.035)';ctx.fillRect(bx+2,by+2,bW-4,2);
            }
            // Mortar
            ctx.strokeStyle='#060c06';ctx.lineWidth=2;
            for(let r=0;r<=6;r++){ctx.beginPath();ctx.moveTo(0,r*bH);ctx.lineTo(256,r*bH);ctx.stroke();}
            for(let r=0;r<6;r++){const ox=(r%2===0)?0:bW/2;for(let c2=-1;c2<=5;c2++){const bx=c2*bW+ox;ctx.beginPath();ctx.moveTo(bx,r*bH);ctx.lineTo(bx,(r+1)*bH);ctx.stroke();}}
            // Corner cracks on some blocks — drawn over mortar
            for(let i=0;i<8;i++){
                const cx3=Math.random()*240,cy3=Math.random()*240;
                ctx.strokeStyle='rgba(0,0,0,0.5)';ctx.lineWidth=1;ctx.beginPath();ctx.moveTo(cx3,cy3);
                let cx4=cx3,cy4=cy3;for(let s=0;s<4;s++){cx4+=Math.random()*8-4;cy4+=Math.random()*6+2;ctx.lineTo(cx4,cy4);}ctx.stroke();
            }
            return makeTex(c,1.2,1.4);
        }

        // Heavy metal floor — diamond plate grating with dirt/grease
        function mkFloorTex(){
            const c=document.createElement('canvas');c.width=256;c.height=256;const ctx=c.getContext('2d');
            ctx.fillStyle='#111111';ctx.fillRect(0,0,256,256);
            // Diamond plate pattern — rows of offset diamonds
            const cell=16;ctx.fillStyle='#1c1c1c';
            for(let y=0;y<256;y+=cell){for(let x=(y/cell%2===0)?0:cell/2;x<256;x+=cell){
                ctx.beginPath();ctx.moveTo(x+cell/2,y);ctx.lineTo(x+cell,y+cell/2);ctx.lineTo(x+cell/2,y+cell);ctx.lineTo(x,y+cell/2);ctx.closePath();ctx.fill();
                ctx.strokeStyle='rgba(0,0,0,0.6)';ctx.lineWidth=1;ctx.stroke();
            }}
            // Bolts at seam crossings
            for(let y=0;y<256;y+=64)for(let x=0;x<256;x+=64){
                ctx.fillStyle='#0e0e0e';ctx.beginPath();ctx.arc(x,y,5,0,Math.PI*2);ctx.fill();
                ctx.fillStyle='#080808';ctx.beginPath();ctx.arc(x,y,2.5,0,Math.PI*2);ctx.fill();
            }
            // Grease/dirt stains
            for(let i=0;i<30;i++){ctx.fillStyle=`rgba(0,0,0,${Math.random()*0.3+0.1})`;ctx.fillRect(Math.random()*240,Math.random()*240,Math.random()*30+5,Math.random()*3+1);}
            for(let i=0;i<12;i++){ctx.fillStyle=`rgba(255,120,0,${Math.random()*0.06})`;ctx.fillRect(Math.random()*240,Math.random()*240,Math.random()*20+4,Math.random()*20+4);}
            return makeTex(c,4,4);
        }

        // Concrete ceiling — cracked panels with water damage
        function mkCeilTex(){
            const c=document.createElement('canvas');c.width=256;c.height=256;const ctx=c.getContext('2d');
            ctx.fillStyle='#0e0f10';ctx.fillRect(0,0,256,256);
            // Panels
            ctx.strokeStyle='#090a0b';ctx.lineWidth=3;
            for(let x=0;x<=256;x+=64){ctx.beginPath();ctx.moveTo(x,0);ctx.lineTo(x,256);ctx.stroke();}
            for(let y=0;y<=256;y+=64){ctx.beginPath();ctx.moveTo(0,y);ctx.lineTo(256,y);ctx.stroke();}
            // Rust/water stains
            for(let i=0;i<20;i++){const gx=Math.random()*200+28,gy=Math.random()*200+28;const gr=ctx.createRadialGradient(gx,gy,0,gx,gy,25+Math.random()*20);gr.addColorStop(0,'rgba(60,30,10,0.25)');gr.addColorStop(1,'rgba(0,0,0,0)');ctx.fillStyle=gr;ctx.fillRect(gx-40,gy-40,80,80);}
            // Noise
            for(let i=0;i<5000;i++){ctx.fillStyle=`rgba(0,0,0,${Math.random()*0.18})`;ctx.fillRect(Math.random()*254,Math.random()*254,Math.random()*2+1,Math.random()*2+1);}
            // Cracks
            for(let i=0;i<6;i++){ctx.strokeStyle='rgba(0,0,0,0.6)';ctx.lineWidth=1;ctx.beginPath();let cx5=Math.random()*200+28,cy5=Math.random()*200+28;ctx.moveTo(cx5,cy5);for(let s=0;s<6;s++){cx5+=Math.random()*12-6;cy5+=Math.random()*12-6;ctx.lineTo(cx5,cy5);}ctx.stroke();}
            return makeTex(c,3,3);
        }

        // Heavy industrial door steel — riveted plates
        function mkDoorTex(){
            const c=document.createElement('canvas');c.width=128;c.height=256;const ctx=c.getContext('2d');
            ctx.fillStyle='#181818';ctx.fillRect(0,0,128,256);
            // Plate divisions
            for(let y=0;y<=256;y+=64){ctx.strokeStyle='#0a0a0a';ctx.lineWidth=3;ctx.beginPath();ctx.moveTo(0,y);ctx.lineTo(128,y);ctx.stroke();}
            // Rivet rows
            for(let y=32;y<256;y+=64)for(let x=14;x<128;x+=18){ctx.fillStyle='#111';ctx.beginPath();ctx.arc(x,y,4,0,Math.PI*2);ctx.fill();ctx.fillStyle='#0a0a0a';ctx.beginPath();ctx.arc(x,y,2,0,Math.PI*2);ctx.fill();}
            // Grime
            for(let i=0;i<3000;i++){ctx.fillStyle=`rgba(0,0,0,${Math.random()*0.2})`;ctx.fillRect(Math.random()*126,Math.random()*254,Math.random()*4+1,Math.random()*3+1);}
            // Scratches
            for(let i=0;i<8;i++){ctx.strokeStyle=`rgba(180,180,180,${Math.random()*0.06})`;ctx.lineWidth=1;ctx.beginPath();const sy=Math.random()*240;ctx.moveTo(Math.random()*20,sy);ctx.lineTo(Math.random()*20+80,sy+Math.random()*20-10);ctx.stroke();}
            return makeTex(c);
        }

        function mkGrimeTex(){
            const c=document.createElement('canvas');c.width=128;c.height=128;const ctx=c.getContext('2d');
            ctx.fillStyle='#1a1a1a';ctx.fillRect(0,0,128,128);
            for(let i=0;i<4000;i++){ctx.fillStyle=Math.random()>0.5?`rgba(0,0,0,${Math.random()*0.18})`:`rgba(70,55,30,${Math.random()*0.1})`;ctx.beginPath();ctx.arc(Math.random()*128,Math.random()*128,Math.random()*2.5,0,Math.PI*2);ctx.fill();}
            return makeTex(c);
        }

        function mkHazardTex(){
            const c=document.createElement('canvas');c.width=128;c.height=128;const ctx=c.getContext('2d');
            ctx.fillStyle='#b89028';ctx.fillRect(0,0,128,128);ctx.fillStyle='#0c0c0c';
            for(let i=-128;i<256;i+=32){ctx.beginPath();ctx.moveTo(i,0);ctx.lineTo(i+16,0);ctx.lineTo(i+144,128);ctx.lineTo(i+128,128);ctx.fill();}
            return makeTex(c);
        }

// Orb animated fluid canvas — updated each frame
        const orbCanvas=document.createElement('canvas');orbCanvas.width=64;orbCanvas.height=64;
        const orbCtx=orbCanvas.getContext('2d');
        const orbTex=new THREE.CanvasTexture(orbCanvas);
        orbTex.magFilter=THREE.LinearFilter;orbTex.minFilter=THREE.LinearFilter;

        // ---> THE FIX: Create the memory block ONCE outside the loop <---
        const orbImageData = orbCtx.createImageData(64, 64);

        function updateOrbTex(now){
            const t=now*0.0018;const w=64,h=64;
            
            // ---> THE FIX: Reuse the existing memory block <---
            const id=orbImageData; 
            const data=id.data;
            
            for(let y=0;y<h;y++)for(let x=0;x<w;x++){
                const nx=(x/w)*2-1,ny=(y/h)*2-1,r=Math.sqrt(nx*nx+ny*ny);
                if(r>1){data[(y*w+x)*4+3]=0;continue;}
                // Multiple wave interference for water droplet look
                const wave=Math.sin(nx*9+t*2.8)*0.45+Math.sin(ny*7+t*2.2)*0.45+Math.sin((nx+ny)*6+t*1.8)*0.35+Math.sin(r*14-t*3.5)*0.4+Math.sin((nx-ny)*5+t*2.5)*0.3;
                const intensity=(wave+2.5)/5.0;
                const edge=1-r*r;const b=edge*intensity;
                data[(y*w+x)*4+0]=Math.min(255,Math.floor(b*30+b*40*Math.sin(t+r*3)));
                data[(y*w+x)*4+1]=Math.min(255,Math.floor(b*210+b*45*Math.sin(t*1.3+nx*4)));
                data[(y*w+x)*4+2]=Math.min(255,Math.floor(b*255));
                data[(y*w+x)*4+3]=Math.min(255,Math.floor(edge*240*(0.6+intensity*0.4)));
            }
            orbCtx.putImageData(id,0,0);orbTex.needsUpdate=true;
        }

// ================================================================
        //  MATERIALS
        // ================================================================
        const wallTex=mkWallTex(),floorTex=mkFloorTex(),ceilTex=mkCeilTex(),doorTex=mkDoorTex();
        const matWall=new THREE.MeshStandardMaterial({map:wallTex, roughness: 0.9});
        const matFloor=new THREE.MeshStandardMaterial({map:floorTex, roughness: 0.8});
        const matCeil=new THREE.MeshStandardMaterial({map:ceilTex, roughness: 0.9});
        const matDoor=new THREE.MeshStandardMaterial({map:doorTex, roughness: 0.6});
        const matDarkMetal=new THREE.MeshStandardMaterial({map:mkGrimeTex(), roughness: 0.8});
        const matRusty=new THREE.MeshStandardMaterial({color:0x2a1f10, roughness: 0.9});
        const matSteel=new THREE.MeshStandardMaterial({color:0x4a4a4a, roughness: 0.5});
        const matChrome=new THREE.MeshStandardMaterial({color:0x666666, roughness: 0.2});
        const matHazard=new THREE.MeshStandardMaterial({map:mkHazardTex(), roughness: 0.8});
        const matWarnYellow=new THREE.MeshStandardMaterial({color:0xaa8800, roughness: 0.8});
        const matBlackHole=new THREE.MeshStandardMaterial({color:0x020202, roughness: 1.0});
        
        // These stay Basic because they emit their own light/color
        const matGlassRed=new THREE.MeshBasicMaterial({color:0xdd0000,transparent:true,opacity:0.85});
        const matIndicator=new THREE.MeshBasicMaterial({color:0xff0000});
        
        const matHydCyl=new THREE.MeshStandardMaterial({color:0x1a1a1a, roughness: 0.7});
        const matHydRod=new THREE.MeshStandardMaterial({color:0x888888, roughness: 0.4});
        // ================================================================
        //  PARTICLES
        // ================================================================
        const particles=[];
        const sparkGeo=new THREE.BoxGeometry(0.08,0.08,0.08);
        const sparkMat=new THREE.MeshBasicMaterial({color:0xff8800});
        const steamGeo=new THREE.PlaneGeometry(1.2,1.2);
        const steamMatBase=new THREE.MeshBasicMaterial({color:0xbbbbbb,transparent:true,opacity:0.35,depthWrite:false});

        function emitSpark(x,y,z){const s=new THREE.Mesh(sparkGeo,sparkMat);s.position.set(x,y,z);s.userData={vel:new THREE.Vector3((Math.random()-0.5)*6,Math.random()*6+2,(Math.random()-0.5)*6),life:0.8,type:'spark'};scene.add(s);particles.push(s);}
        function emitSteam(x,y,z){const mat=steamMatBase.clone(),s=new THREE.Mesh(steamGeo,mat);s.position.set(x,y,z);s.userData={vel:new THREE.Vector3((Math.random()-0.5)*1.5,Math.random()*2.5+0.5,(Math.random()-0.5)*1.5),life:1.2,type:'steam',mat};scene.add(s);particles.push(s);}

        // ================================================================
        //  COLLISION
        // ================================================================
        const solidDoorParts=[],partBox=new THREE.Box3();
        function registerSolid(m){solidDoorParts.push(m);}

        function isWall(x,z,r){
            const off=Math.floor(MAZE_SIZE/2);
            const x0=Math.floor((x-r+TILE_SIZE/2)/TILE_SIZE)+off-1,x1=Math.floor((x+r+TILE_SIZE/2)/TILE_SIZE)+off+1;
            const z0=Math.floor((z-r+TILE_SIZE/2)/TILE_SIZE)+off-1,z1=Math.floor((z+r+TILE_SIZE/2)/TILE_SIZE)+off+1;
            for(let i=x0;i<=x1;i++)for(let j=z0;j<=z1;j++){
                if(i<0||i>=MAZE_SIZE||j<0||j>=MAZE_SIZE||maze[i][j]!==1)continue;
                const wx=(i-off)*TILE_SIZE,wz=(j-off)*TILE_SIZE;
                const cx=Math.max(wx-TILE_SIZE/2,Math.min(x,wx+TILE_SIZE/2)),cz=Math.max(wz-TILE_SIZE/2,Math.min(z,wz+TILE_SIZE/2));
                if((x-cx)*(x-cx)+(z-cz)*(z-cz)<r*r)return true;
            }
            if(Math.abs(x-doorGroup.position.x)<TILE_SIZE&&Math.abs(z-doorGroup.position.z)<TILE_SIZE){
                const pb=new THREE.Box3(new THREE.Vector3(x-r,0,z-r),new THREE.Vector3(x+r,player.height,z+r));
                for(const sp of solidDoorParts){partBox.setFromObject(sp);if(pb.intersectsBox(partBox))return true;}
            }
            return false;
        }

// ================================================================
        //  LEVEL GEOMETRY (Optimized for Performance)
        // ================================================================
        
        // 1. SETUP LISTS
        // We do NOT use 'let', 'const', or 'window' here. 
        // This links directly to the global lists we made at the top.
        corridorLights = [];
        cullableMeshes = []; 

   // 2. FLOOR
        const floorMesh = new THREE.Mesh(new THREE.PlaneGeometry(MAZE_SIZE*TILE_SIZE, MAZE_SIZE*TILE_SIZE), matFloor);
        floorMesh.rotation.x = -Math.PI/2;
        floorMesh.receiveShadow = true;
        scene.add(floorMesh);
        // REMOVED: cullableMeshes.push(floorMesh); <-- Do not put it in the bucket!

        // 3. CEILING
        const ceilMesh = new THREE.Mesh(new THREE.PlaneGeometry(MAZE_SIZE*TILE_SIZE, MAZE_SIZE*TILE_SIZE), matCeil);
        ceilMesh.rotation.x = Math.PI/2;
        ceilMesh.position.y = 14;
        ceilMesh.receiveShadow = true;
        scene.add(ceilMesh);
        // REMOVED: cullableMeshes.push(ceilMesh); <-- Do not put it in the bucket!

        // 4. WALLS (InstancedMesh)
        let wallCount = 0;
        for (let i = 0; i < MAZE_SIZE; i++) {
            for (let j = 0; j < MAZE_SIZE; j++) {
                if (maze[i][j] === 1) wallCount++;
            }
        }

        const iWallGeo = new THREE.BoxGeometry(TILE_SIZE, 14, TILE_SIZE);
        matWall.shadowSide = THREE.DoubleSide; 

        const iWallMesh = new THREE.InstancedMesh(iWallGeo, matWall, wallCount);
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
        cullableMeshes.push(iWallMesh);

        // --- SIMPLE FUNCTIONING LIGHTS (Now safely following the geometry) ---
        {
            const sp = getPos(1, 1);
            let added = 0;
            // ... (Rest of your light fixture code follows)
            
            // 1. Procedural Scratched Texture (Keeping your original material!)
            const lightTexCanvas = document.createElement('canvas');
            lightTexCanvas.width = lightTexCanvas.height = 64;
            const ltCtx = lightTexCanvas.getContext('2d');
            ltCtx.fillStyle = '#222'; ltCtx.fillRect(0,0,64,64);
            for(let i=0; i<400; i++) {
                ltCtx.fillStyle = `rgba(255,255,255,${Math.random()*0.05})`;
                ltCtx.fillRect(Math.random()*64, Math.random()*64, 1, 10 * Math.random());
            }
            const lightTex = new THREE.CanvasTexture(lightTexCanvas);
            lightTex.magFilter = THREE.NearestFilter;

            const fixtureMat = new THREE.MeshStandardMaterial({
                map: lightTex, color: 0x444444, roughness: 0.8, metalness: 0.3
            });

            for(const cell of emptyCells) {
                if(added >= 14) break;
                const pos = getPos(cell.x, cell.z);
                if(Math.hypot(pos.x - sp.x, pos.z - sp.z) < 14) continue;

                if(Math.random() > 0.85) {
                    const lightGroup = new THREE.Group();
                    lightGroup.position.set(pos.x, 13.9, pos.z);

                    // A. THE HOUSING (Your original boxes)
                    const mainBody = new THREE.Mesh(new THREE.BoxGeometry(2.5, 0.15, 0.6), fixtureMat);
                    lightGroup.add(mainBody);
                    const bezelTop = new THREE.Mesh(new THREE.BoxGeometry(2.7, 0.04, 0.7), fixtureMat);
                    bezelTop.position.y = 0.08;
                    lightGroup.add(bezelTop);

                    // B. THE HARDWARE (Your original screws)
                    const screwGeo = new THREE.CylinderGeometry(0.03, 0.03, 0.02, 6);
                    const screwMat = new THREE.MeshStandardMaterial({color: 0x111111});
                    [[1.1, 0.22], [1.1, -0.22], [-1.1, 0.22], [-1.1, -0.22]].forEach(loc => {
                        const s = new THREE.Mesh(screwGeo, screwMat);
                        s.position.set(loc[0], -0.07, loc[1]);
                        lightGroup.add(s);
                    });

                    // C. THE RADIATING ELEMENT (Your original glowing tube)
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
                    
                    // Basic shadow setup that won't leak or draw lines
                    light.castShadow = true;
                    light.shadow.mapSize.width = 256;  // <--- LOWERED FOR PERFORMANCE
                    light.shadow.mapSize.height = 256; // <--- LOWERED FOR PERFORMANCE
                    light.shadow.bias = -0.005; 

                    scene.add(light);

                    // Push both the light AND the strip to the array
                    corridorLights.push({
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
const startPos=getPos(1,1);
        camera.position.set(startPos.x,player.height,startPos.z);camera.rotation.set(0,yaw,0);

           let doorState='closed';
        const doorWP=getPos(exitGridX,exitGridZ);
        const doorGroup=new THREE.Group();
        doorGroup.position.set(doorWP.x,0,doorWP.z);

        // Door geometry: FH=frame height, FAR=distance in front toward player
        // PW=panel half-width. NOTHING is registered solid below y=0.5.
        const FH=17, FAR=-2.0, PW=5.0;

        // New door sound engine — all oscillator-based, no old variables needed
        let doorAudio={ctx:audioCtx, klaxonOsc:null, klaxonGain:null,
                       grindOsc:null, grindGain:null, rumbleOsc:null, rumbleGain:null,
                       steamSrc:null, steamGain:null, boltOsc:null, boltGain:null};

        function initDoorAudio(){
            const a=doorAudio; a.ctx=audioCtx; resume();
            // Klaxon — warbling triangle wave
            a.klaxonOsc=a.ctx.createOscillator(); a.klaxonOsc.type='triangle'; a.klaxonOsc.frequency.value=440;
            const klaxLFO=a.ctx.createOscillator(); klaxLFO.frequency.value=3;
            const klaxMod=a.ctx.createGain(); klaxMod.gain.value=120;
            klaxLFO.connect(klaxMod); klaxMod.connect(a.klaxonOsc.frequency); klaxLFO.start();
            a.klaxonGain=a.ctx.createGain(); a.klaxonGain.gain.value=0;
            a.klaxonOsc.connect(a.klaxonGain); a.klaxonGain.connect(a.ctx.destination); a.klaxonOsc.start();
            // Gear grind — sawtooth with bandpass
            a.grindOsc=a.ctx.createOscillator(); a.grindOsc.type='sawtooth'; a.grindOsc.frequency.value=38;
            const gbp=a.ctx.createBiquadFilter(); gbp.type='bandpass'; gbp.frequency.value=180; gbp.Q.value=2;
            a.grindGain=a.ctx.createGain(); a.grindGain.gain.value=0;
            a.grindOsc.connect(gbp); gbp.connect(a.grindGain); a.grindGain.connect(a.ctx.destination); a.grindOsc.start();
            // Deep rumble — very low square wave
            a.rumbleOsc=a.ctx.createOscillator(); a.rumbleOsc.type='square'; a.rumbleOsc.frequency.value=22;
            const rlp=a.ctx.createBiquadFilter(); rlp.type='lowpass'; rlp.frequency.value=80;
            a.rumbleGain=a.ctx.createGain(); a.rumbleGain.value=0;
            a.rumbleOsc.connect(rlp); rlp.connect(a.rumbleGain); a.rumbleGain.connect(a.ctx.destination); a.rumbleOsc.start();
            // Steam hiss — white noise highpass
            const nBuf=a.ctx.createBuffer(1,a.ctx.sampleRate*2,a.ctx.sampleRate);
            const nd=nBuf.getChannelData(0); for(let i=0;i<nd.length;i++)nd[i]=Math.random()*2-1;
            a.steamSrc=a.ctx.createBufferSource(); a.steamSrc.buffer=nBuf; a.steamSrc.loop=true;
            const shp=a.ctx.createBiquadFilter(); shp.type='highpass'; shp.frequency.value=1200;
            a.steamGain=a.ctx.createGain(); a.steamGain.gain.value=0;
            a.steamSrc.connect(shp); shp.connect(a.steamGain); a.steamGain.connect(a.ctx.destination); a.steamSrc.start();
            // Bolt clang — sawtooth burst played on demand via function
            a.boltOsc=a.ctx.createOscillator(); a.boltOsc.type='sawtooth'; a.boltOsc.frequency.value=95;
            a.boltGain=a.ctx.createGain(); a.boltGain.gain.value=0;
            a.boltOsc.connect(a.boltGain); a.boltGain.connect(a.ctx.destination); a.boltOsc.start();
        }

        function doorSnd(which,vol){
            const a=doorAudio; if(!a.klaxonGain)return;
            const t=a.ctx.currentTime;
            const set=(g,v)=>{if(g)g.gain.setTargetAtTime(v,t,0.12);};
            if(which==='klaxon') set(a.klaxonGain,vol);
            if(which==='grind')  set(a.grindGain,vol);
            if(which==='rumble') {if(a.rumbleGain)a.rumbleGain.gain.setTargetAtTime(vol,t,0.12);}
            if(which==='steam')  set(a.steamGain,vol);
            if(which==='bolt'){
                if(a.boltGain){
                    a.boltGain.gain.setValueAtTime(vol,t);
                    a.boltGain.gain.exponentialRampToValueAtTime(0.001,t+0.18);
                    a.boltOsc.frequency.setValueAtTime(95,t);
                    a.boltOsc.frequency.exponentialRampToValueAtTime(35,t+0.18);
                }
            }
        }

        function stopAllDoorAudio(){
            const a=doorAudio;
            try{if(a.klaxonOsc)a.klaxonOsc.stop();if(a.grindOsc)a.grindOsc.stop();
                if(a.rumbleOsc)a.rumbleOsc.stop();if(a.steamSrc)a.steamSrc.stop();
                if(a.boltOsc)a.boltOsc.stop();}catch(_){}
        }

        // GEAR FACTORY — used throughout the door
        const mkGear=(r,depth,teeth,mat)=>{
            const g=new THREE.Group();
            g.add(Object.assign(new THREE.Mesh(new THREE.CylinderGeometry(r*0.82,r*0.82,depth,18),mat||matChrome),{rotation:{x:Math.PI/2}}));
            const hub=new THREE.Mesh(new THREE.CylinderGeometry(r*0.24,r*0.24,depth+0.25,10),matDarkMetal); hub.rotation.x=Math.PI/2; g.add(hub);
            const tGeo=new THREE.BoxGeometry((Math.PI*r*2)/(teeth*2.1),r*0.28,depth*0.88);
            for(let i=0;i<teeth;i++){
                const a=(i/teeth)*Math.PI*2;
                const t=new THREE.Mesh(tGeo,matSteel); t.position.set(Math.cos(a)*r*0.92,Math.sin(a)*r*0.92,0); t.rotation.z=a+Math.PI/2; g.add(t);
            }
            for(let i=0;i<6;i++){
                const a=(i/6)*Math.PI*2;
                const sp=new THREE.Mesh(new THREE.BoxGeometry(r*0.68,r*0.11,depth*0.66),matDarkMetal);
                sp.position.set(Math.cos(a)*r*0.44,Math.sin(a)*r*0.44,0); sp.rotation.z=a+Math.PI/2; g.add(sp);
            }
            return g;
        };

        // ── FRAME: Thick I-beam pillars, NO floor geometry ────────────────
        const mkIPillar=(xs)=>{
            const g=new THREE.Group(); g.position.set(xs*6.6,FH/2,FAR);
            const web=new THREE.Mesh(new THREE.BoxGeometry(0.55,FH,2.2),matRusty); g.add(web);
            const tF=new THREE.Mesh(new THREE.BoxGeometry(3.6,0.75,2.6),matRusty); tF.position.y=FH/2-0.38; g.add(tF);
            for(const py of[FH*0.28,FH*0.0,-FH*0.22]){
                const mF=new THREE.Mesh(new THREE.BoxGeometry(3.2,0.42,2.2),matRusty); mF.position.y=py; g.add(mF);
            }
            const gp=new THREE.Mesh(new THREE.BoxGeometry(0.65,3.0,2.2),matDarkMetal); gp.position.y=FH/2-2.4; g.add(gp);
            // Bolt rows on flange face
            for(const by of[FH/2-0.38,FH*0.28,FH*0.0,-FH*0.22]) for(const bx of[-1.2,0,1.2]){
                const bolt=new THREE.Mesh(new THREE.CylinderGeometry(0.13,0.13,0.16,8),matChrome);
                bolt.rotation.x=Math.PI/2; bolt.position.set(bx,by,1.18); g.add(bolt);
            }
            doorGroup.add(g);
            // Collision hitbox — full height, but player walks between pillars
            const hb=new THREE.Mesh(new THREE.BoxGeometry(3.6,FH,2.6),new THREE.MeshBasicMaterial({visible:false}));
            hb.position.set(xs*6.6,FH/2,FAR); doorGroup.add(hb); registerSolid(hb);
        };
        mkIPillar(-1); mkIPillar(1);

        // Heavy lintel spanning the top — above the walkway
        const lintel=new THREE.Mesh(new THREE.BoxGeometry(17.0,3.4,2.6),matRusty);
        lintel.position.set(0,FH+1.4,FAR); lintel.castShadow=true;
        doorGroup.add(lintel); registerSolid(lintel);

        // Cross-braces from upper pillar to lintel centre (decorative, connected)
        for(const xs of[-1,1]){
            const bLen=6.2; const brace=new THREE.Mesh(new THREE.BoxGeometry(0.3,bLen,0.5),matDarkMetal);
            brace.position.set(xs*3.2,FH-0.5,FAR+0.3); brace.rotation.z=xs*0.5; doorGroup.add(brace);
        }

        // ── WARNING SIRENS ────────────────────────────────────────────────
        const sirens=[];
        const mkSiren=(x,z)=>{
            const sg=new THREE.Group(); sg.position.set(x,FH-1.2,z);
            sg.add(new THREE.Mesh(new THREE.CylinderGeometry(0.38,0.55,0.95,14),new THREE.MeshLambertMaterial({color:0x0c0c0c})));
            const dome=new THREE.Mesh(new THREE.SphereGeometry(0.40,12,8,0,Math.PI*2,0,Math.PI/2),matGlassRed);
            dome.position.y=0.08; sg.add(dome);
            const ref=new THREE.Mesh(new THREE.BoxGeometry(0.65,0.11,0.11),new THREE.MeshLambertMaterial({color:0xaaaa00}));
            sg.add(ref);
            const sl=new THREE.SpotLight(0xff2200,0,60,Math.PI/5,0.4,1);
            sl.position.set(0,0.2,0); sl.target.position.set(0,-8,6); sl.castShadow=false;
            sg.add(sl); sg.add(sl.target); doorGroup.add(sg);
            sirens.push({group:sg,light:sl,reflector:ref});
        };
        mkSiren(-6.2,FAR-0.4); mkSiren(6.2,FAR-0.4);
        mkSiren(-6.2,FAR+0.4); mkSiren(6.2,FAR+0.4);

        // Status indicator bars (glow green when unlocked)
        const matInd=matIndicator;
        const indL=new THREE.Mesh(new THREE.BoxGeometry(0.2,FH,0.2),matInd); indL.position.set(-5.0,FH/2,FAR); doorGroup.add(indL);
        const indR=new THREE.Mesh(new THREE.BoxGeometry(0.2,FH,0.2),matInd); indR.position.set(5.0,FH/2,FAR); doorGroup.add(indR);

        // ── DOOR PANELS — two slabs that slide apart ───────────────────────
        const doorHL=new THREE.Group(); doorHL.position.set(-PW/2,FH/2,0.5); doorGroup.add(doorHL);
        const doorHR=new THREE.Group(); doorHR.position.set(PW/2,FH/2,0.5); doorGroup.add(doorHR);

        const panGeo=new THREE.BoxGeometry(PW,FH,1.3);
        const pL2=new THREE.Mesh(panGeo,matDoor); pL2.castShadow=true; doorHL.add(pL2); registerSolid(pL2);
        const pR2=new THREE.Mesh(panGeo,matDoor); pR2.castShadow=true; doorHR.add(pR2); registerSolid(pR2);

        // Hazard edge strips
        const hzG=new THREE.BoxGeometry(0.45,FH,0.38);
        const hzL=new THREE.Mesh(hzG,matHazard); hzL.position.set(PW/2-0.22,0,0.74); doorHL.add(hzL);
        const hzR=new THREE.Mesh(hzG,matHazard); hzR.position.set(-PW/2+0.22,0,0.74); doorHR.add(hzR);

        // Rivet rows on panel face
        for(const px of[-PW/2+0.5,PW/2-0.5]) for(let py=-FH/2+1.2;py<FH/2;py+=2.1){
            const rv=new THREE.Mesh(new THREE.CylinderGeometry(0.1,0.1,0.1,8),matChrome);
            rv.rotation.x=Math.PI/2; rv.position.set(px,py,0.68); doorHL.add(rv);
            const rv2=rv.clone(); rv2.position.set(-px,py,0.68); doorHR.add(rv2);
        }

        // ── GEAR TRAIN — horizontal rack on panel tops, drive gears above lintel ──
        const tGeo2=new THREE.BoxGeometry(PW,0.62,0.52);
        const rackL2=new THREE.Mesh(tGeo2,matSteel); rackL2.position.set(0,FH/2+0.31,0); doorHL.add(rackL2);
        const rackR2=new THREE.Mesh(tGeo2,matSteel); rackR2.position.set(0,FH/2+0.31,0); doorHR.add(rackR2);
        const toothG=new THREE.BoxGeometry(0.28,0.38,0.48);
        for(let tx=-PW/2+0.28;tx<PW/2;tx+=0.58){
            const tL2=new THREE.Mesh(toothG,matSteel); tL2.position.set(tx,FH/2+0.62,0); doorHL.add(tL2);
            const tR2=new THREE.Mesh(toothG,matSteel); tR2.position.set(tx,FH/2+0.62,0); doorHR.add(tR2);
        }

        // Main drive gears — one per side, meshing with rack
        const GR=2.1, HGR=1.0;
        const gearY=FH+1.8, gearZ=FAR+0.65;
        const mgL=mkGear(GR,0.75,15); mgL.position.set(-PW-GR+0.3,gearY,gearZ); doorGroup.add(mgL);
        const mgR=mkGear(GR,0.75,15); mgR.position.set(PW+GR-0.3,gearY,gearZ); doorGroup.add(mgR);
        // Idler gears connected to motors
        const hgL=mkGear(HGR,0.55,9); hgL.position.set(-PW-GR*2.1+0.2,gearY+GR+HGR-0.25,gearZ); doorGroup.add(hgL);
        const hgR=mkGear(HGR,0.55,9); hgR.position.set(PW+GR*2.1-0.2,gearY+GR+HGR-0.25,gearZ); doorGroup.add(hgR);
        // Motor housings — bolted to lintel underside
        const mhMat=new THREE.MeshLambertMaterial({color:0x0a0a0a});
        const mhL=new THREE.Mesh(new THREE.BoxGeometry(3.1,2.5,1.9),mhMat); mhL.position.set(-PW-GR+0.3,gearY+GR+1.5,gearZ-0.4); doorGroup.add(mhL);
        const mhR=new THREE.Mesh(new THREE.BoxGeometry(3.1,2.5,1.9),mhMat); mhR.position.set(PW+GR-0.3,gearY+GR+1.5,gearZ-0.4); doorGroup.add(mhR);
        // Motor output shafts (connected visually from motor to gear)
        const shaftMat=new THREE.MeshLambertMaterial({color:0x333333});
        const shL=new THREE.Mesh(new THREE.CylinderGeometry(0.22,0.22,1.0,10),shaftMat); shL.rotation.x=Math.PI/2; shL.position.set(-PW-GR+0.3,gearY,gearZ-0.38); doorGroup.add(shL);
        const shR=new THREE.Mesh(new THREE.CylinderGeometry(0.22,0.22,1.0,10),shaftMat); shR.rotation.x=Math.PI/2; shR.position.set(PW+GR-0.3,gearY,gearZ-0.38); doorGroup.add(shR);
        // Gear indicator lights on motor housings
        const mIndL=new THREE.Mesh(new THREE.SphereGeometry(0.14,8,6),matInd); mIndL.position.set(-PW-GR+0.3-1.0,gearY+GR+2.2,gearZ+0.6); doorGroup.add(mIndL);
        const mIndR=new THREE.Mesh(new THREE.SphereGeometry(0.14,8,6),matInd); mIndR.position.set(PW+GR-0.3+1.0,gearY+GR+2.2,gearZ+0.6); doorGroup.add(mIndR);

        // ── LOCKING BOLTS — horizontal, above floor (never block walkway) ─
        const deadboltsL=[], deadboltsR=[];
        for(const yOff of[FH*0.52,FH*0.22,-FH*0.06]){
            // Left bolt group
            const bL=new THREE.Group(); bL.position.set(-PW-0.4,yOff,FAR-0.6);
            const bBody=new THREE.Mesh(new THREE.BoxGeometry(2.6,0.58,0.58),matChrome); bBody.position.x=-1.1; bL.add(bBody);
            const bHead=new THREE.Mesh(new THREE.BoxGeometry(0.82,0.88,0.88),matSteel); bHead.position.x=-2.55; bL.add(bHead);
            const bSlot=new THREE.Mesh(new THREE.BoxGeometry(1.0,0.82,0.82),matDarkMetal); bSlot.position.x=-3.7; bL.add(bSlot);
            // Connecting rod from bolt to frame — shows it's anchored
            const bRod=new THREE.Mesh(new THREE.CylinderGeometry(0.12,0.12,1.2,8),shaftMat); bRod.rotation.z=Math.PI/2; bRod.position.x=-4.5; bL.add(bRod);
            doorGroup.add(bL); deadboltsL.push(bL);
            // Right bolt group (mirror)
            const bR=new THREE.Group(); bR.position.set(PW+0.4,yOff,FAR-0.6);
            const bRBody=new THREE.Mesh(new THREE.BoxGeometry(2.6,0.58,0.58),matChrome); bRBody.position.x=1.1; bR.add(bRBody);
            const bRHead=new THREE.Mesh(new THREE.BoxGeometry(0.82,0.88,0.88),matSteel); bRHead.position.x=2.55; bR.add(bRHead);
            const bRSlot=new THREE.Mesh(new THREE.BoxGeometry(1.0,0.82,0.82),matDarkMetal); bRSlot.position.x=3.7; bR.add(bRSlot);
            const bRRod=new THREE.Mesh(new THREE.CylinderGeometry(0.12,0.12,1.2,8),shaftMat); bRRod.rotation.z=Math.PI/2; bRRod.position.x=4.5; bR.add(bRRod);
            doorGroup.add(bR); deadboltsR.push(bR);
        }

        // ── PRESSURE VALVES ───────────────────────────────────────────────
        const valves=[];
        for(const[xv,yv]of[[-3.6,FH*0.44],[-3.6,FH*0.12],[3.6,FH*0.44],[3.6,FH*0.12]]){
            const vG=new THREE.Group();
            const vBody=new THREE.Mesh(new THREE.CylinderGeometry(0.36,0.36,0.72,10),matSteel); vG.add(vBody);
            const vH1=new THREE.Mesh(new THREE.BoxGeometry(1.5,0.2,0.2),matWarnYellow); vH1.position.y=0.46; vG.add(vH1);
            const vH2=new THREE.Mesh(new THREE.BoxGeometry(0.2,0.2,1.5),matWarnYellow); vH2.position.y=0.46; vG.add(vH2);
            // Pipe stub connecting valve to door panel
            const vStub=new THREE.Mesh(new THREE.CylinderGeometry(0.14,0.14,0.8,8),matDarkMetal); vStub.position.y=-0.75; vG.add(vStub);
            vG.position.set(xv,yv,FAR); vG.rotation.x=Math.PI/2;
            doorGroup.add(vG); valves.push(vG);
        }

        // ── VAULT WHEEL (centre, connected via recessed shaft) ────────────
        const vaultWG=new THREE.Group(); vaultWG.position.set(0,FH*0.40,FAR+0.5); doorGroup.add(vaultWG);
        const vRim=new THREE.Mesh(new THREE.TorusGeometry(1.9,0.22,10,28),matRusty); vaultWG.add(vRim);
        const vDisc=new THREE.Mesh(new THREE.CylinderGeometry(1.9,1.9,0.52,26),matChrome); vDisc.rotation.x=Math.PI/2; vaultWG.add(vDisc);
        for(let i=0;i<8;i++){const a=(i/8)*Math.PI*2;const sp=new THREE.Mesh(new THREE.BoxGeometry(3.4,0.28,0.28),matSteel);sp.rotation.z=a;vaultWG.add(sp);}
        const vHub2=new THREE.Mesh(new THREE.CylinderGeometry(0.48,0.48,0.72,12),matDarkMetal); vHub2.rotation.x=Math.PI/2; vaultWG.add(vHub2);
        // Shaft from wheel back into door panel — shows it's connected
        const wShaft=new THREE.Mesh(new THREE.CylinderGeometry(0.2,0.2,0.8,10),shaftMat); wShaft.rotation.x=Math.PI/2; wShaft.position.z=-0.65; vaultWG.add(wShaft);

        // ── PRESSURE GAUGES ───────────────────────────────────────────────
        const mkGauge2=(xg,yg)=>{
            const g=new THREE.Group(); g.position.set(xg,yg,FAR);
            const face=new THREE.Mesh(new THREE.CylinderGeometry(0.62,0.62,0.18,16),new THREE.MeshLambertMaterial({color:0x080808}));
            face.rotation.x=Math.PI/2; g.add(face);
            g.add(new THREE.Mesh(new THREE.TorusGeometry(0.62,0.09,8,20),matChrome));
            const needle=new THREE.Mesh(new THREE.BoxGeometry(0.06,0.46,0.07),new THREE.MeshBasicMaterial({color:0xff3300}));
            needle.position.set(0.18,0.15,0.12); needle.rotation.z=-0.55; g.add(needle);
            doorGroup.add(g);
        };
        mkGauge2(-5.5,FH*0.70); mkGauge2(5.5,FH*0.70);
        mkGauge2(-5.5,FH*0.22); mkGauge2(5.5,FH*0.22);

        // ── PIPE NETWORK — all connected to real structures ───────────────
        const pipMat=new THREE.MeshLambertMaterial({color:0x181818});
        const mkPipe2=(x,y1,y2,z)=>{
            const len=Math.abs(y2-y1);
            const p=new THREE.Mesh(new THREE.CylinderGeometry(0.12,0.12,len,8),pipMat);
            p.position.set(x,(y1+y2)/2,z); doorGroup.add(p);
            for(const ey of[y1,y2]){const c=new THREE.Mesh(new THREE.CylinderGeometry(0.19,0.19,0.2,8),pipMat);c.position.set(x,ey,z);doorGroup.add(c);}
        };
        // Vertical pipe runs along pillar faces
        mkPipe2(-7.2, 2.2, FH-1.2, FAR-0.35);
        mkPipe2( 7.2, 2.2, FH-1.2, FAR-0.35);
        // Horizontal crossover pipes at mid height (connecting left to right)
        const hPipe1=new THREE.Mesh(new THREE.CylinderGeometry(0.12,0.12,8.0,8),pipMat);
        hPipe1.rotation.z=Math.PI/2; hPipe1.position.set(0,FH*0.35,FAR-0.4); doorGroup.add(hPipe1);
        const hPipe2=new THREE.Mesh(new THREE.CylinderGeometry(0.12,0.12,8.0,8),pipMat);
        hPipe2.rotation.z=Math.PI/2; hPipe2.position.set(0,FH*0.60,FAR-0.4); doorGroup.add(hPipe2);
        // Diagonal pipe from lower valve to gauge
        for(const xs of[-1,1]){
            const dp=new THREE.Mesh(new THREE.CylinderGeometry(0.1,0.1,2.5,8),pipMat);
            dp.position.set(xs*4.4,FH*0.27,FAR-0.3); dp.rotation.z=xs*0.35; doorGroup.add(dp);
        }

        scene.add(doorGroup);

  // ================================================================
        //  WALL PUZZLE PANELS — 6 panels with dedicated 3D models
        // ================================================================
        const PUZZLE_TYPES=['power','fuse','sequence','power','fuse','sequence'];
        const panelSearchSeeds=[
            {sx:Math.floor(MAZE_SIZE*0.2),sz:Math.floor(MAZE_SIZE*0.2)},
            {sx:Math.floor(MAZE_SIZE*0.8),sz:Math.floor(MAZE_SIZE*0.2)},
            {sx:Math.floor(MAZE_SIZE*0.2),sz:Math.floor(MAZE_SIZE*0.8)},
            {sx:Math.floor(MAZE_SIZE*0.8),sz:Math.floor(MAZE_SIZE*0.8)},
            {sx:Math.floor(MAZE_SIZE*0.5),sz:Math.floor(MAZE_SIZE*0.3)},
            {sx:Math.floor(MAZE_SIZE*0.5),sz:Math.floor(MAZE_SIZE*0.7)},
        ];
        const usedPanelCells=new Set();

        function findWallCell(seedX,seedZ){
            for(let radius=1;radius<12;radius++){
                for(let dx=-radius;dx<=radius;dx++){
                    for(let dz=-radius;dz<=radius;dz++){
                        const cx=seedX+dx,cz=seedZ+dz;
                        if(cx<1||cx>=MAZE_SIZE-1||cz<1||cz>=MAZE_SIZE-1)continue;
                        if(maze[cx][cz]!==0)continue;
                        const key=`${cx},${cz}`;
                        if(usedPanelCells.has(key))continue;
                        if(Math.hypot(cx-exitGridX,cz-(exitGridZ-3))<6)continue;
                        for(const[wx,wz]of[[1,0],[-1,0],[0,1],[0,-1]]){
                            const nx=cx+wx,nz=cz+wz;
                            if(nx>=0&&nx<MAZE_SIZE&&nz>=0&&nz<MAZE_SIZE&&maze[nx][nz]===1){
                                usedPanelCells.add(key);
                                return{cx,cz,wx,wz};
                            }
                        }
                    }
                }
            }
            return null;
        }

        function buildWallPanel(cx,cz,wx,wz,typeStr){
            const wp=getPos(cx,cz);
            const pwx=wp.x+wx*(TILE_SIZE/2-0.3);
            const pwz=wp.z+wz*(TILE_SIZE/2-0.3);
            const angle=Math.atan2(-wx,-wz);
            const grp=new THREE.Group();
            grp.position.set(pwx,0,pwz); grp.rotation.y=angle;

            // Mounting bracket
            const brk=new THREE.Mesh(new THREE.BoxGeometry(3.2,5.4,0.2),new THREE.MeshLambertMaterial({color:0x181408}));
            brk.position.set(0,2.6,-0.09); grp.add(brk);
            // Corner bolts
            for(const[bx,by]of[[-1.3,0.35],[1.3,0.35],[-1.3,4.9],[1.3,4.9]]){
                const bolt=new THREE.Mesh(new THREE.CylinderGeometry(0.14,0.14,0.13,8),matChrome);
                bolt.rotation.x=Math.PI/2; bolt.position.set(bx,by,0.07); grp.add(bolt);
            }
            // Bezel housing
            const bez=new THREE.Mesh(new THREE.BoxGeometry(3.0,5.0,0.45),new THREE.MeshLambertMaterial({color:0x0e0e0a}));
            bez.position.set(0,2.6,0.05); grp.add(bez);
            // Screen
            const screenMat=new THREE.MeshBasicMaterial({color:0x100004});
            const scrn=new THREE.Mesh(new THREE.BoxGeometry(2.4,3.0,0.05),screenMat);
            scrn.position.set(0,3.1,0.28); grp.add(scrn);
            // Status strip
            const stripMat=new THREE.MeshBasicMaterial({color:0x440008});
            const strip=new THREE.Mesh(new THREE.BoxGeometry(2.4,0.2,0.05),stripMat);
            strip.position.set(0,0.55,0.28); grp.add(strip);
            // Glow light
            const pLight=new THREE.PointLight(0x550010,1.4,8);
            pLight.position.set(0,2.6,1.2); grp.add(pLight);

            // Type-specific surface details
            if(typeStr==='power'){
                const condMat=new THREE.MeshLambertMaterial({color:0x1a2a10});
                for(const py of[1.2,2.2,3.2,4.0]){
                    const rail=new THREE.Mesh(new THREE.BoxGeometry(2.6,0.1,0.08),condMat);
                    rail.position.set(0,py,0.3); grp.add(rail);
                }
                for(const px of[-0.8,0,0.8]){
                    const vr=new THREE.Mesh(new THREE.BoxGeometry(0.1,3.0,0.08),condMat);
                    vr.position.set(px,2.5,0.3); grp.add(vr);
                }
                const nodeMat=new THREE.MeshBasicMaterial({color:0x00aa44});
                for(const[nx2,ny2]of[[-0.8,1.2],[0,2.2],[0.8,3.2],[-0.8,4.0],[0.8,1.2]]){
                    const nd=new THREE.Mesh(new THREE.BoxGeometry(0.25,0.25,0.12),nodeMat);
                    nd.position.set(nx2,ny2,0.32); grp.add(nd);
                }
            }
            if(typeStr==='fuse'){
                const fuseMat=new THREE.MeshLambertMaterial({color:0x886600});
                const fuseCapGeo=new THREE.CylinderGeometry(0.22,0.22,0.28,6);
                for(const[fx,fy]of[[-0.7,1.0],[0.7,1.0],[-0.7,2.0],[0.7,2.0],[-0.7,3.0],[0.7,3.0]]){
                    const fc=new THREE.Mesh(fuseCapGeo,fuseMat); fc.rotation.x=Math.PI/2;
                    fc.position.set(fx,fy,0.32); grp.add(fc);
                    const led=new THREE.Mesh(new THREE.SphereGeometry(0.08,6,4),new THREE.MeshBasicMaterial({color:0xff4400}));
                    led.position.set(fx,fy+0.35,0.3); grp.add(led);
                }
                const mfMat=new THREE.MeshLambertMaterial({color:0xaa8800});
                const mf=new THREE.Mesh(new THREE.CylinderGeometry(0.32,0.32,0.4,6),mfMat);
                mf.rotation.x=Math.PI/2; mf.position.set(0,4.2,0.33); grp.add(mf);
            }
            if(typeStr==='sequence'){
                const btnColors=[0xaa0000,0x006600,0x000088,0x886600];
                const btnPositions=[[-0.6,1.0],[0.6,1.0],[-0.6,2.2],[0.6,2.2]];
                btnPositions.forEach(([bx,by],i)=>{
                    const bMat=new THREE.MeshLambertMaterial({color:btnColors[i]});
                    const btn=new THREE.Mesh(new THREE.BoxGeometry(0.7,0.7,0.22),bMat);
                    btn.position.set(bx,by,0.32); grp.add(btn);
                });
                const waveMat=new THREE.MeshBasicMaterial({color:0x00cc66});
                for(let wi=0;wi<5;wi++){
                    const seg=new THREE.Mesh(new THREE.BoxGeometry(0.35,0.06,0.05),waveMat);
                    seg.position.set(-0.8+wi*0.4,3.5+Math.sin(wi*1.6)*0.18,0.3); grp.add(seg);
                }
            }

            scene.add(grp);
            const labels={power:'PWR-ROUTE',fuse:'FUSE-BOX',sequence:'SEQ-LOCK'};
            return{worldX:pwx,worldZ:pwz,type:typeStr,solved:false,group:grp,screenMat,stripMat,light:pLight,label:labels[typeStr]};
        }

        for(let i=0;i<6;i++){
            const seed=panelSearchSeeds[i];
            const cell=findWallCell(seed.sx,seed.sz);
            if(cell) wallPanels.push(buildWallPanel(cell.cx,cell.cz,cell.wx,cell.wz,PUZZLE_TYPES[i]));
        }

        // ================================================================
        //  PUZZLE ENGINE
        // ================================================================
        const BADGE_LABELS={power:'PWR',fuse:'FUSE',sequence:'SEQ'};
        const TYPE_LABELS={power:'PWR-ROUTE',fuse:'FUSE-BOX',sequence:'SEQ-LOCK'};

        function openPuzzle(panel){
            if(panel.solved)return;
            activePuzzle=panel; puzzleOpen=true; document.exitPointerLock();
            elPuzzleOverlay.setAttribute('data-ptype',panel.type);
            document.getElementById('puzzle-type-badge').innerText=BADGE_LABELS[panel.type]||'SYS';
            elPuzzleTitle.innerText=TYPE_LABELS[panel.type]||panel.label;
            elPuzzleStatus.innerText='AWAITING INPUT';
            const box=document.getElementById('puzzle-box');
            box.style.animation='none'; void box.offsetWidth; box.style.animation='';
            elPuzzleOverlay.style.display='flex'; elPuzzleOverlay.classList.add('active');
            if(panel.type==='power')    initPowerPuzzle();
            if(panel.type==='fuse')     initFusePuzzle();
            if(panel.type==='sequence') initSequencePuzzle();
            requestAnimationFrame(drawPuzzle);
        }
        function closePuzzle(){
            puzzleOpen=false; activePuzzle=null;
            elPuzzleOverlay.classList.remove('active'); elPuzzleOverlay.style.display='none';
            document.body.requestPointerLock();
        }
        function solvePuzzle(panel){
            panel.solved=true;
            panel.screenMat.color.setHex(0x002210);
            panel.stripMat.color.setHex(0x00aa44);
            panel.light.color.setHex(0x00ff66); panel.light.intensity=2.8;
            puzzlesSolved++;
            playPuzzleSuccess();
            elPuzzleStatus.innerText='SYSTEM ONLINE — '+(TOTAL_PUZZLES-puzzlesSolved)+' PANELS REMAINING';
            const slotIndex=wallPanels.indexOf(panel);
            if(slotIndex>=0){const slot=document.getElementById('tslot-'+slotIndex);if(slot)slot.classList.add('solved');}
            setTimeout(closePuzzle,1800);
        }

        // ── PUZZLE A: POWER ROUTING (5x5, no pre-solved path) ────────────
        const PR_SHAPES=[[0,1,1,0],[1,1,1,0],[1,0,1,0],[1,1,1,1]];

        function prRotateExits(exits,r){
            const e=[...exits];
            for(let i=0;i<r;i++){const tmp=e[3];e[3]=e[2];e[2]=e[1];e[1]=e[0];e[0]=tmp;}
            return e;
        }
        function initPowerPuzzle(){
            prGrid=[];
            for(let r=0;r<PR_SIZE;r++){prGrid[r]=[];for(let c=0;c<PR_SIZE;c++)prGrid[r][c]={shape:Math.floor(Math.random()*4),rot:Math.floor(Math.random()*4),powered:false};}
            const hubR=1+Math.floor(Math.random()*3),hubC=1+Math.floor(Math.random()*3);
            prGrid[hubR][hubC].shape=3; prGrid[hubR][hubC].rot=0;
            prGrid[PR_SIZE-1][Math.floor(Math.random()*PR_SIZE)].shape=2;
            prGrid[PR_SIZE-1][Math.floor(Math.random()*PR_SIZE)].rot=0;
            prGrid[0][Math.floor(Math.random()*PR_SIZE)].shape=2;
            prGrid[0][Math.floor(Math.random()*PR_SIZE)].rot=0;
            prCheckPower();
        }
        function prCheckPower(){
            for(let r=0;r<PR_SIZE;r++)for(let c=0;c<PR_SIZE;c++)prGrid[r][c].powered=false;
            const q=[];
            for(let c=0;c<PR_SIZE;c++){prGrid[PR_SIZE-1][c].powered=true;q.push([PR_SIZE-1,c]);}
            while(q.length){
                const[r,c]=q.shift();
                const exits=prRotateExits(PR_SHAPES[prGrid[r][c].shape],prGrid[r][c].rot);
                const dirs=[[-1,0],[0,1],[1,0],[0,-1]];
                exits.forEach((open,d)=>{
                    if(!open)return;
                    const[nr,nc]=[r+dirs[d][0],c+dirs[d][1]];
                    if(nr<0||nr>=PR_SIZE||nc<0||nc>=PR_SIZE||prGrid[nr][nc].powered)return;
                    const oppD=(d+2)%4;
                    const nExits=prRotateExits(PR_SHAPES[prGrid[nr][nc].shape],prGrid[nr][nc].rot);
                    if(nExits[oppD]){prGrid[nr][nc].powered=true;q.push([nr,nc]);}
                });
            }
        }
        function prIsSolved(){for(let c=0;c<PR_SIZE;c++)if(prGrid[0][c].powered)return true;return false;}
        function drawPowerPuzzle(){
            const W=480,H=400,pad=28,cellW=(W-pad*2)/PR_SIZE,cellH=(H-pad*2-50)/PR_SIZE;
            pCtx.fillStyle='#080c08'; pCtx.fillRect(0,0,W,H);
            for(let i=0;i<300;i++){pCtx.fillStyle=`rgba(0,0,0,${Math.random()*0.08})`;pCtx.fillRect(Math.random()*W,Math.random()*H,Math.random()*4+1,Math.random()*3+1);}
            pCtx.fillStyle='#101810'; pCtx.fillRect(0,0,W,46);
            pCtx.fillStyle='#284028'; pCtx.fillRect(0,44,W,2);
            pCtx.fillStyle='#40aa60'; pCtx.font='bold 11px Courier New';
            pCtx.fillText('\u26a1 POWER IN \u25bc  ROUTE SIGNAL TO \u25b2 POWER OUT',pad,16);
            pCtx.fillStyle='#286040'; pCtx.font='9px Courier New';
            pCtx.fillText('CLICK NODES TO ROTATE \u00b7 ALL CONNECTIONS MUST BE MUTUAL',pad,34);
            for(let r=0;r<PR_SIZE;r++)for(let c=0;c<PR_SIZE;c++){
                const node=prGrid[r][c];
                const x=pad+c*cellW+cellW/2,y=pad+50+r*cellH+cellH/2;
                const exits=prRotateExits(PR_SHAPES[node.shape],node.rot);
                const color=node.powered?'#00ffaa':'#1e4a1e';
                const fill=node.powered?'#003318':'#070f07';
                pCtx.save(); pCtx.translate(x,y);
                if(node.powered){pCtx.shadowColor='#00ff88';pCtx.shadowBlur=18;}
                pCtx.beginPath();
                for(let i=0;i<8;i++){const a=(i/8)*Math.PI*2-Math.PI/8;pCtx.lineTo(Math.cos(a)*16,Math.sin(a)*16);}
                pCtx.closePath();
                pCtx.fillStyle=fill; pCtx.fill();
                pCtx.strokeStyle=color; pCtx.lineWidth=node.powered?2.5:1; pCtx.stroke();
                pCtx.shadowBlur=0;
                pCtx.strokeStyle=color; pCtx.lineWidth=node.powered?5:2.5;
                const hw=cellW/2-2,hh=cellH/2-2;
                if(exits[0]){pCtx.beginPath();pCtx.moveTo(0,-9);pCtx.lineTo(0,-hh);pCtx.stroke();}
                if(exits[1]){pCtx.beginPath();pCtx.moveTo(9,0);pCtx.lineTo(hw,0);pCtx.stroke();}
                if(exits[2]){pCtx.beginPath();pCtx.moveTo(0,9);pCtx.lineTo(0,hh);pCtx.stroke();}
                if(exits[3]){pCtx.beginPath();pCtx.moveTo(-9,0);pCtx.lineTo(-hw,0);pCtx.stroke();}
                pCtx.fillStyle=node.powered?'#004422':'#0a120a'; pCtx.fillRect(-6,-6,12,12);
                pCtx.strokeStyle=color; pCtx.lineWidth=0.8; pCtx.strokeRect(-6,-6,12,12);
                pCtx.restore();
            }
            pCtx.fillStyle='#00ffaa'; pCtx.font='bold 9px Courier New';
            pCtx.fillText('\u26a1 POWER IN',pad,H-8);
            pCtx.fillText('\u26a1 POWER OUT',W-pad-70,62);
        }

        // ── PUZZLE B: FUSE BOX (5x5, TWO master fuses, 160 shuffles) ─────
        function initFusePuzzle(){
            fuseGrid=[];
            for(let r=0;r<FUSE_SIZE;r++){fuseGrid[r]=[];for(let c=0;c<FUSE_SIZE;c++)fuseGrid[r][c]=1;}
            fuseGrid[0][FUSE_SIZE-1]=2; fuseGrid[FUSE_SIZE-1][0]=3; fuseGrid[2][2]=0;
            fuseEmpty={r:2,c:2};
            for(let i=0;i<160;i++){
                const moves=[];
                if(fuseEmpty.r>0)moves.push({r:fuseEmpty.r-1,c:fuseEmpty.c});
                if(fuseEmpty.r<FUSE_SIZE-1)moves.push({r:fuseEmpty.r+1,c:fuseEmpty.c});
                if(fuseEmpty.c>0)moves.push({r:fuseEmpty.r,c:fuseEmpty.c-1});
                if(fuseEmpty.c<FUSE_SIZE-1)moves.push({r:fuseEmpty.r,c:fuseEmpty.c+1});
                const m=moves[Math.floor(Math.random()*moves.length)];
                fuseGrid[fuseEmpty.r][fuseEmpty.c]=fuseGrid[m.r][m.c];
                fuseGrid[m.r][m.c]=0; fuseEmpty={r:m.r,c:m.c};
            }
        }
        function fuseSlide(r,c){
            if(Math.abs(r-fuseEmpty.r)+Math.abs(c-fuseEmpty.c)!==1||fuseGrid[r][c]===0)return;
            fuseGrid[fuseEmpty.r][fuseEmpty.c]=fuseGrid[r][c];
            fuseGrid[r][c]=0; fuseEmpty={r,c}; playPuzzleTick();
        }
        function fuseIsSolved(){return fuseGrid[0][FUSE_SIZE-1]===2&&fuseGrid[FUSE_SIZE-1][0]===3;}
        function drawFusePuzzle(){
            const W=480,H=400,pad=30,cellW=(W-pad*2)/FUSE_SIZE,cellH=(H-pad*2-50)/FUSE_SIZE;
            pCtx.fillStyle='#0c0a06'; pCtx.fillRect(0,0,W,H);
            for(let i=0;i<300;i++){pCtx.fillStyle=`rgba(0,0,0,${Math.random()*0.1})`;pCtx.fillRect(Math.random()*W,Math.random()*H,Math.random()*4+1,2);}
            pCtx.fillStyle='#1a1000'; pCtx.fillRect(0,0,W,48);
            pCtx.fillStyle='#4a3000'; pCtx.fillRect(0,46,W,2);
            pCtx.fillStyle='#ffaa00'; pCtx.font='bold 11px Courier New';
            pCtx.fillText('\u2b21 FUSE BOX \u2014 SLIDE BOTH MASTERS TO TARGETS',pad,16);
            pCtx.fillStyle='#886000'; pCtx.font='9px Courier New';
            pCtx.fillText('[A]\u2192TOP-RIGHT  \u00b7  [B]\u2192BOTTOM-LEFT  \u00b7  CLICK ADJACENT TO MOVE',pad,34);
            pCtx.fillStyle='#0d0a06'; pCtx.fillRect(pad,pad+8,W-pad*2,H-pad*2-8);
            for(let r=0;r<FUSE_SIZE;r++)for(let c=0;c<FUSE_SIZE;c++){
                const val=fuseGrid[r][c];
                const x=pad+c*cellW+5,y=pad+50+r*cellH+5,fw=cellW-10,fh=cellH-10;
                if(val===0){pCtx.fillStyle='rgba(0,0,0,0.55)';pCtx.fillRect(x,y,fw,fh);continue;}
                const isA=(val===2),isB=(val===3),isMaster=isA||isB;
                pCtx.fillStyle=isA?'#2a1e00':isB?'#0a1a2a':'#141212';
                pCtx.beginPath();pCtx.roundRect(x,y,fw,fh,3);pCtx.fill();
                pCtx.strokeStyle=isA?'#ffaa00':isB?'#00aaff':'#3a2a10';pCtx.lineWidth=isMaster?2:1;pCtx.stroke();
                const hcx=x+fw/2,hcy=y+fh/2,hr2=Math.min(fw,fh)*0.26;
                pCtx.beginPath();
                for(let i=0;i<6;i++){const a=(i/6)*Math.PI*2;pCtx.lineTo(hcx+Math.cos(a)*hr2,hcy+Math.sin(a)*hr2);}
                pCtx.closePath();
                pCtx.fillStyle=isA?'#886600':isB?'#005588':'#1e1a16';pCtx.fill();
                pCtx.strokeStyle=isA?'#ffcc00':isB?'#00ccff':'#4a3820';pCtx.lineWidth=isMaster?1.5:0.8;pCtx.stroke();
                pCtx.fillStyle=isA?'#ffe080':isB?'#80e0ff':'#6a5840';
                pCtx.font=`bold ${isMaster?12:9}px Courier New`;pCtx.textAlign='center';
                pCtx.fillText(isA?'A':isB?'B':r*FUSE_SIZE+c,hcx,hcy+4);pCtx.textAlign='left';
            }
            pCtx.setLineDash([4,3]);
            pCtx.strokeStyle='#ffaa00';pCtx.lineWidth=2;
            pCtx.strokeRect(pad+(FUSE_SIZE-1)*cellW+5,pad+50+5,cellW-10,cellH-10);
            pCtx.strokeStyle='#00aaff';
            pCtx.strokeRect(pad+5,pad+50+(FUSE_SIZE-1)*cellH+5,cellW-10,cellH-10);
            pCtx.setLineDash([]);
        }

        // ── PUZZLE C: SEQUENCE (6 buttons, 6 rounds, reset on fail) ──────
        const SO_COLORS=[
            {on:'#ff2222',off:'#3a0505',label:'A'},
            {on:'#22ff44',off:'#053a10',label:'B'},
            {on:'#2244ff',off:'#050a3a',label:'C'},
            {on:'#ffcc00',off:'#3a2e00',label:'D'},
            {on:'#ff44ff',off:'#3a053a',label:'E'},
            {on:'#44ffff',off:'#053a3a',label:'F'},
        ];
        const SO_BTN_POS=[{x:55,y:110},{x:195,y:110},{x:335,y:110},{x:55,y:250},{x:195,y:250},{x:335,y:250}];
        const SO_BTN_SIZE=85;

        function initSequencePuzzle(){
            soSequence=[];
            for(let i=0;i<6;i++)soSequence.push(Math.floor(Math.random()*6));
            soPlayerSeq=[]; soRound=0; soState='watching'; soFlashing=[];
            startSoShow();
        }
        function startSoShow(){
            soState='watching'; soPlayerSeq=[]; soFlashing=[];
            const ft=Math.max(0.22,0.48-soRound*0.04);
            const gt=Math.max(0.08,0.18-soRound*0.02);
            for(let i=0;i<=soRound;i++)soFlashing.push({btnIdx:soSequence[i],timer:ft,gap:gt,phase:'on'});
            elPuzzleStatus.innerText='OBSERVE \u2014 ROUND '+(soRound+1)+' / '+soSequence.length;
        }
        function soClickBtn(btnIdx){
            if(soState!=='input')return;
            soPlayerSeq.push(btnIdx); playPuzzleTick();
            soFlashing.push({btnIdx,timer:0.10,phase:'flash',gap:0});
            const pos=soPlayerSeq.length-1;
            if(soPlayerSeq[pos]!==soSequence[pos]){
                soState='failed'; playPuzzleFail();
                elPuzzleStatus.innerText='WRONG \u2014 RESETTING TO ROUND 1';
                soRound=0; setTimeout(()=>startSoShow(),1600); return;
            }
            if(soPlayerSeq.length>soRound){
                soRound++;
                if(soRound>=soSequence.length) solvePuzzle(activePuzzle);
                else setTimeout(()=>startSoShow(),500);
            }
        }
        function drawSequencePuzzle(delta){
            soLastDelta=delta||0.016;
            const W=480,H=400;
            pCtx.fillStyle='#040408'; pCtx.fillRect(0,0,W,H);
            for(let i=0;i<200;i++){pCtx.fillStyle=`rgba(0,0,0,${Math.random()*0.1})`;pCtx.fillRect(Math.random()*W,Math.random()*H,Math.random()*5+1,2);}
            pCtx.fillStyle='#0a0010'; pCtx.fillRect(0,0,W,46);
            pCtx.fillStyle='#cc44ff'; pCtx.font='bold 11px Courier New';
            pCtx.fillText('\u25b6 SEQ-LOCK \u2014 MEMORIZE & REPEAT ALL 6 ROUNDS',30,16);
            pCtx.fillStyle='#663388'; pCtx.font='9px Courier New';
            pCtx.fillText('WRONG INPUT RESETS TO ROUND 1 \u00b7 SPEED INCREASES EACH ROUND',30,34);
            if(soFlashing.length>0&&soState==='watching'){
                const f=soFlashing[0];
                if(f.phase==='on'){f.timer-=soLastDelta;if(f.timer<=0){f.phase='off';f.timer=f.gap;}}
                else{f.timer-=soLastDelta;if(f.timer<=0){soFlashing.shift();if(soFlashing.length===0)soState='input';}}
            }
            SO_BTN_POS.forEach((pos,i)=>{
                const isFlashing=soFlashing.length>0&&soFlashing[0].phase==='on'&&soFlashing[0].btnIdx===i;
                const isPlayerFlash=soFlashing.some(f=>f.phase==='on'&&f.btnIdx===i&&f.gap===0);
                const active=isFlashing||isPlayerFlash;
                const col=SO_COLORS[i]; const depY=active?4:0;
                pCtx.fillStyle='rgba(0,0,0,0.7)';pCtx.fillRect(pos.x+4,pos.y+4,SO_BTN_SIZE,SO_BTN_SIZE);
                pCtx.fillStyle=active?col.on:col.off;pCtx.fillRect(pos.x,pos.y+depY,SO_BTN_SIZE,SO_BTN_SIZE-depY);
                if(!active){pCtx.fillStyle='rgba(255,255,255,0.08)';pCtx.fillRect(pos.x,pos.y,SO_BTN_SIZE,3);}
                pCtx.fillStyle=active?'#ffffff':col.on+'aa';
                pCtx.font='bold 20px Courier New';pCtx.textAlign='center';
                pCtx.fillText(col.label,pos.x+SO_BTN_SIZE/2,pos.y+SO_BTN_SIZE/2+depY+7);pCtx.textAlign='left';
                if(active){pCtx.shadowColor=col.on;pCtx.shadowBlur=22;pCtx.strokeStyle=col.on;pCtx.lineWidth=2;pCtx.strokeRect(pos.x,pos.y+depY,SO_BTN_SIZE,SO_BTN_SIZE-depY);pCtx.shadowBlur=0;}
            });
            pCtx.fillStyle='rgba(255,255,255,0.015)';
            for(let dx=0;dx<W;dx+=4)for(let dy=0;dy<H;dy+=4)if((dx+dy)%8===0)pCtx.fillRect(dx,dy,2,2);
            const seg=56;
            for(let i=0;i<soSequence.length;i++){
                const rx=30+i*seg,ry=H-22;
                pCtx.fillStyle=i<soRound?'#00ff88':i===soRound?'#ffffff':'#1a1a1a';
                pCtx.fillRect(rx,ry,seg-4,12);
                pCtx.fillStyle=i<soRound?'#004422':i===soRound?'#333':'#0a0a0a';
                pCtx.font='8px Courier New';pCtx.textAlign='center';
                pCtx.fillText(i+1,rx+(seg-4)/2,ry+9);pCtx.textAlign='left';
            }
        }

        // ── DRAW DISPATCHER ───────────────────────────────────────────────
        let _pLastT=0;
        function drawPuzzle(nowT){
            if(!puzzleOpen||!activePuzzle)return;
            const dt=nowT?Math.min((nowT-_pLastT)/1000,0.05):0.016; _pLastT=nowT||_pLastT;
            if(activePuzzle.type==='power')    drawPowerPuzzle();
            if(activePuzzle.type==='fuse')     drawFusePuzzle();
            if(activePuzzle.type==='sequence') drawSequencePuzzle(dt);
            if(puzzleOpen) requestAnimationFrame(drawPuzzle);
        }

        // ── CANVAS CLICK HANDLER ─────────────────────────────────────────
        elPuzzleCanvas.addEventListener('click',(e)=>{
            if(!puzzleOpen||!activePuzzle)return;
            const rect=elPuzzleCanvas.getBoundingClientRect();
            const mx=(e.clientX-rect.left)*(480/rect.width);
            const my=(e.clientY-rect.top)*(400/rect.height);
            if(activePuzzle.type==='power'){
                const pad=28,cellW=(480-pad*2)/PR_SIZE,cellH=(400-pad*2-50)/PR_SIZE;
                const c=Math.floor((mx-pad)/cellW),r=Math.floor((my-pad-50)/cellH);
                if(r>=0&&r<PR_SIZE&&c>=0&&c<PR_SIZE){
                    prGrid[r][c].rot=(prGrid[r][c].rot+1)%4; playPuzzleTick(); prCheckPower();
                    if(prIsSolved())solvePuzzle(activePuzzle);
                }
            }
            if(activePuzzle.type==='fuse'){
                const pad=30,cellW=(480-pad*2)/FUSE_SIZE,cellH=(400-pad*2-50)/FUSE_SIZE;
                const c=Math.floor((mx-pad)/cellW),r=Math.floor((my-pad-50)/cellH);
                if(r>=0&&r<FUSE_SIZE&&c>=0&&c<FUSE_SIZE){
                    fuseSlide(r,c);
                    if(fuseIsSolved())solvePuzzle(activePuzzle);
                }
            }
            if(activePuzzle.type==='sequence'&&soState==='input'){
                SO_BTN_POS.forEach((pos,i)=>{
                    if(mx>=pos.x&&mx<=pos.x+SO_BTN_SIZE&&my>=pos.y&&my<=pos.y+SO_BTN_SIZE)soClickBtn(i);
                });
            }
        });


        // Escape to close puzzle without solving
        document.addEventListener('keydown', (e)=>{
            if (e.code==='Escape' && puzzleOpen) { closePuzzle(); }
        }, {capture:true});

        // ================================================================
        //  MENU + INPUT
        // ================================================================
        const uiContainer=document.getElementById('main-ui');
        const engageBtn=document.getElementById('engage-btn');
        const nameInput=document.getElementById('name-input');
        const bgText=document.getElementById('input-bg-text');

        const quotes=["The corridors are wide, but the paths are many.","Do not trust the geometry.","They do not stop until you stop.","The light draws them. So does sound.","Some things cannot be outrun."];
        document.getElementById('lore-text').innerText=`"${quotes[Math.floor(Math.random()*quotes.length)]}"`;

        nameInput.addEventListener('focus',()=>{if(!nameInput.value){bgText.innerHTML='<div class="dots"><span>.</span><span>.</span><span>.</span></div>';bgText.style.opacity='1';}});
        nameInput.addEventListener('blur',()=>{if(!nameInput.value){bgText.innerHTML='NAMETAG';bgText.style.opacity='1';}});
        nameInput.addEventListener('input',e=>{playUISound(90,1.2,0.25,'triangle');e.target.value=e.target.value.replace(/[^A-Za-z]/g,'').toUpperCase();if(nameInput.value.length>0)bgText.style.opacity='0';else{bgText.style.opacity='1';bgText.innerHTML='<div class="dots"><span>.</span><span>.</span><span>.</span></div>';}});
        nameInput.addEventListener('keydown',e=>e.stopPropagation());nameInput.addEventListener('keyup',e=>e.stopPropagation());
        document.querySelectorAll('#main-ui button,#main-ui input').forEach(el=>{el.addEventListener('mouseenter',()=>playUISound(500,0.5,0.08,'triangle'));if(el!==engageBtn)el.addEventListener('mousedown',()=>playUISound(180,1.5,0.2,'sine'));else el.addEventListener('mousedown',()=>playUISound(100,2.0,0.4,'sine'));});
        engageBtn.addEventListener('mousedown',()=>{const g=document.querySelector('.grid-container');g.classList.remove('shake-active');void g.offsetWidth;g.classList.add('shake-active');document.body.requestPointerLock();});

        document.addEventListener('pointerlockchange',()=>{
            if(document.pointerLockElement===document.body){
                uiContainer.style.display='none';gameActive=true;if(startTime===0)startTime=Date.now();prevTime=performance.now();
                if(!introShown){
                    introShown=true;const name=nameInput.value||'OPERATIVE';
                    const fb=document.getElementById('fade-black');
                    fb.style.cssText='position:fixed;top:0;left:0;width:100%;height:100%;background:#000;z-index:200;opacity:1;display:flex;align-items:center;justify-content:center;pointer-events:none;transition:none;';
                    fb.innerHTML=`<div style="text-align:center;font-family:'Courier New',monospace;color:#a88840;letter-spacing:4px;"><div style="font-size:1.4em;font-weight:bold;margin-bottom:10px;">OPERATIVE: ${name}</div><div style="font-size:0.7em;color:#4a3820;letter-spacing:6px;margin-top:8px;">SIGNAL LOCKED — DEPLOYING</div></div>`;
                    setTimeout(()=>{fb.style.transition='opacity 1.8s ease-in-out';fb.style.opacity='0';setTimeout(()=>{fb.style.cssText='position:fixed;top:0;left:0;width:100%;height:100%;background:#000;opacity:0;z-index:105;transition:opacity 3s ease-in-out;pointer-events:none;';fb.innerHTML='';},1900);},1600);
                }
            } else if(!gameWon){
                uiContainer.style.display='flex';document.getElementById('main-title').innerText='SYSTEM PAUSED';engageBtn.innerText='RESUME';
                gameActive=false;accumulatedTime+=(Date.now()-startTime)/1000;document.getElementById('menuOrbCount').innerText=orbsCollected;elPrompt.style.display='none';
            }
        });

        document.addEventListener('mousemove',e=>{if(document.pointerLockElement===document.body){yaw-=e.movementX*SENSITIVITY;pitch-=e.movementY*SENSITIVITY;pitch=Math.max(-Math.PI/2,Math.min(Math.PI/2,pitch));camera.rotation.set(pitch,yaw,0);}});

        document.addEventListener('keydown',e=>{
            keys[e.code]=true;

            // --- Wall puzzle panels: E opens nearest unsolved panel ---
            if(e.code==='KeyE'&&gameActive&&!gameWon&&!puzzleOpen){
                for(const panel of wallPanels){
                    if(panel.solved)continue;
                    const dist=Math.hypot(camera.position.x-panel.worldX,camera.position.z-panel.worldZ);
                    if(dist<7){openPuzzle(panel);break;}
                }
            }

            // --- Exit terminal: E activates it when all objectives done ---
            if(e.code==='KeyE'&&gameActive&&!gameWon&&doorState==='ready_terminal'){
                if(Math.hypot(camera.position.x-TERM_WX,camera.position.z-TERM_WZ)<9){
                    terminalActivated=true;terminalBtnT=0.18;
                    termBtn.position.z=0.44;
                    termScreenMat.color.setHex(0xff4400);termLight.color.setHex(0xff6600);termLight.intensity=4;
                    ledMat.color.setHex(0xff4400);playTerminalClick();
                  setTimeout(()=>{doorState='valves_pressure';initDoorAudio();sirens.forEach(s=>s.light.intensity=50);},700);

                }
            }
        });
        document.addEventListener('keyup',e=>keys[e.code]=false);
       

        // ================================================================
        //  UPDATE LOOP
        // ================================================================
        function update(){
            if(!gameActive)return;
            const now=performance.now();
            const delta=Math.min((now-prevTime)/1000,0.05);prevTime=now;
            const totalElapsed=(accumulatedTime+(Date.now()-startTime)/1000).toFixed(1);
            if(!gameWon)elTimeVal.innerText=totalElapsed;

            // Update animated orb fluid texture once per frame
            updateOrbTex(now);

            // Track explored cells
            const pg=worldToGrid(camera.position.x,camera.position.z);exploredCells.add(`${pg.x},${pg.z}`);
// ---- MOVEMENT ----
            if(!gameWon){
                const inp=new THREE.Vector2(0,0);
                if(keys['KeyW'])inp.y-=1;if(keys['KeyS'])inp.y+=1;if(keys['KeyA'])inp.x-=1;if(keys['KeyD'])inp.x+=1;
                if(inp.length()>0)inp.normalize();
                const moving=inp.length()>0,isSprinting=keys['ShiftLeft']&&moving&&!player.isExhausted;
                currentlySprinting=isSprinting;

        // --- NEW: Bulletproof F Key Toggle (Smooth Intensity Version) ---
if(keys['KeyF'] && !window.fKeyWasPressed) {
    flashlightOn = !flashlightOn;
    flash1.intensity = flashlightOn ? 150 : 0;
    flash2.intensity = flashlightOn ? 30 : 0;
    if(typeof playFlashlightClick === 'function') playFlashlightClick();
    window.fKeyWasPressed = true;
    // Update the HUD indicator
    const fi = document.getElementById('flashlight-indicator');
    if (fi) { flashlightOn ? fi.classList.remove('off') : fi.classList.add('off'); }
} else if (!keys['KeyF']) {
    window.fKeyWasPressed = false;
}

                if(isSprinting){player.stamina-=0.4;
                                if(player.stamina<=0)player.isExhausted=true;}
                else{player.stamina=Math.min(MAX_STAMINA,player.stamina+0.9);if(player.stamina>=MAX_STAMINA*0.25)player.isExhausted=false;}
                const stPct=(player.stamina/MAX_STAMINA)*100;
                elStBar.style.height=stPct+'%';
                elStBar.style.background=player.isExhausted?'#8b0000':'linear-gradient(to top, #5a4200, #d4af37, #ffe060)';
                elStCont.classList.toggle('exhausted',player.isExhausted);

                // --- FIXED: Flashlight flicker now respects the toggle state ---
                if(flashlightOn) {
                    if(stPct<28){const fl=0.65+0.35*Math.abs(Math.sin(now*0.03+Math.sin(now*0.009)*4));flash1.intensity=90*fl;flash2.intensity=18*fl;}
                    else{flash1.intensity=90;flash2.intensity=18;}
                }

                // FOV sprint tunnel
                const tFOV=isSprinting?86:75;camera.fov+=(tFOV-camera.fov)*0.09;camera.updateProjectionMatrix();

                const spd=isSprinting?player.runSpeed:(moving?player.walkSpeed:0);
                const tv=inp.clone().multiplyScalar(spd);player.velocity.lerp(tv,0.14);
                const mx=player.velocity.x*Math.cos(yaw)+player.velocity.y*Math.sin(yaw);
                const mz=-player.velocity.x*Math.sin(yaw)+player.velocity.y*Math.cos(yaw);
                let tx=camera.position.x,tz=camera.position.z;
                if(!isWall(tx+mx,tz,player.radius))tx+=mx;
                if(!isWall(tx,tz+mz,player.radius))tz+=mz;
                camera.position.x=tx;camera.position.z=tz;

                const spd2=player.velocity.length();
                if(spd2>0.02){
                    const hz=isSprinting?3.5:1.5,amp=isSprinting?0.10:0.07;
                    player.headBobTimer+=delta*hz*Math.PI*2;
                    camera.position.y=player.height+Math.sin(player.headBobTimer)*amp;
                    const cycle=Math.floor(player.headBobTimer/Math.PI);
                    if(cycle>lastFootCycle){lastFootCycle=cycle;playFootstep(isSprinting);}
                    if(isSprinting){sprintAlertCD-=delta;if(sprintAlertCD<=0){sprintAlertCD=0.65;alertAllInRadius(camera.position.x,camera.position.z,22);}}
                } else {camera.position.y+=(player.height-camera.position.y)*0.1;player.headBobTimer+=delta;}
            }
            // ---- PARTICLES ----
            for(let i=particles.length-1;i>=0;i--){
                const p=particles[i];p.position.addScaledVector(p.userData.vel,delta);p.userData.life-=delta;
                if(p.userData.type==='steam'){p.userData.mat.opacity=(p.userData.life/1.2)*0.35;p.scale.setScalar(2.2-p.userData.life);}
                else if(p.userData.type==='spark'){p.userData.vel.y-=delta*18;if(p.position.y<0.1){p.position.y=0.1;p.userData.vel.y*=-0.4;}}
                if(p.userData.life<=0){scene.remove(p);if(p.userData.type==='steam')p.userData.mat.dispose();particles.splice(i,1);}
            }

// ---- PERFORMANCE OPTIMIZED LIGHT UPDATE (Lag-Free) ----
corridorLights.forEach(cl => {
    const now = performance.now();
    let targetI = 1.0;

    // 1. Flicker/Broken Logic (Kept exactly as yours)
    if (cl.broken) {
        const t = now * 0.001 * cl.rate + cl.seed;
        const noise = Math.sin(t * 7.8) * Math.sin(t * 3.3) * Math.sin(t * 15.0);
        targetI = noise > 0.1 ? 1.0 : 0.05;
        if (Math.random() > 0.98) targetI = 0; 
    } else {
        targetI = 0.9 + Math.sin(now * 0.005 + cl.seed) * 0.1; 
    }

    if (cl.currentI === undefined) cl.currentI = 0;
    cl.currentI += (targetI - cl.currentI) * 0.25; 

    // 2. The Ultimate Shadow Fix
    if (cl.light) {
        cl.light.intensity = cl.base * cl.currentI;

        // Calculate distance squared to the player
        const dx = camera.position.x - cl.light.position.x;
        const dz = camera.position.z - cl.light.position.z;
        const distSq = dx*dx + dz*dz;

        // ---> THE NEW FIX: Combine Distance AND Intensity <---
        // The shadow map only re-draws if the light is CLOSE (< 60 units) 
        // AND the light is actually ON (intensity > 0.1).
        const isClose = distSq < 3600;
        const isBrightEnough = cl.light.intensity > 0.1;

        cl.light.shadow.autoUpdate = (isClose && isBrightEnough);
        
        // Quality Optimization: Keep the shadow camera tight
        if(cl.light.shadow.camera.far !== 45) {
            cl.light.shadow.camera.far = 45;
            cl.light.shadow.camera.updateProjectionMatrix();
        }
    }

    // Keep your emissive strip syncing with the light
    if (cl.strip) cl.strip.emissiveIntensity = 2.5 * cl.currentI;
});
   // ---- HIGH-SPEED MESH CULLING (FPS BOOST) ----
        // We only check the specific "bucket" of walls and floors
        if (typeof cullableMeshes !== 'undefined' && cullableMeshes.length > 0) {
            cullableMeshes.forEach(obj => {
                // Safety: ensure the object and its position exist
                if (!obj || !obj.position) return;

                const dx = camera.position.x - obj.position.x;
                const dz = camera.position.z - obj.position.z;
                const distSq = dx*dx + dz*dz;

                // Thresholds: 
                // 1. If it's the giant Wall Mesh (iWallMesh), we use a massive distance (400 units)
                // 2. If it's a Floor/Ceiling, we use 120 units
                let limit = (obj.count !== undefined) ? 160000 : 14400; 

                if (distSq > limit) {
                    if (obj.visible) obj.visible = false;
                } else {
                    if (!obj.visible) obj.visible = true;
                }
            });
        }
            // ---- TERMINAL BUTTON ANIMATION ----
            if(terminalBtnT>0){terminalBtnT-=delta;if(terminalBtnT<=0)termBtn.position.z=0.56;}
            if(doorState==='ready_terminal'&&!terminalActivated)termLight.intensity=2.8+1.6*Math.sin(now*0.006);

            // ---- RADAR (200x200) ----
            rCtx.clearRect(0,0,radarCanvas.width,radarCanvas.height);
            // Outer ring
            rCtx.strokeStyle='rgba(60,100,55,0.4)';rCtx.lineWidth=1.5;rCtx.beginPath();rCtx.arc(RC,RC,RC-4,0,Math.PI*2);rCtx.stroke();
            // Range rings
            rCtx.strokeStyle='rgba(40,70,35,0.2)';rCtx.lineWidth=1;
            [RC*0.35,RC*0.65].forEach(r=>{rCtx.beginPath();rCtx.arc(RC,RC,r,0,Math.PI*2);rCtx.stroke();});
            // Crosshair lines
            rCtx.strokeStyle='rgba(50,85,45,0.2)';rCtx.beginPath();rCtx.moveTo(RC,8);rCtx.lineTo(RC,radarCanvas.height-8);rCtx.moveTo(8,RC);rCtx.lineTo(radarCanvas.width-8,RC);rCtx.stroke();

            // Explored cell dots
            rCtx.fillStyle='rgba(55,90,50,0.2)';
            exploredCells.forEach(k=>{
                const[gx,gz]=k.split(',').map(Number);const wp=getPos(gx,gz);
                const dx=wp.x-camera.position.x,dz=wp.z-camera.position.z;
                if(Math.hypot(dx,dz)>R_MAX)return;
                const lr=dx*Math.cos(yaw)-dz*Math.sin(yaw),lf=-dx*Math.sin(yaw)-dz*Math.cos(yaw);
                rCtx.fillRect(RC+lr*R_SCL-2,RC-lf*R_SCL-2,4,4);
            });

            // Player arrow
            rCtx.fillStyle='rgba(220,200,150,0.85)';
            rCtx.beginPath();rCtx.moveTo(RC,RC-9);rCtx.lineTo(RC-5,RC+6);rCtx.lineTo(RC,RC+3);rCtx.lineTo(RC+5,RC+6);rCtx.closePath();rCtx.fill();

            function drawBlip(wx,wz,col,sz){
                const dx=wx-camera.position.x,dz=wz-camera.position.z;
                let lr=dx*Math.cos(yaw)-dz*Math.sin(yaw),lf=-dx*Math.sin(yaw)-dz*Math.cos(yaw);
                const d=Math.hypot(lr,lf);if(d>R_MAX){lr=(lr/d)*R_MAX;lf=(lf/d)*R_MAX;}
                const rx=RC+lr*R_SCL,ry=RC-lf*R_SCL;
                rCtx.fillStyle=col;rCtx.beginPath();rCtx.arc(rx,ry,sz,0,Math.PI*2);rCtx.fill();
                return{rx,ry};
            }
            function drawDoor(wx,wz){
                const dx=wx-camera.position.x,dz=wz-camera.position.z;
                let lr=dx*Math.cos(yaw)-dz*Math.sin(yaw),lf=-dx*Math.sin(yaw)-dz*Math.cos(yaw);
                const d=Math.hypot(lr,lf);if(d>R_MAX){lr=(lr/d)*R_MAX;lf=(lf/d)*R_MAX;}
                const rx=RC+lr*R_SCL,ry=RC-lf*R_SCL;
                // Door icon — green arch
                rCtx.strokeStyle='rgba(40,180,60,0.9)';rCtx.lineWidth=2;
                rCtx.strokeRect(rx-6,ry-8,12,14);
                rCtx.fillStyle='rgba(20,120,30,0.6)';rCtx.fillRect(rx-4,ry-6,8,12);
            }
            drawDoor(doorGroup.position.x,doorGroup.position.z);
            if(doorState==='ready_terminal')drawBlip(TERM_WX,TERM_WZ,'rgba(0,220,255,0.9)',4);
            orbs.forEach(o=>{if(o.position.y>0){const{rx,ry}=drawBlip(o.position.x,o.position.z,'rgba(0,220,255,0.5)',3);const grd=rCtx.createRadialGradient(rx,ry,0,rx,ry,6);grd.addColorStop(0,'rgba(0,238,255,0.4)');grd.addColorStop(1,'rgba(0,0,0,0)');rCtx.fillStyle=grd;rCtx.beginPath();rCtx.arc(rx,ry,6,0,Math.PI*2);rCtx.fill();}});

            // ---- CROSSHAIR nearby orb check ----
            let nearOrb=false;orbs.forEach(o=>{if(o.position.y>0&&camera.position.distanceTo(o.position)<5.5)nearOrb=true;});
            elCross.classList.toggle('nearby',nearOrb);

            // ---- ADVANCED PHANTOM AI ----
            let closestDist=100;let anyAlerted=false;
            const camPos=camera.position;

            enemies.forEach((enemy,idx)=>{
                const ud=enemy.userData;
                const distE=camPos.distanceTo(enemy.position);
                if(distE<closestDist)closestDist=distE;

                // --- Group alert countdown ---
                if(ud.groupAlerted){ud.groupTimer-=delta;if(ud.groupTimer<=0)ud.groupAlerted=false;}

                // --- Light cone detection (only when not already hunting) ---
                if(ud.state==='patrol'||ud.state==='search'){
                    if(distE<LIGHT_RANGE){
                        const fwd=new THREE.Vector3(0,0,-1).applyQuaternion(camera.quaternion);
                        const toE=new THREE.Vector3().subVectors(enemy.position,camPos).normalize();
                        if(fwd.dot(toE)>CONE_COS&&hasLOS(camPos.x,camPos.z,enemy.position.x,enemy.position.z))
                            triggerAlert(enemy,false);
                    }
                }

                // --- State machine ---
                if(ud.state==='hunt'){
                    anyAlerted=true;
                    ud.alertTimer-=delta;ud.huntTimer-=delta;
                    ud.eyeL.intensity=2.5+Math.sin(now*0.012)*0.8;ud.eyeR.intensity=ud.eyeL.intensity;
                    ud.light.intensity=2.5;

                    // Record player position to memory (up to 8 entries)
                    if(hasLOS(camPos.x,camPos.z,enemy.position.x,enemy.position.z)){
                        ud.lastKnownGrid=worldToGrid(camPos.x,camPos.z);
                        ud.lastKnownPos={x:camPos.x,z:camPos.z};
                        ud.playerMemory.push({wx:camPos.x,wz:camPos.z,t:now});
                        if(ud.playerMemory.length>8)ud.playerMemory.shift();
                    }

                    // Predict player position from velocity if we have multiple memory entries
                    if(ud.playerMemory.length>=3){
                        const m=ud.playerMemory;const recent=m[m.length-1],older=m[m.length-3];
                        const dt=(recent.t-older.t)/1000;
                        if(dt>0.1){
                            const vx=(recent.wx-older.wx)/dt,vz=(recent.wz-older.wz)/dt;
                            const lookahead=2.5;
                            ud.predictedPos={x:recent.wx+vx*lookahead,z:recent.wz+vz*lookahead};
                        }
                    }

                    // Chase logic: BFS toward predicted or last known
                    ud.pathUpdateT-=delta;
                    if(ud.pathUpdateT<=0){
                        ud.pathUpdateT=1.2;
                        const target=ud.predictedPos||ud.lastKnownPos||{x:camPos.x,z:camPos.z};
                        const eg=worldToGrid(enemy.position.x,enemy.position.z);
                        const tg=worldToGrid(target.x,target.z);
                        const path=bfsPath(eg.x,eg.z,tg.x,tg.z);
                        if(path.length>0)ud.pathQueue=path;
                    }

                    if(ud.huntTimer<=0||ud.alertTimer<=0){ud.state='search';ud.searchTimer=SEARCH_DUR;ud.pathQueue=[];ud.pathUpdateT=0;}
                    ud.currentSpeed+=(HUNT_SPD-ud.currentSpeed)*0.04;

                    // Radar: pulsing red diamond
                    const pulse=0.55+0.45*Math.abs(Math.sin(now*0.008+idx));
                    const{rx,ry}=drawBlip(enemy.position.x,enemy.position.z,`rgba(255,0,0,${0.7+pulse*0.3})`,5+pulse*2);
                    // Glow
                    const g=rCtx.createRadialGradient(rx,ry,0,rx,ry,12);g.addColorStop(0,'rgba(255,0,0,0.35)');g.addColorStop(1,'rgba(255,0,0,0)');rCtx.fillStyle=g;rCtx.beginPath();rCtx.arc(rx,ry,12,0,Math.PI*2);rCtx.fill();

                } else if(ud.state==='search'){
                    anyAlerted=true;
                    ud.searchTimer-=delta;
                    ud.eyeL.intensity=1.2+Math.sin(now*0.005+idx)*0.4;ud.eyeR.intensity=ud.eyeL.intensity;
                    ud.light.intensity=1.8;

                    // Navigate to last known grid
                    if(ud.lastKnownGrid){
                        const lk=getPos(ud.lastKnownGrid.x,ud.lastKnownGrid.z);
                        if(Math.hypot(enemy.position.x-lk.x,enemy.position.z-lk.z)<TILE_SIZE*0.55||ud.searchTimer<=0){
                            // Check memory: is there another unvisited entry?
                            if(ud.playerMemory.length>0){
                                const mem=ud.playerMemory.pop();
                                ud.lastKnownGrid=worldToGrid(mem.wx,mem.wz);ud.pathQueue=[];ud.pathUpdateT=0;ud.searchTimer=SEARCH_DUR*0.6;
                            } else {
                                ud.state='patrol';ud.pathQueue=[];ud.eyeL.intensity=0;ud.eyeR.intensity=0;ud.light.intensity=1.2;
                                ud.predictedPos=null;
                            }
                        } else {
                            ud.pathUpdateT-=delta;
                            if(ud.pathUpdateT<=0){
                                ud.pathUpdateT=2.0;const eg=worldToGrid(enemy.position.x,enemy.position.z);
                                ud.pathQueue=bfsPath(eg.x,eg.z,ud.lastKnownGrid.x,ud.lastKnownGrid.z);
                            }
                        }
                    } else {ud.state='patrol';ud.eyeL.intensity=0;ud.eyeR.intensity=0;}
                    ud.currentSpeed+=(SEARCH_SPD-ud.currentSpeed)*0.03;

                    // Radar: orange smeared blob
                    const{rx:rx2,ry:ry2}=drawBlip(enemy.position.x,enemy.position.z,'rgba(220,110,0,0.75)',3.5);
                    const g2=rCtx.createRadialGradient(rx2,ry2,0,rx2,ry2,9);g2.addColorStop(0,'rgba(220,100,0,0.25)');g2.addColorStop(1,'rgba(0,0,0,0)');rCtx.fillStyle=g2;rCtx.beginPath();rCtx.arc(rx2,ry2,9,0,Math.PI*2);rCtx.fill();

                } else {
                    // PATROL: original wander, eyes dim
                    ud.eyeL.intensity=0;ud.eyeR.intensity=0;ud.light.intensity=0.8;
                    if(enemy.position.distanceTo(ud.targetPos)<0.55){
                        const cx=Math.round(ud.targetPos.x/TILE_SIZE)+Math.floor(MAZE_SIZE/2);
                        const cz=Math.round(ud.targetPos.z/TILE_SIZE)+Math.floor(MAZE_SIZE/2);
                        const nb=[];[[0,-1],[0,1],[-1,0],[1,0]].forEach(([dx2,dz2])=>{const nx=cx+dx2,nz=cz+dz2;if(nx>=0&&nx<MAZE_SIZE&&nz>=0&&nz<MAZE_SIZE&&maze[nx][nz]===0&&!(nx===ud.lastGrid.x&&nz===ud.lastGrid.z))nb.push({x:nx,z:nz});});
                        if(!nb.length&&maze[ud.lastGrid.x]&&maze[ud.lastGrid.x][ud.lastGrid.z]===0)nb.push(ud.lastGrid);
                        ud.lastGrid={x:cx,z:cz};const nc=nb.length?nb[Math.floor(Math.random()*nb.length)]:ud.lastGrid;
                        ud.targetPos.set(getPos(nc.x,nc.z).x,2.2,getPos(nc.x,nc.z).z);
                    }
                    ud.currentSpeed+=(PATROL_SPD-ud.currentSpeed)*0.02;
                    // Patrol: NOT shown on radar
                }

                // Follow BFS path
                if(ud.pathQueue.length>0){
                    const nc=ud.pathQueue[0],nw=getPos(nc.x,nc.z);
                    const nPos=new THREE.Vector3(nw.x,2.2,nw.z);
                    if(enemy.position.distanceTo(nPos)<TILE_SIZE*0.42)ud.pathQueue.shift();
                    else ud.targetPos.copy(nPos);
                }

                // Move with smooth speed
                const dir=new THREE.Vector3().subVectors(ud.targetPos,enemy.position);dir.y=0;
                if(dir.length()>0.01){dir.normalize();enemy.position.addScaledVector(dir,ud.currentSpeed);}

                // Visual wobble — sinusoidal undulation for ethereal feel
                const wt=now*0.0025+ud.wobbleSeed;
                enemy.position.y=2.2+Math.sin(wt)*0.35;
                enemy.rotation.y+=delta*(ud.state==='hunt'?1.4:0.6)*(idx%2===0?1:-1);
                // Scale pulsation
                const sc=ud.state==='hunt'?1.0+0.08*Math.sin(now*0.014+idx):1.0+0.03*Math.sin(wt);
                enemy.scale.setScalar(sc);

                // Core color changes with state
                if(ud.state==='hunt'){ud.coreMesh.material.color.setHex(0x220028);ud.midMesh.material.color.setHex(0x5a0066);}
                else if(ud.state==='search'){ud.coreMesh.material.color.setHex(0x1a0018);ud.midMesh.material.color.setHex(0x3a0050);}
                else{ud.coreMesh.material.color.setHex(0x110016);ud.midMesh.material.color.setHex(0x2a0050);}

                // Death
                if(!gameWon&&distE<2.8&&gameActive){
                    gameActive=false;document.exitPointerLock();
                    const t=(accumulatedTime+(Date.now()-startTime)/1000).toFixed(1);
                    document.getElementById('time-stat').innerText=t+'s';document.getElementById('orb-stat').innerText=`${orbsCollected} / ${TOTAL_ORBS}`;
                    document.getElementById('death-screen-ui').style.display='block';
                }
            });

            // Proximity shake/sting
            if(!gameWon&&closestDist<12){camera.position.x+=(Math.random()-0.5)*((12-closestDist)*0.018);if(!hasPlayedSting){playSting();hasPlayedSting=true;}}
            else hasPlayedSting=false;

            // ---- ORB COLLECTION ----
            orbs.forEach(orb=>{
                if(!gameWon&&orb.position.y>0&&camPos.distanceTo(orb.position)<2.8){
                    orb.position.y=-1000;orbsCollected++;elOrbCount.innerText=orbsCollected;
                    playOrbChime();alertAllInRadius(orb.position.x,orb.position.z,20);
                    if(orbsCollected===TOTAL_ORBS&&puzzlesSolved>=TOTAL_PUZZLES&&doorState==='closed'){
                        doorState='ready_terminal';
                        termScreenMat.color.setHex(0x001400);termLight.color.setHex(0x00ff44);termLight.intensity=3.5;
                        ledMat.color.setHex(0x00cc22);termBtnMat.color.setHex(0x00bb00);
                        playUISound(280,0.7,0.7,'sine');
                    } else if(orbsCollected===TOTAL_ORBS&&puzzlesSolved<TOTAL_PUZZLES&&doorState==='closed'){
                        termLight.color.setHex(0xff8800);
                        termLight.intensity=1.0+0.4*Math.sin(now*0.005);
                    }
                }
            });
            orbs.forEach(orb=>{if(orb.position.y>0&&orb.userData.ringMat)orb.userData.ringMat.opacity=0.25+0.18*Math.sin(now*0.005+orb.position.x);});

            // Siren spin
            sirens.forEach((s,i)=>s.group.rotation.y+=delta*(i%2===0?2.2:-2.2));
// ---- WALL PUZZLE PANEL PROMPTS + PULSE ----
            if (gameActive && !gameWon && !puzzleOpen) {
                let nearPanel = false;
                wallPanels.forEach(panel => {
                    const dist = Math.hypot(camPos.x-panel.worldX, camPos.z-panel.worldZ);
                    if (!panel.solved) {
                        panel.light.intensity = 1.0 + 0.6*Math.sin(now*0.004 + panel.worldX);
                    }
                    if (!panel.solved && dist < 7) nearPanel = true;
                });
      if (nearPanel && !terminalActivated) {
                    elPrompt.style.display = 'block';
                    document.getElementById('prompt-text').innerText = 'OPEN PANEL';
                } else if (!nearPanel) {
                    elPrompt.style.display = 'none';
                }
            }

            // Terminal proximity prompt
            if(gameActive&&!gameWon&&!terminalActivated){
                const dt=Math.hypot(camPos.x-TERM_WX,camPos.z-TERM_WZ);
 const showTerm = doorState==='ready_terminal' && dt < 9;
                elPrompt.style.display = showTerm ? 'block' : 'none';
                if (showTerm) document.getElementById('prompt-text').innerText = 'ACTIVATE TERMINAL';
            }

          // ---- DOOR ANIMATION ─────────────────────────────────────────
            if(!gameWon) camera.rotation.z=0;
            // Siren group spin (always active once door sequence starts)
            if(doorState!=='closed'&&doorState!=='ready_terminal'){
                sirens.forEach((s,i)=>{s.group.rotation.y+=delta*(i%2===0?2.6:-2.6);});
            }
            if(doorState!=='closed'&&doorState!=='open'&&doorState!=='ready_terminal'){
                const dtd=camPos.distanceTo(doorGroup.position),vs=Math.max(0,1-dtd/55);
                if(!gameWon&&dtd<50){camera.rotation.z=(Math.random()-0.5)*(50-dtd)*0.0012;}
                doorSnd('klaxon',vs*0.018);

                if(doorState==='valves_pressure'){
                    valves.forEach(v=>v.rotation.z+=delta*Math.PI*1.5);
                    if(Math.random()>0.5) emitSteam(doorGroup.position.x+(Math.random()-0.5)*4,1.2,doorGroup.position.z-1.5);
                    doorSnd('steam',vs*0.14);
                    if(valves[0].rotation.z>Math.PI*6){
                        doorState='vault_unlock';
                        doorSnd('steam',0); doorSnd('grind',vs*0.05);
                    }
                } else if(doorState==='vault_unlock'){
                    vaultWG.rotation.z+=delta*(Math.PI/4.2);
                    doorSnd('grind',vs*0.05);
                    if(vaultWG.rotation.z>Math.PI*2.0){
                        doorState='unlatching'; matInd.color.setHex(0x00ff00);
                        doorSnd('grind',0);
                        // Play three bolt clangs staggered
                        [0,0.18,0.36].forEach(delay=>setTimeout(()=>doorSnd('bolt',0.18),delay*1000));
                    }
                } else if(doorState==='unlatching'){
                    const bs=delta*0.85;
                    deadboltsL.forEach(b=>{b.position.x-=bs*4.2;});
                    deadboltsR.forEach(b=>{b.position.x+=bs*4.2;});
                    if(deadboltsL[0].position.x<-9.0){
                        doorState='sliding';
                        doorSnd('grind',vs*0.10); doorSnd('rumble',vs*0.12);
                    }
                } else if(doorState==='sliding'){
                    if(doorHL.position.x>-PW-3.5){
                        const sl=delta*0.58;
                        doorHL.position.x-=sl; doorHR.position.x+=sl;
                        // Gear rotation proportional to panel movement
                        mgL.rotation.z-=sl/GR; mgR.rotation.z+=sl/GR;
                        hgL.rotation.z+=(sl/GR)*(GR/HGR); hgR.rotation.z-=(sl/GR)*(GR/HGR);
                        if(Math.random()>0.35){
                            emitSpark(doorGroup.position.x-3.0,gearY,gearZ-0.3);
                            emitSpark(doorGroup.position.x+3.0,gearY,gearZ-0.3);
                        }
                        doorSnd('grind',vs*0.10); doorSnd('rumble',vs*0.12);
                    } else {
                        doorState='open';
                        sirens.forEach(s=>s.light.intensity=0);
                        doorSnd('klaxon',0); doorSnd('grind',0); doorSnd('rumble',0);
                        setTimeout(stopAllDoorAudio,2000);
                    }
                }
            }


     // --- UPDATE DUST PARTICLES (OPTIMIZED) ---
            if (dustParticles) {
                dustParticles.rotation.y -= 0.0004; 
                dustParticles.position.y = Math.sin(Date.now() * 0.0005) * 0.5;
            }

            // ---- WIN ----
            if(doorState==='open'&&camPos.z>doorGroup.position.z+1.5&&!gameWon){
                gameWon=true;document.exitPointerLock();
                const ws=document.getElementById('win-screen'),fb=document.getElementById('fade-black');
                ws.style.display='flex';setTimeout(()=>{fb.style.opacity='1';ws.style.opacity='1';},50);
                document.getElementById('finalTime').innerText=`FINAL TIME: ${totalElapsed}s`;
                elPrompt.style.display='none';
                  try{stopAllDoorAudio();}catch(_){}
            }
        }

        function animate(){requestAnimationFrame(animate);update();renderer.render(scene,camera);}
        animate();

        window.addEventListener('resize',()=>{camera.aspect=innerWidth/innerHeight;camera.updateProjectionMatrix();renderer.setSize(innerWidth,innerHeight);});

        document.getElementById('reboot-btn').addEventListener('click',()=>{
            const d=document.getElementById('death-screen-ui');d.style.transition='opacity 0.5s';d.style.opacity='0';setTimeout(()=>location.reload(),500);
        });
