
        import * as THREE from 'three';

        // ================================================================
        //  MAZE GENERATION
        // ================================================================
        const MAZE_SIZE=25, TILE_SIZE=12;
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

        // ================================================================
        //  SCENE — PSX style: low pixel ratio, nearest filter, no AA
        // ================================================================
        const scene=new THREE.Scene();
        scene.background=new THREE.Color(0x040508);
        scene.fog=new THREE.FogExp2(0x040508,0.022);

        const camera=new THREE.PerspectiveCamera(75,innerWidth/innerHeight,0.1,280);
        camera.rotation.order='YXZ';

       const renderer = new THREE.WebGLRenderer({ antialias: false });
renderer.setPixelRatio(Math.min(devicePixelRatio, 1) * 0.6);
renderer.setSize(innerWidth, innerHeight);

// Enable Shadows
renderer.shadowMap.enabled = true;
// CHANGE THIS LINE for the smooth look:
renderer.shadowMap.type = THREE.PCFSoftShadowMap; 

document.body.appendChild(renderer.domElement);
// Bodycam flashlight — Bigger, detailed, and toggleable
        let flashlightOn = true;
        const flash1=new THREE.SpotLight(0xfffdd8,150,80,Math.PI/4,0.1,1.8); 
        flash1.castShadow=true; flash1.shadow.mapSize.setScalar(1024); flash1.shadow.bias=-0.001;
        
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

        function updateOrbTex(now){
            const t=now*0.0018;const w=64,h=64;
            const id=orbCtx.createImageData(w,h);const data=id.data;
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
        //  LEVEL GEOMETRY
        // ================================================================
        // Floor
        const floorMesh=new THREE.Mesh(new THREE.PlaneGeometry(MAZE_SIZE*TILE_SIZE,MAZE_SIZE*TILE_SIZE),matFloor);
        floorMesh.rotation.x=-Math.PI/2;floorMesh.receiveShadow=true;scene.add(floorMesh);

        // Ceiling — same plane size as floor, at height 14
        const ceilMesh=new THREE.Mesh(new THREE.PlaneGeometry(MAZE_SIZE*TILE_SIZE,MAZE_SIZE*TILE_SIZE),matCeil);
        ceilMesh.rotation.x=Math.PI/2;ceilMesh.position.y=14;scene.add(ceilMesh);

       // Walls — InstancedMesh (1 draw call for all walls)
        let wallCount = 0;
        for (let i = 0; i < MAZE_SIZE; i++) {
            for (let j = 0; j < MAZE_SIZE; j++) {
                if (maze[i][j] === 1) wallCount++;
            }
        }

        const iWallGeo = new THREE.BoxGeometry(TILE_SIZE, 14, TILE_SIZE);
        
        // Fix for "leaking" light at the edges: ensures backfaces block light too
        matWall.shadowSide = THREE.DoubleSide; 

        const iWallMesh = new THREE.InstancedMesh(iWallGeo, matWall, wallCount);
        
        // CRITICAL: These tell the walls to actually stop the light beams
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

// --- SIMPLE FUNCTIONING LIGHTS (Keeping Original Fixture) ---
        const corridorLights = [];
        {
            const sp = getPos(1, 1);
            let added = 0;
            
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
        // ================================================================
        //  TITAN DOOR — fully rebuilt, purpose-built, no overlapping parts
        // ================================================================
        let doorState='closed';
        const doorWP=getPos(exitGridX,exitGridZ);
        const doorGroup=new THREE.Group();doorGroup.position.set(doorWP.x,0,doorWP.z);

        // --- Frame: Heavy I-beam pillars + lintel + threshold ---
        const FH=18,FZ=-1.8,PW=5.2;

        // Left pillar — I-beam cross section via three boxes
        const mkIPillar=(xSign)=>{
            const g=new THREE.Group();
            // Web (vertical center)
            const web=new THREE.Mesh(new THREE.BoxGeometry(0.5,FH,1.8),matRusty);g.add(web);
            // Top flange
            const topF=new THREE.Mesh(new THREE.BoxGeometry(3.2,0.6,2.2),matRusty);topF.position.y=FH/2-0.3;g.add(topF);
            // Bottom flange
            const botF=new THREE.Mesh(new THREE.BoxGeometry(3.2,0.6,2.2),matRusty);botF.position.y=-FH/2+0.3;g.add(botF);
            // Mid flange for rigidity
            const midF=new THREE.Mesh(new THREE.BoxGeometry(2.8,0.4,1.8),matRusty);midF.position.y=FH*0.15;g.add(midF);
            // Bolt plates on web
            const boltPl=new THREE.Mesh(new THREE.BoxGeometry(0.55,3.0,2.2),matDarkMetal);boltPl.position.set(0,-FH*0.15,0);g.add(boltPl);
            // Gusset triangle (bottom)
            const gusset=new THREE.Mesh(new THREE.BoxGeometry(0.3,2.5,1.6),matRusty);gusset.position.set(0,-FH/2+1.5,0);g.add(gusset);
            g.position.set(xSign*7.2,FH/2,FZ);
            doorGroup.add(g);
            // Register pillar for collision
            const hitbox=new THREE.Mesh(new THREE.BoxGeometry(3.2,FH,2.2),new THREE.MeshBasicMaterial({visible:false}));
            hitbox.position.set(xSign*7.2,FH/2,FZ);doorGroup.add(hitbox);registerSolid(hitbox);
        };
        mkIPillar(-1);mkIPillar(1);

        // Lintel — heavy beam across top
        const lintel=new THREE.Mesh(new THREE.BoxGeometry(17.8,3.0,2.2),matRusty);lintel.position.set(0,FH+0.8,FZ);lintel.castShadow=true;doorGroup.add(lintel);registerSolid(lintel);

        // Threshold at floor level
        const threshold=new THREE.Mesh(new THREE.BoxGeometry(17.8,0.4,2.2),matDarkMetal);threshold.position.set(0,0.2,FZ);doorGroup.add(threshold);registerSolid(threshold);

        // --- Warning sirens on pillars ---
        const sirens=[];
        const mkSiren=(x,z)=>{
            const sg=new THREE.Group();sg.position.set(x,FH-2,z);
            // Siren housing
            const housing=new THREE.Mesh(new THREE.CylinderGeometry(0.55,0.7,1.2,16),new THREE.MeshLambertMaterial({color:0x111111}));sg.add(housing);
            // Glass dome
            const dome=new THREE.Mesh(new THREE.SphereGeometry(0.5,12,8,0,Math.PI*2,0,Math.PI/2),matGlassRed);dome.position.y=0.1;sg.add(dome);
            // Spinning reflector inside
            const reflector=new THREE.Mesh(new THREE.CylinderGeometry(0.3,0.3,0.8,8),new THREE.MeshLambertMaterial({color:0x888800}));sg.add(reflector);
            const sp=new THREE.SpotLight(0xff2200,0,55,Math.PI/5.5,0.4,1);
            sp.position.set(0,0.3,0);sp.target.position.set(0,-8,8);sp.castShadow=false;
            sg.add(sp);sg.add(sp.target);doorGroup.add(sg);sirens.push({group:sg,light:sp,reflector});
        };
        mkSiren(-6.5,FZ-0.5);mkSiren(-6.5,FZ+0.5);mkSiren(6.5,FZ-0.5);mkSiren(6.5,FZ+0.5);

        // Indicator strips on inner frame edges
        const indL=new THREE.Mesh(new THREE.BoxGeometry(0.15,FH,0.15),matIndicator);indL.position.set(-5.5,FH/2,FZ);doorGroup.add(indL);
        const indR=new THREE.Mesh(new THREE.BoxGeometry(0.15,FH,0.15),matIndicator);indR.position.set(5.5,FH/2,FZ);doorGroup.add(indR);

        // --- Door Panels (left and right halves) ---
        const doorHL=new THREE.Group();doorHL.position.set(-PW/2,FH/2,0.4);doorGroup.add(doorHL);
        const doorHR=new THREE.Group();doorHR.position.set(PW/2,FH/2,0.4);doorGroup.add(doorHR);

        // Main panel slab — thick door texture
        const panelGeo=new THREE.BoxGeometry(PW,FH,1.4);
        const pL=new THREE.Mesh(panelGeo,matDoor);pL.castShadow=true;doorHL.add(pL);registerSolid(pL);
        const pR=new THREE.Mesh(panelGeo,matDoor);pR.castShadow=true;doorHR.add(pR);registerSolid(pR);

        // Hazard edge strips on inner faces of panels
        const hazEdgeGeo=new THREE.BoxGeometry(0.5,FH,0.4);
        const heL=new THREE.Mesh(hazEdgeGeo,matHazard);heL.position.set(PW/2-0.25,0,0.8);doorHL.add(heL);
        const heR=new THREE.Mesh(hazEdgeGeo,matHazard);heR.position.set(-PW/2+0.25,0,0.8);doorHR.add(heR);

        // Recessed surface panels (decorative)
        const recGeo=new THREE.BoxGeometry(PW-0.8,FH*0.35,0.25);
        const rec1L=new THREE.Mesh(recGeo,matDarkMetal);rec1L.position.set(0,FH*0.18,0.75);doorHL.add(rec1L);
        const rec2L=new THREE.Mesh(recGeo,matDarkMetal);rec2L.position.set(0,-FH*0.2,0.75);doorHL.add(rec2L);
        const rec1R=new THREE.Mesh(recGeo,matDarkMetal);rec1R.position.set(0,FH*0.18,0.75);doorHR.add(rec1R);
        const rec2R=new THREE.Mesh(recGeo,matDarkMetal);rec2R.position.set(0,-FH*0.2,0.75);doorHR.add(rec2R);

        // --- Rack and Pinion Drive System (top of door) ---
        // Rack bars — horizontal toothed bars embedded in top of each panel
        const rackGeo=new THREE.BoxGeometry(PW,0.7,0.6);
        const rackL=new THREE.Mesh(rackGeo,matSteel);rackL.position.set(0,FH/2+0.35,0);doorHL.add(rackL);
        const rackR=new THREE.Mesh(rackGeo,matSteel);rackR.position.set(0,FH/2+0.35,0);doorHR.add(rackR);

        // Rack teeth (evenly spaced along the bar)
        const toothGeo=new THREE.BoxGeometry(0.35,0.45,0.55);
        for(let tx=-PW/2+0.35;tx<PW/2;tx+=0.7){
            const tL=new THREE.Mesh(toothGeo,matSteel);tL.position.set(tx,FH/2+0.72,0);doorHL.add(tL);
            const tR=new THREE.Mesh(toothGeo,matSteel);tR.position.set(tx,FH/2+0.72,0);doorHR.add(tR);
        }

        // Main drive gear — centered above door gap
        const GR=2.0;
        const mkGear=(r,depth,teeth)=>{
            const g=new THREE.Group();
            const core=new THREE.Mesh(new THREE.CylinderGeometry(r*0.82,r*0.82,depth,20),matChrome);core.rotation.x=Math.PI/2;g.add(core);
            // Hub
            const hub=new THREE.Mesh(new THREE.CylinderGeometry(r*0.28,r*0.28,depth+0.3,10),matDarkMetal);hub.rotation.x=Math.PI/2;g.add(hub);
            // Teeth
            const tG=new THREE.BoxGeometry((Math.PI*r*2)/(teeth*2.2),r*0.28,depth*0.9);
            for(let i=0;i<teeth;i++){const a=(i/teeth)*Math.PI*2,t=new THREE.Mesh(tG,matSteel);t.position.set(Math.cos(a)*r*0.94,Math.sin(a)*r*0.94,0);t.rotation.z=a+Math.PI/2;g.add(t);}
            // Spokes
            for(let i=0;i<6;i++){const a=(i/6)*Math.PI*2,sp=new THREE.Mesh(new THREE.BoxGeometry(r*0.7,r*0.12,depth*0.7),matDarkMetal);sp.position.set(Math.cos(a)*r*0.42,Math.sin(a)*r*0.42,0);sp.rotation.z=a+Math.PI/2;g.add(sp);}
            const hb=new THREE.Mesh(new THREE.BoxGeometry(r*2.2,r*2.2,depth),new THREE.MeshBasicMaterial({visible:false}));g.add(hb);registerSolid(hb);
            return g;
        };
        const mgL=mkGear(GR,0.7,14);mgL.position.set(-PW-GR*0.5,FH/2+FH/2+GR,FZ+0.6);doorGroup.add(mgL);
        const mgR=mkGear(GR,0.7,14);mgR.position.set(PW+GR*0.5,FH/2+FH/2+GR,FZ+0.6);doorGroup.add(mgR);

        // Helper/idler gears
        const HGR=1.0;
        const hgL=mkGear(HGR,0.5,8);hgL.position.set(-PW-GR*0.5-GR-HGR+0.15,FH/2+FH/2+GR+0.8,FZ+0.6);doorGroup.add(hgL);
        const hgR=mkGear(HGR,0.5,8);hgR.position.set(PW+GR*0.5+GR+HGR-0.15,FH/2+FH/2+GR+0.8,FZ+0.6);doorGroup.add(hgR);

        // Motor housings above gears
        const motorHouseMat=new THREE.MeshLambertMaterial({color:0x0d0d0d});
        const mhL=new THREE.Mesh(new THREE.BoxGeometry(2.8,2.2,1.6),motorHouseMat);mhL.position.set(-PW-GR*0.5,FH/2+FH/2+GR+2.4,FZ+0.3);doorGroup.add(mhL);
        const mhR=new THREE.Mesh(new THREE.BoxGeometry(2.8,2.2,1.6),motorHouseMat);mhR.position.set(PW+GR*0.5,FH/2+FH/2+GR+2.4,FZ+0.3);doorGroup.add(mhR);
        // Motor indicator lights
        const mIndL=new THREE.Mesh(new THREE.BoxGeometry(0.3,0.3,0.05),matIndicator);mIndL.position.set(-PW-GR*0.5-0.8,FH/2+FH/2+GR+2.8,FZ+1.12);doorGroup.add(mIndL);
        const mIndR=new THREE.Mesh(new THREE.BoxGeometry(0.3,0.3,0.05),matIndicator);mIndR.position.set(PW+GR*0.5+0.8,FH/2+FH/2+GR+2.8,FZ+1.12);doorGroup.add(mIndR);

        // --- Hydraulic Pistons (hold door sealed, retract to allow sliding) ---
        // Left piston — vertical cylinder on outer left, presses down on panel
        const mkPiston=(xPos)=>{
            const g=new THREE.Group();g.position.set(xPos,FH*0.6,FZ-0.3);doorGroup.add(g);
            // Outer cylinder housing
            const cyl=new THREE.Mesh(new THREE.CylinderGeometry(0.7,0.7,5.5,14),matHydCyl);cyl.position.y=0;g.add(cyl);
            // End caps
            const capT=new THREE.Mesh(new THREE.CylinderGeometry(0.85,0.85,0.35,14),matRusty);capT.position.y=2.9;g.add(capT);
            const capB=new THREE.Mesh(new THREE.CylinderGeometry(0.85,0.85,0.35,14),matRusty);capB.position.y=-2.9;g.add(capB);
            // Hydraulic line ports (small nipples)
            const port=new THREE.Mesh(new THREE.CylinderGeometry(0.14,0.14,0.5,8),matChrome);port.rotation.z=Math.PI/2;port.position.set(0.72,1.5,0);g.add(port);
            // Piston rod (chrome — visible extending from bottom)
            const rod=new THREE.Mesh(new THREE.CylinderGeometry(0.38,0.38,4.5,12),matHydRod);rod.position.y=-3.6;g.add(rod);
            // Rod end with attachment clevis
            const clevis=new THREE.Mesh(new THREE.BoxGeometry(1.0,0.5,0.8),matRusty);clevis.position.y=-6.2;g.add(clevis);
            registerSolid(new THREE.Mesh(new THREE.BoxGeometry(1.4,5.5,1.4),new THREE.MeshBasicMaterial({visible:false})));
            return g;
        };
        const pistonGrpL=mkPiston(-8.5);
        const pistonGrpR=mkPiston(8.5);
        // We only animate pistonGrp position y, so wrap them
        const pistonGrp=new THREE.Group();doorGroup.add(pistonGrp);
        pistonGrp.add(pistonGrpL);pistonGrp.add(pistonGrpR);

        // --- Locking Bolts — horizontal square rods sliding from panel face into frame receivers ---
        // 3 bolts per side
        const deadboltsL=[],deadboltsR=[];
        for(const yOff of[-3.5,-0.5,2.5]){
            // Left side bolts (slide further left to unlock)
            const bL=new THREE.Group();
            const boltBody=new THREE.Mesh(new THREE.BoxGeometry(3.2,0.65,0.65),matChrome);boltBody.position.x=-1.4;bL.add(boltBody);
            const boltHead=new THREE.Mesh(new THREE.BoxGeometry(0.9,1.0,0.9),matSteel);boltHead.position.x=-3.05;bL.add(boltHead);
            const receiver=new THREE.Mesh(new THREE.BoxGeometry(1.0,0.9,0.9),matDarkMetal);receiver.position.x=-4.3;bL.add(receiver);
            bL.position.set(-PW-0.5,yOff,FZ-0.5);doorGroup.add(bL);deadboltsL.push(bL);
            // Right side bolts (mirror)
            const bR=new THREE.Group();
            const bRBody=new THREE.Mesh(new THREE.BoxGeometry(3.2,0.65,0.65),matChrome);bRBody.position.x=1.4;bR.add(bRBody);
            const bRHead=new THREE.Mesh(new THREE.BoxGeometry(0.9,1.0,0.9),matSteel);bRHead.position.x=3.05;bR.add(bRHead);
            const bRReceiver=new THREE.Mesh(new THREE.BoxGeometry(1.0,0.9,0.9),matDarkMetal);bRReceiver.position.x=4.3;bR.add(bRReceiver);
            bR.position.set(PW+0.5,yOff,FZ-0.5);doorGroup.add(bR);deadboltsR.push(bR);
        }
        // latchL/latchR for animation compatibility — use first bolt group as proxy
        const latchL=deadboltsL[0];const latchR=deadboltsR[0];

        // --- Pressure Release Valves (for the valves_pressure animation state) ---
        const valves=[];
        for(const[xv,yv]of[[-4.5,FH*0.3],[-4.5,-FH*0.15],[4.5,FH*0.3],[4.5,-FH*0.15]]){
            const vGrp=new THREE.Group();
            const body=new THREE.Mesh(new THREE.CylinderGeometry(0.35,0.35,0.7,10),matSteel);vGrp.add(body);
            const handle=new THREE.Mesh(new THREE.BoxGeometry(1.4,0.2,0.2),matWarnYellow);handle.position.y=0.45;vGrp.add(handle);
            const handleB=new THREE.Mesh(new THREE.BoxGeometry(0.2,0.2,1.4),matWarnYellow);handleB.position.y=0.45;vGrp.add(handleB);
            vGrp.position.set(xv,yv,FZ);vGrp.rotation.x=Math.PI/2;doorGroup.add(vGrp);valves.push(vGrp);
        }

        // --- Central Vault Wheel (vaultWG — rotates on vault_unlock) ---
        const vaultWG=new THREE.Group();vaultWG.position.set(0,FH*0.2,0.5);doorGroup.add(vaultWG);
        const vWheelCore=new THREE.Mesh(new THREE.CylinderGeometry(1.8,1.8,0.5,24),matChrome);vWheelCore.rotation.x=Math.PI/2;vaultWG.add(vWheelCore);
        const vWheelRim=new THREE.Mesh(new THREE.TorusGeometry(1.8,0.22,10,28),matRusty);vaultWG.add(vWheelRim);
        for(let i=0;i<8;i++){const a=(i/8)*Math.PI*2,sp=new THREE.Mesh(new THREE.BoxGeometry(3.4,0.28,0.28),matSteel);sp.rotation.z=a;sp.position.set(0,0,0.1);vaultWG.add(sp);}
        const vWheelHub=new THREE.Mesh(new THREE.CylinderGeometry(0.45,0.45,0.7,12),matDarkMetal);vWheelHub.rotation.x=Math.PI/2;vaultWG.add(vWheelHub);
        // Vault socket (receives the wheel pin on right panel)
        const vSocket=new THREE.Mesh(new THREE.CylinderGeometry(0.5,0.5,0.25,12),matBlackHole);vSocket.rotation.x=Math.PI/2;vSocket.position.set(0,FH*0.2,0.8);doorHR.add(vSocket);

        // Pressure gauge (decorative)
        const mkGauge=(xg,yg)=>{
            const g=new THREE.Group();g.position.set(xg,yg,FZ);doorGroup.add(g);
            const face=new THREE.Mesh(new THREE.CylinderGeometry(0.6,0.6,0.18,16),new THREE.MeshLambertMaterial({color:0x0a0a0a}));face.rotation.x=Math.PI/2;g.add(face);
            const rim=new THREE.Mesh(new THREE.TorusGeometry(0.6,0.08,8,20),matChrome);g.add(rim);
            const needle=new THREE.Mesh(new THREE.BoxGeometry(0.05,0.45,0.06),new THREE.MeshBasicMaterial({color:0xff3300}));needle.position.set(0.18,0.15,0.12);needle.rotation.z=-0.6;g.add(needle);
        };
        mkGauge(-5.5,FH*0.45);mkGauge(5.5,FH*0.45);

        // Hydraulic pipe runs (decorative thin pipes along frame)
        const pipeMat=new THREE.MeshLambertMaterial({color:0x1a1a1a});
        const mkPipeRun=(x,y1,y2,z)=>{const p=new THREE.Mesh(new THREE.CylinderGeometry(0.12,0.12,Math.abs(y2-y1),8),pipeMat);p.position.set(x,(y1+y2)/2,z);doorGroup.add(p);};
        mkPipeRun(-7.8,4,FH-2,FZ-0.2);mkPipeRun(7.8,4,FH-2,FZ-0.2);

        scene.add(doorGroup);

        // ================================================================
        //  TERMINAL PANEL — wall-anchored, never floating
        //  Find open cell adjacent to wall near door approach, mount on wall face
        // ================================================================
        let termCellX=-1,termCellZ=-1,termFaceX=0,termFaceZ=0;
        const searchX=exitGridX,searchZ=exitGridZ-3;
        outer:for(let radius=1;radius<8;radius++){
            for(let dx=-radius;dx<=radius;dx++)for(let dz=-radius;dz<=radius;dz++){
                const cx=searchX+dx,cz=searchZ+dz;
                if(cx<1||cx>=MAZE_SIZE-1||cz<1||cz>=MAZE_SIZE-1||maze[cx][cz]!==0)continue;
                for(const[wx,wz]of[[1,0],[-1,0],[0,1],[0,-1]]){
                    const nx=cx+wx,nz=cz+wz;
                    if(nx>=0&&nx<MAZE_SIZE&&nz>=0&&nz<MAZE_SIZE&&maze[nx][nz]===1){
                        termCellX=cx;termCellZ=cz;termFaceX=wx;termFaceZ=wz;break outer;
                    }
                }
            }
        }
        const termWP=getPos(termCellX,termCellZ);
        const TERM_WX=termWP.x+termFaceX*(TILE_SIZE/2-0.4);
        const TERM_WZ=termWP.z+termFaceZ*(TILE_SIZE/2-0.4);
        const termAngle=Math.atan2(-termFaceX,-termFaceZ);

        const termGrp=new THREE.Group();termGrp.position.set(TERM_WX,0,TERM_WZ);termGrp.rotation.y=termAngle;

        // Mounting bracket bolted into wall
        const mBracket=new THREE.Mesh(new THREE.BoxGeometry(4.2,6.8,0.3),matRusty);mBracket.position.set(0,2.6,-0.15);termGrp.add(mBracket);
        // Bolt heads on bracket
        for(const[bx2,by2]of[[-1.7,0.4],[1.7,0.4],[-1.7,4.8],[1.7,4.8]]){const bolt=new THREE.Mesh(new THREE.CylinderGeometry(0.15,0.15,0.12,8),matChrome);bolt.rotation.x=Math.PI/2;bolt.position.set(bx2,by2,0.06);termGrp.add(bolt);}

        // Main terminal housing
        const tHousing=new THREE.Mesh(new THREE.BoxGeometry(3.0,4.5,0.55),new THREE.MeshLambertMaterial({color:0x0c0c08}));tHousing.position.set(0,2.6,0.14);termGrp.add(tHousing);

        // Bezel frame around screen
        const tBezel=new THREE.Mesh(new THREE.BoxGeometry(2.6,3.2,0.1),new THREE.MeshLambertMaterial({color:0x1c1a0e}));tBezel.position.set(0,3.1,0.44);termGrp.add(tBezel);

        // Screen
        const termScreenMat=new THREE.MeshBasicMaterial({color:0x180002});
        const tScreen=new THREE.Mesh(new THREE.BoxGeometry(2.3,2.8,0.04),termScreenMat);tScreen.position.set(0,3.1,0.50);termGrp.add(tScreen);
        const termLight=new THREE.PointLight(0x550008,1.5,8);termLight.position.set(0,3.0,1.2);termGrp.add(termLight);

        // Button assembly (round with housing)
        const termBtnHouse=new THREE.Mesh(new THREE.BoxGeometry(0.8,0.8,0.35),new THREE.MeshLambertMaterial({color:0x0e0e0a}));termBtnHouse.position.set(0,1.1,0.36);termGrp.add(termBtnHouse);
        const termBtnMat=new THREE.MeshBasicMaterial({color:0xbb0000});
        const termBtn=new THREE.Mesh(new THREE.CylinderGeometry(0.24,0.24,0.18,16),termBtnMat);termBtn.rotation.x=Math.PI/2;termBtn.position.set(0,1.1,0.56);termGrp.add(termBtn);
        // Button label engraving
        const btnLabel=new THREE.Mesh(new THREE.BoxGeometry(0.5,0.12,0.02),new THREE.MeshLambertMaterial({color:0x888866}));btnLabel.position.set(0,0.65,0.45);termGrp.add(btnLabel);

        // LED indicator column
        const ledMat=new THREE.MeshBasicMaterial({color:0x880010});
        const led1=new THREE.Mesh(new THREE.SphereGeometry(0.1,8,6),ledMat);led1.position.set(1.3,1.8,0.5);termGrp.add(led1);
        const led2=new THREE.Mesh(new THREE.SphereGeometry(0.1,8,6),new THREE.MeshBasicMaterial({color:0x008800}));led2.position.set(1.3,2.2,0.5);termGrp.add(led2);
        const led3=new THREE.Mesh(new THREE.SphereGeometry(0.1,8,6),new THREE.MeshBasicMaterial({color:0x006688}));led3.position.set(1.3,2.6,0.5);termGrp.add(led3);

        // Cable run at bottom going into wall
        const cableMat=new THREE.MeshLambertMaterial({color:0x111110});
        const cable=new THREE.Mesh(new THREE.CylinderGeometry(0.12,0.12,1.5,8),cableMat);cable.position.set(0.4,0.1,0.3);cable.rotation.z=0.3;termGrp.add(cable);

        scene.add(termGrp);

        // ================================================================
        //  ORBS — bigger, animated fluid texture, pickup ring
        // ================================================================
        const orbs=[],SAFE=20;
        let oAt=0;
        while(orbs.length<TOTAL_ORBS&&oAt<2000){
            oAt++;const cell=emptyCells[Math.floor(Math.random()*emptyCells.length)];
            const pos=getPos(cell.x,cell.z);
            if(Math.hypot(pos.x-startPos.x,pos.z-startPos.z)<SAFE)continue;
            let near=false;for(const o of orbs)if(Math.hypot(pos.x-o.position.x,pos.z-o.position.z)<20){near=true;break;}
            if(!near){
                // Animated fluid sphere — uses shared orbTex updated each frame
                const orbMat=new THREE.MeshBasicMaterial({map:orbTex,transparent:true,opacity:0.95});
                const orb=new THREE.Mesh(new THREE.SphereGeometry(0.85,16,12),orbMat);
                orb.position.set(pos.x,2.2,pos.z);
                // Outer glow shell
                const glowMat=new THREE.MeshBasicMaterial({color:0x00ccff,transparent:true,opacity:0.18,depthWrite:false,side:THREE.BackSide});
                const glow=new THREE.Mesh(new THREE.SphereGeometry(1.3,10,8),glowMat);orb.add(glow);
                // Floor ring
                const rMat=new THREE.MeshBasicMaterial({color:0x00eeff,transparent:true,opacity:0.35,depthWrite:false});
                const ring=new THREE.Mesh(new THREE.RingGeometry(0.9,1.1,28),rMat);ring.rotation.x=-Math.PI/2;ring.position.y=-2.15;orb.add(ring);
                orb.userData.ringMat=rMat;orb.userData.glowMat=glowMat;
                const oL=new THREE.PointLight(0x00eeff,1.8,18);orb.add(oL);
                scene.add(orb);orbs.push(orb);
            }
        }

        // ================================================================
        //  PHANTOMS — multi-layer ominous appearance + advanced AI
        // ================================================================
        const enemies=[];
        function mkPhantom(ePos,eCell){
            const root=new THREE.Group();root.position.set(ePos.x,2.2,ePos.z);
            // Dark core
            const core=new THREE.Mesh(new THREE.SphereGeometry(0.85,14,10),new THREE.MeshBasicMaterial({color:0x110016,transparent:true,opacity:0.97}));root.add(core);
            // Mid wispy shell
            const mid=new THREE.Mesh(new THREE.SphereGeometry(1.25,10,7),new THREE.MeshBasicMaterial({color:0x2a0050,transparent:true,opacity:0.5,depthWrite:false}));root.add(mid);
            // Outer wisp
            const outer=new THREE.Mesh(new THREE.SphereGeometry(1.7,8,5),new THREE.MeshBasicMaterial({color:0x3a0060,transparent:true,opacity:0.2,depthWrite:false}));root.add(outer);
            // Eye-like inner glow — two dim reddish points
            const eyeL=new THREE.PointLight(0xff1100,0,0);eyeL.position.set(-0.3,0.2,0.6);root.add(eyeL);
            const eyeR=new THREE.PointLight(0xff1100,0,0);eyeR.position.set(0.3,0.2,0.6);root.add(eyeR);
            // Ambient glow light for environment
            const pL=new THREE.PointLight(0x660033,1.2,20);root.add(pL);
            root.userData={
                // Core AI state machine
                state:'patrol',
                alertTimer:0, huntTimer:0, searchTimer:0,
                pathQueue:[], pathUpdateT:0,
                targetPos:new THREE.Vector3(ePos.x,2.2,ePos.z),
                lastGrid:{x:eCell.x,z:eCell.z},
                lastKnownGrid:null,
                lastKnownPos:{x:ePos.x,z:ePos.z}, // world coords of last player sighting
                spawnGrid:{x:eCell.x,z:eCell.z},   // for returning to patrol area
                // Speed accumulates over time
                baseSpeed:PATROL_SPD, currentSpeed:PATROL_SPD,
                // Memory: ring buffer of recent player positions with timestamps
                playerMemory:[], // [{wx,wz,t}]
                // Predicted hunt position
                predictedPos:null,
                // Group coordination: true for 3s after being alerted by another phantom
                groupAlerted:false, groupTimer:0,
                // Eye glow refs
                eyeL, eyeR, light:pL,
                name:ENEMY_NAMES[enemies.length%ENEMY_NAMES.length],
                // Wobble phase for visual undulation
                wobbleSeed:Math.random()*100,
                // Alert visual state
                coreMesh:core, midMesh:mid, outerMesh:outer
            };
            scene.add(root); enemies.push(root); return root;
        }
        let eAt=0;
        while(enemies.length<8&&eAt<2000){
            eAt++;const eCell=emptyCells[Math.floor(Math.random()*emptyCells.length)];
            const ePos=getPos(eCell.x,eCell.z);
            if(Math.hypot(ePos.x-startPos.x,ePos.z-startPos.z)<40)continue;
            let near=false;for(const e of enemies)if(Math.hypot(ePos.x-e.position.x,ePos.z-e.position.z)<30){near=true;break;}
            if(!near)mkPhantom(ePos,eCell);
        }

        // ================================================================
        //  AI HELPERS
        // ================================================================
        function triggerAlert(e,fromGroup){
            const ud=e.userData;
            if(ud.state==='hunt'){ud.alertTimer=ALERT_DUR;return;}
            const wasPatrol=ud.state==='patrol';
            ud.state=fromGroup?'search':'hunt';
            if(!fromGroup){ud.huntTimer=HUNT_DUR;ud.alertTimer=ALERT_DUR;}
            else{ud.searchTimer=SEARCH_DUR;ud.groupAlerted=true;ud.groupTimer=3.0;}
            ud.pathQueue=[];ud.pathUpdateT=0;
            if(!fromGroup){
                ud.eyeL.distance=8;ud.eyeR.distance=8;
                ud.eyeL.intensity=3;ud.eyeR.intensity=3;
                playScreech();
                // Group coordination: partial-alert nearby phantoms
                enemies.forEach(e2=>{if(e2!==e&&e2.userData.state==='patrol'){const d=e.position.distanceTo(e2.position);if(d<55)triggerAlert(e2,true);}});
            }
        }

        function alertAllInRadius(wx,wz,r){enemies.forEach(e=>{if(Math.hypot(e.position.x-wx,e.position.z-wz)<r)triggerAlert(e,false);});}

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
            if(e.code==='KeyE'&&gameActive&&!gameWon&&doorState==='ready_terminal'){
                if(Math.hypot(camera.position.x-TERM_WX,camera.position.z-TERM_WZ)<9){
                    terminalActivated=true;terminalBtnT=0.18;
                    termBtn.position.z=0.44; // depress button
                    termScreenMat.color.setHex(0xff4400);termLight.color.setHex(0xff6600);termLight.intensity=4;
                    ledMat.color.setHex(0xff4400);playTerminalClick();
                    setTimeout(()=>{doorState='valves_pressure';initIndustrialAudio();sirens.forEach(s=>s.light.intensity=45);klaxonGain.gain.setTargetAtTime(0.015,audioCtx.currentTime,0.1);hissGain.gain.setTargetAtTime(0.1,audioCtx.currentTime,0.1);},700);
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

                // --- NEW: Bulletproof F Key Toggle ---
                if(keys['KeyF'] && !window.fKeyWasPressed) {
                    flashlightOn = !flashlightOn;
                    flash1.visible = flashlightOn;
                    flash2.visible = flashlightOn;
                    if(typeof playFlashlightClick === 'function') playFlashlightClick();
                    window.fKeyWasPressed = true;
                } else if (!keys['KeyF']) {
                    window.fKeyWasPressed = false;
                }

                if(isSprinting){player.stamina-=0.4;if(player.stamina<=0)player.isExhausted=true;}
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

// ---- SIMPLE LIGHT UPDATE (Keeping Fixture Visuals) ----
corridorLights.forEach(cl => {
    const now = performance.now();
    let targetI = 1.0;

    // Determine what the brightness SHOULD be
    if (cl.broken) {
        const t = now * 0.001 * cl.rate + cl.seed;
        const noise = Math.sin(t * 7.8) * Math.sin(t * 3.3) * Math.sin(t * 15.0);
        targetI = noise > 0.1 ? 1.0 : 0.05;
        if (Math.random() > 0.98) targetI = 0; // Total cutout
    } else {
        targetI = 0.9 + Math.sin(now * 0.005 + cl.seed) * 0.1; // Electrical hum
    }

    // SMOOTHING: Transition cl.currentI toward targetI
    if (cl.currentI === undefined) cl.currentI = 0;
    cl.currentI += (targetI - cl.currentI) * 0.25; 

    // 1. Update the Simple PointLight (The functioning room illumination)
    if (cl.light) cl.light.intensity = cl.base * cl.currentI;

    // 2. Update the Emissive Mesh (The actual ceiling fixture tube)
    if (cl.strip) cl.strip.emissiveIntensity = 2.5 * cl.currentI;
});
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
                    if(orbsCollected===TOTAL_ORBS&&doorState==='closed'){
                        doorState='ready_terminal';
                        termScreenMat.color.setHex(0x001400);termLight.color.setHex(0x00ff44);termLight.intensity=3.5;
                        ledMat.color.setHex(0x00cc22);termBtnMat.color.setHex(0x00bb00);
                        playUISound(280,0.7,0.7,'sine');
                    }
                }
            });
            orbs.forEach(orb=>{if(orb.position.y>0&&orb.userData.ringMat)orb.userData.ringMat.opacity=0.25+0.18*Math.sin(now*0.005+orb.position.x);});

            // Siren spin
            sirens.forEach((s,i)=>s.group.rotation.y+=delta*(i%2===0?2.2:-2.2));

            // Terminal proximity prompt
            if(gameActive&&!gameWon&&!terminalActivated){
                const dt=Math.hypot(camPos.x-TERM_WX,camPos.z-TERM_WZ);
                elPrompt.style.display=(doorState==='ready_terminal'&&dt<9)?'block':'none';
            }

            // ---- DOOR ANIMATION ----
            if(!gameWon)camera.rotation.z=0;
            if(doorState!=='closed'&&doorState!=='open'&&doorState!=='ready_terminal'){
                const dtd=camPos.distanceTo(doorGroup.position),vs=Math.max(0,1-dtd/55);
                if(klaxonGain)klaxonGain.gain.setTargetAtTime(vs*0.016,audioCtx.currentTime,0.1);
                if(!gameWon&&dtd<50){const si=(50-dtd)*0.0012;camera.rotation.z=(Math.random()-0.5)*si;}

                if(doorState==='valves_pressure'){
                    valves.forEach(v=>v.rotation.z+=delta*Math.PI*1.2);
                    if(Math.random()>0.55)emitSteam(doorGroup.position.x+(Math.random()-0.5)*4,0.5,doorGroup.position.z-1);
                    if(hissGain)hissGain.gain.setTargetAtTime(vs*0.12,audioCtx.currentTime,0.1);
                    // After valve full rotation, move to vault unlock
                    if(valves[0].rotation.z>Math.PI*5){
                        doorState='vault_unlock';
                        if(hissGain)hissGain.gain.setTargetAtTime(0,audioCtx.currentTime,0.1);
                        if(vaultGain)vaultGain.gain.setTargetAtTime(vs*0.045,audioCtx.currentTime,0.1);
                    }
                } else if(doorState==='vault_unlock'){
                    vaultWG.rotation.z+=delta*(Math.PI/4.5);
                    if(vaultGain)vaultGain.gain.setTargetAtTime(vs*0.045,audioCtx.currentTime,0.1);
                    if(vaultWG.rotation.z>Math.PI*1.5){
                        doorState='unlatching';matIndicator.color.setHex(0x00ff00);
                        if(vaultGain)vaultGain.gain.setTargetAtTime(0,audioCtx.currentTime,0.1);
                        if(latchGain)latchGain.gain.setTargetAtTime(vs*0.065,audioCtx.currentTime,0.1);
                    }
                } else if(doorState==='unlatching'){
                    // Slide all bolts back
                    const bs=delta*0.6;
                    deadboltsL.forEach(b=>{b.position.x-=bs*3.5;});
                    deadboltsR.forEach(b=>{b.position.x+=bs*3.5;});
                    if(latchGain)latchGain.gain.setTargetAtTime(vs*0.065,audioCtx.currentTime,0.1);
                    if(deadboltsL[0].position.x<-7){
                        doorState='retracting_pistons';
                        if(latchGain)latchGain.gain.setTargetAtTime(0,audioCtx.currentTime,0.1);
                        if(pistonGain)pistonGain.gain.setTargetAtTime(vs*0.18,audioCtx.currentTime,0.1);
                    }
                } else if(doorState==='retracting_pistons'){
                    pistonGrp.position.y+=delta*1.1;
                    if(pistonGain)pistonGain.gain.setTargetAtTime(vs*0.18,audioCtx.currentTime,0.1);
                    if(pistonGrp.position.y>5.5){
                        doorState='sliding';
                        if(pistonGain)pistonGain.gain.setTargetAtTime(0,audioCtx.currentTime,0.1);
                        if(gearGain)gearGain.gain.setTargetAtTime(vs*0.09,audioCtx.currentTime,0.1);
                    }
                } else if(doorState==='sliding'){
                    if(doorHL.position.x>-PW-2.5){
                        const sl=delta*0.52;doorHL.position.x-=sl;doorHR.position.x+=sl;
                        const gr=sl/GR;mgL.rotation.z-=gr;mgR.rotation.z+=gr;
                        const hr=GR/1.0;hgL.rotation.z+=gr*hr;hgR.rotation.z-=gr*hr;
                        if(Math.random()>0.42){emitSpark(doorGroup.position.x-3.5,FH/2+FH/2+GR,doorGroup.position.z-0.5);emitSpark(doorGroup.position.x+3.5,FH/2+FH/2+GR,doorGroup.position.z-0.5);}
                        if(gearGain)gearGain.gain.setTargetAtTime(vs*0.09,audioCtx.currentTime,0.1);
                    } else {
                        doorState='open';sirens.forEach(s=>s.light.intensity=0);
                        const fot=audioCtx.currentTime+1.5;
                        if(klaxonGain)klaxonGain.gain.linearRampToValueAtTime(0,fot);if(gearGain)gearGain.gain.linearRampToValueAtTime(0,fot);
                    }
                }
            }

            // ---- WIN ----
            if(doorState==='open'&&camPos.z>doorGroup.position.z+1.5&&!gameWon){
                gameWon=true;document.exitPointerLock();
                const ws=document.getElementById('win-screen'),fb=document.getElementById('fade-black');
                ws.style.display='flex';setTimeout(()=>{fb.style.opacity='1';ws.style.opacity='1';},50);
                document.getElementById('finalTime').innerText=`FINAL TIME: ${totalElapsed}s`;
                elPrompt.style.display='none';
                try{if(klaxonOsc)klaxonOsc.stop();if(latchOsc)latchOsc.stop();if(pistonOsc)pistonOsc.stop();if(gearOsc)gearOsc.stop();if(vaultOsc)vaultOsc.stop();if(hissSrc)hissSrc.stop();}catch(_){}
            }
        }

        function animate(){requestAnimationFrame(animate);update();renderer.render(scene,camera);}
        animate();

        window.addEventListener('resize',()=>{camera.aspect=innerWidth/innerHeight;camera.updateProjectionMatrix();renderer.setSize(innerWidth,innerHeight);});

        document.getElementById('reboot-btn').addEventListener('click',()=>{
            const d=document.getElementById('death-screen-ui');d.style.transition='opacity 0.5s';d.style.opacity='0';setTimeout(()=>location.reload(),500);
        });
