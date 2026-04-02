
        import * as THREE from 'three';

        // ============================================================
        //  MAZE GENERATION
        // ============================================================
        const MAZE_SIZE = 25; const TILE_SIZE = 12;
        const maze = Array(MAZE_SIZE).fill(null).map(() => Array(MAZE_SIZE).fill(1));
        const emptyCells = [];
        function carveMaze(x, y) {
            maze[x][y] = 0;
            const dirs = [[0,-1],[0,1],[-1,0],[1,0]].sort(() => Math.random()-0.5);
            for (const [dx,dy] of dirs) { const nx=x+dx*2,ny=y+dy*2; if(nx>0&&nx<MAZE_SIZE-1&&ny>0&&ny<MAZE_SIZE-1&&maze[nx][ny]===1){maze[x+dx][y+dy]=0;carveMaze(nx,ny);} }
        }
        carveMaze(1,1);
        for(let i=1;i<MAZE_SIZE-1;i++) for(let j=1;j<MAZE_SIZE-1;j++) if(maze[i][j]===1&&((maze[i-1][j]===0&&maze[i+1][j]===0)||(maze[i][j-1]===0&&maze[i][j+1]===0))&&Math.random()<0.25) maze[i][j]=0;
        const exitGridX=Math.floor(MAZE_SIZE/2),exitGridZ=MAZE_SIZE-1;
        for(let i=-1;i<=1;i++) for(let j=-3;j<=-1;j++) maze[exitGridX+i][exitGridZ+j]=0;
        maze[exitGridX][exitGridZ]=0;
        for(let i=0;i<MAZE_SIZE;i++) for(let j=0;j<MAZE_SIZE;j++) if(maze[i][j]===0) emptyCells.push({x:i,z:j});

        // ============================================================
        //  PATHFINDING UTILITIES
        // ============================================================
        function getPos(i,j){return{x:(i-Math.floor(MAZE_SIZE/2))*TILE_SIZE,z:(j-Math.floor(MAZE_SIZE/2))*TILE_SIZE};}
        function worldToGrid(wx,wz){const o=Math.floor(MAZE_SIZE/2);return{x:Math.max(0,Math.min(MAZE_SIZE-1,Math.round(wx/TILE_SIZE)+o)),z:Math.max(0,Math.min(MAZE_SIZE-1,Math.round(wz/TILE_SIZE)+o))};}
        function bfsPath(sx,sz,gx,gz){
            if(sx===gx&&sz===gz)return[];
            const q=[{x:sx,z:sz,path:[]}],vis=new Set([`${sx},${sz}`]);let it=0;
            while(q.length&&it++<3000){const{x,z,path}=q.shift();for(const[dx,dz]of[[0,-1],[0,1],[-1,0],[1,0]]){const nx=x+dx,nz=z+dz,k=`${nx},${nz}`;if(nx<0||nx>=MAZE_SIZE||nz<0||nz>=MAZE_SIZE||maze[nx][nz]!==0||vis.has(k))continue;const np=[...path,{x:nx,z:nz}];if(nx===gx&&nz===gz)return np;vis.add(k);q.push({x:nx,z:nz,path:np});}}
            return[];
        }
        function hasLineOfSight(ax,az,bx,bz){
            const g0=worldToGrid(ax,az),g1=worldToGrid(bx,bz),steps=Math.max(Math.abs(g1.x-g0.x),Math.abs(g1.z-g0.z));
            if(steps===0)return true;
            for(let i=1;i<steps;i++){const t=i/steps,cx=Math.round(g0.x+(g1.x-g0.x)*t),cz=Math.round(g0.z+(g1.z-g0.z)*t);if(cx>=0&&cx<MAZE_SIZE&&cz>=0&&cz<MAZE_SIZE&&maze[cx][cz]===1)return false;}
            return true;
        }

        // ============================================================
        //  ALERT CONSTANTS
        // ============================================================
        const ALERT_DURATION = 12.0;
        const LIGHT_DETECT_RANGE = 38;
        const FLASHLIGHT_CONE_COS = Math.cos(65 * Math.PI / 180);
        const SOUND_SPRINT_RADIUS = 28;
        const SOUND_ORB_RADIUS = 22;
        const ENEMY_NAMES = ['REVENANT','UNIT-07','SPECTER-X','THE HOLLOW','SHADE-03','REMNANT','ECHO-NULL','VOID-TRACE'];

        // ============================================================
        //  GAME STATE
        // ============================================================
        const totalOrbs = 12; let orbsCollected = 0; let gameActive = false; let gameWon = false;
      let startTime = 0; let accumulatedTime = 0; let totalElapsed = 0; let hasPlayedSting = false; let prevTime = performance.now();
        document.getElementById('totalOrbsUI').innerText = totalOrbs;

        let yaw = Math.PI; let pitch = 0; const SENSITIVITY = 0.002;
        let prevYaw = Math.PI; let leanAngle = 0; let doorShakeZ = 0;
        let currentlySprinting = false; let introPlayed = false;
        let sprintAlertCooldown = 0; let sprintBreathCounter = 0;
        let lastKnownPlayerPos = null; let lastKnownPlayerTime = 0;
        const footstepEchoPositions = []; // last 3 sprint step world positions
        const exploredCells = new Set();
        let ceilingDripTimer = 3 + Math.random() * 3;

        const MAX_STAMINA = 200;
        const player = {
            height: 2.1, radius: 0.8, walkSpeed: 0.22, runSpeed: 0.48,
            stamina: MAX_STAMINA, isExhausted: false,
            velocity: new THREE.Vector2(0,0), headBobTimer: 0, lastFootstepCycle: 0
        };
      const keys = {};

const nameInput = document.getElementById('name-input');
const radarCanvas = document.getElementById('radar'); const rCtx = radarCanvas.getContext('2d');
const rCenter = radarCanvas.width/2; const radarMaxDist = 120; const radarScale = (rCenter-10)/radarMaxDist;

        // ============================================================
        //  AUDIO ENGINE
        // ============================================================
        const audioCtx = new (window.AudioContext || window.webkitAudioContext)();
        let klaxonOsc,klaxonGain,vaultOsc,vaultGain,latchOsc,latchGain,pistonOsc,pistonGain,gearOsc,gearGain,hissSrc,hissGain;
        let ambientGainNode, proximityBreathGain, enemyGrowlGain, ambientStarted = false;

        function initIndustrialAudio(){
            if(audioCtx.state==='suspended')audioCtx.resume();
            klaxonOsc=audioCtx.createOscillator();klaxonOsc.type='triangle';klaxonOsc.frequency.value=450;
            const kLFO=audioCtx.createOscillator();kLFO.frequency.value=2;const kMod=audioCtx.createGain();kMod.gain.value=150;kLFO.connect(kMod);kMod.connect(klaxonOsc.frequency);kLFO.start();
            klaxonGain=audioCtx.createGain();klaxonGain.gain.value=0;klaxonOsc.connect(klaxonGain);klaxonGain.connect(audioCtx.destination);klaxonOsc.start();
            vaultOsc=audioCtx.createOscillator();vaultOsc.type='sawtooth';vaultOsc.frequency.value=180;vaultGain=audioCtx.createGain();vaultGain.gain.value=0;vaultOsc.connect(vaultGain);vaultGain.connect(audioCtx.destination);vaultOsc.start();
            latchOsc=audioCtx.createOscillator();latchOsc.type='sawtooth';latchOsc.frequency.value=90;latchGain=audioCtx.createGain();latchGain.gain.value=0;latchOsc.connect(latchGain);latchGain.connect(audioCtx.destination);latchOsc.start();
            pistonOsc=audioCtx.createOscillator();pistonOsc.type='square';pistonOsc.frequency.value=35;pistonGain=audioCtx.createGain();pistonGain.gain.value=0;
            const pf=audioCtx.createBiquadFilter();pf.type='lowpass';pf.frequency.value=150;pistonOsc.connect(pf);pf.connect(pistonGain);pistonGain.connect(audioCtx.destination);pistonOsc.start();
            gearOsc=audioCtx.createOscillator();gearOsc.type='square';gearOsc.frequency.value=18;gearGain=audioCtx.createGain();gearGain.gain.value=0;gearOsc.connect(gearGain);gearGain.connect(audioCtx.destination);gearOsc.start();
            const bSz=audioCtx.sampleRate*2;const nBuf=audioCtx.createBuffer(1,bSz,audioCtx.sampleRate);const out=nBuf.getChannelData(0);for(let i=0;i<bSz;i++)out[i]=Math.random()*2-1;
            hissSrc=audioCtx.createBufferSource();hissSrc.buffer=nBuf;hissSrc.loop=true;
            const hF=audioCtx.createBiquadFilter();hF.type='highpass';hF.frequency.value=1000;hissGain=audioCtx.createGain();hissGain.gain.value=0;
            hissSrc.connect(hF);hF.connect(hissGain);hissGain.connect(audioCtx.destination);hissSrc.start();
        }

        function startAmbientAudio(){
            if(ambientStarted)return; ambientStarted=true;
            if(audioCtx.state==='suspended')audioCtx.resume();
            ambientGainNode=audioCtx.createGain();ambientGainNode.gain.setValueAtTime(0,audioCtx.currentTime);
            [40.0,41.4,80.7].forEach(f=>{const o=audioCtx.createOscillator();o.type='sine';o.frequency.value=f;o.connect(ambientGainNode);o.start();});
            const sw=audioCtx.createOscillator();sw.frequency.value=0.07;const sg=audioCtx.createGain();sg.gain.value=0.007;sw.connect(sg);sg.connect(ambientGainNode.gain);sw.start();
            ambientGainNode.connect(audioCtx.destination);
            ambientGainNode.gain.linearRampToValueAtTime(0.045,audioCtx.currentTime+4);
            // proximity breath
            const bSz=audioCtx.sampleRate*2;const nBuf=audioCtx.createBuffer(1,bSz,audioCtx.sampleRate);const nd=nBuf.getChannelData(0);for(let i=0;i<bSz;i++)nd[i]=Math.random()*2-1;
            const nSrc=audioCtx.createBufferSource();nSrc.buffer=nBuf;nSrc.loop=true;
            const bp=audioCtx.createBiquadFilter();bp.type='bandpass';bp.frequency.value=260;bp.Q.value=4;
            const tr=audioCtx.createOscillator();tr.frequency.value=5.5;const tg=audioCtx.createGain();tg.gain.value=0;tr.connect(tg);
            proximityBreathGain=audioCtx.createGain();proximityBreathGain.gain.value=0;tg.connect(proximityBreathGain.gain);
            tr.start();nSrc.start();nSrc.connect(bp);bp.connect(proximityBreathGain);proximityBreathGain.connect(audioCtx.destination);
            // enemy growl: continuous low drone scaled by alerted enemy proximity
            const gBuf=audioCtx.createBuffer(1,bSz,audioCtx.sampleRate);const gd=gBuf.getChannelData(0);for(let i=0;i<bSz;i++)gd[i]=Math.random()*2-1;
            const gSrc=audioCtx.createBufferSource();gSrc.buffer=gBuf;gSrc.loop=true;
            const gF=audioCtx.createBiquadFilter();gF.type='lowpass';gF.frequency.value=120;
            const gLFO=audioCtx.createOscillator();gLFO.frequency.value=3.2;const gLG=audioCtx.createGain();gLG.gain.value=0;gLFO.connect(gLG);
            enemyGrowlGain=audioCtx.createGain();enemyGrowlGain.gain.value=0;gLG.connect(enemyGrowlGain.gain);
            gLFO.start();gSrc.start();gSrc.connect(gF);gF.connect(enemyGrowlGain);enemyGrowlGain.connect(audioCtx.destination);
        }

        function playFootstep(isSprint){
            if(!audioCtx||audioCtx.state==='suspended')return;
            const sz=Math.floor(audioCtx.sampleRate*0.045);const b=audioCtx.createBuffer(1,sz,audioCtx.sampleRate);const d=b.getChannelData(0);
            for(let i=0;i<sz;i++)d[i]=(Math.random()*2-1)*Math.pow(1-i/sz,5);
            const s=audioCtx.createBufferSource();s.buffer=b;
            const f=audioCtx.createBiquadFilter();f.type='lowpass';f.frequency.value=isSprint?750:460;
            const g=audioCtx.createGain();g.gain.value=isSprint?0.55:0.32;
            s.connect(f);f.connect(g);g.connect(audioCtx.destination);s.start();
        }
        function playSprintBreath(){
            if(!audioCtx||audioCtx.state==='suspended')return;
            const sz=Math.floor(audioCtx.sampleRate*0.065);const b=audioCtx.createBuffer(1,sz,audioCtx.sampleRate);const d=b.getChannelData(0);
            for(let i=0;i<sz;i++)d[i]=(Math.random()*2-1)*Math.pow(1-i/sz,2);
            const s=audioCtx.createBufferSource();s.buffer=b;
            const f=audioCtx.createBiquadFilter();f.type='bandpass';f.frequency.value=380;f.Q.value=1.5;
            const g=audioCtx.createGain();g.gain.value=0.22;s.connect(f);f.connect(g);g.connect(audioCtx.destination);s.start();
        }
        function playOrbCollect(){
            if(!audioCtx)return;
            [440,660,880].forEach((freq,i)=>{
                const o=audioCtx.createOscillator(),g=audioCtx.createGain();o.type='triangle';o.frequency.value=freq;
                const t=audioCtx.currentTime+i*0.09;g.gain.setValueAtTime(0,t);g.gain.linearRampToValueAtTime(0.28,t+0.01);g.gain.exponentialRampToValueAtTime(0.001,t+0.22);
                o.connect(g);g.connect(audioCtx.destination);o.start(t);o.stop(t+0.22);
            });
        }
        function playGoldOrbCollect(){
            if(!audioCtx)return;
            [330,495,660,880,1100].forEach((freq,i)=>{
                const o=audioCtx.createOscillator(),g=audioCtx.createGain();o.type='sine';o.frequency.value=freq;
                const t=audioCtx.currentTime+i*0.07;g.gain.setValueAtTime(0,t);g.gain.linearRampToValueAtTime(0.22,t+0.01);g.gain.exponentialRampToValueAtTime(0.001,t+0.3);
                o.connect(g);g.connect(audioCtx.destination);o.start(t);o.stop(t+0.3);
            });
        }
        function playOrbMilestone(isLast){
            if(!audioCtx)return;
            const freqs=isLast?[220,330,440,660,880]:[330,440,660];
            freqs.forEach((freq,i)=>{
                const o=audioCtx.createOscillator(),g=audioCtx.createGain();o.type='triangle';o.frequency.value=freq;
                const t=audioCtx.currentTime+i*0.13;g.gain.setValueAtTime(0,t);g.gain.linearRampToValueAtTime(0.3,t+0.02);g.gain.exponentialRampToValueAtTime(0.001,t+0.35);
                o.connect(g);g.connect(audioCtx.destination);o.start(t);o.stop(t+0.35);
            });
        }
        function playEnemyScreech(){
            if(!audioCtx)return;
            const o=audioCtx.createOscillator(),g=audioCtx.createGain();o.type='sawtooth';
            o.frequency.setValueAtTime(280,audioCtx.currentTime);o.frequency.exponentialRampToValueAtTime(60,audioCtx.currentTime+0.4);
            g.gain.setValueAtTime(0.18,audioCtx.currentTime);g.gain.exponentialRampToValueAtTime(0.001,audioCtx.currentTime+0.4);
            o.connect(g);g.connect(audioCtx.destination);o.start();o.stop(audioCtx.currentTime+0.4);
        }
        function playDrip(vol){
            if(!audioCtx||audioCtx.state==='suspended')return;
            const sz=Math.floor(audioCtx.sampleRate*0.03);const b=audioCtx.createBuffer(1,sz,audioCtx.sampleRate);const d=b.getChannelData(0);
            for(let i=0;i<sz;i++)d[i]=(Math.random()*2-1)*Math.pow(1-i/sz,8);
            const s=audioCtx.createBufferSource();s.buffer=b;
            const f=audioCtx.createBiquadFilter();f.type='highpass';f.frequency.value=1200+Math.random()*400;
            const g=audioCtx.createGain();g.gain.value=vol*0.4;s.connect(f);f.connect(g);g.connect(audioCtx.destination);s.start();
        }
        function playSting(){
            if(audioCtx.state==='suspended')audioCtx.resume();
            const o=audioCtx.createOscillator(),g=audioCtx.createGain();o.type='sawtooth';
            o.frequency.setValueAtTime(120,audioCtx.currentTime);o.frequency.exponentialRampToValueAtTime(30,audioCtx.currentTime+1);
            g.gain.setValueAtTime(0.2,audioCtx.currentTime);g.gain.exponentialRampToValueAtTime(0.01,audioCtx.currentTime+1);
            o.connect(g);g.connect(audioCtx.destination);o.start();o.stop(audioCtx.currentTime+1);
        }
        function playUISound(freq,vol,dur,type='triangle'){
            if(audioCtx.state==='suspended')audioCtx.resume();
            const o=audioCtx.createOscillator(),g=audioCtx.createGain();o.type=type;
            o.frequency.setValueAtTime(freq,audioCtx.currentTime);o.frequency.exponentialRampToValueAtTime(freq/2,audioCtx.currentTime+dur);
            g.gain.setValueAtTime(vol,audioCtx.currentTime);g.gain.exponentialRampToValueAtTime(0.001,audioCtx.currentTime+dur);
            o.connect(g);g.connect(audioCtx.destination);o.start();o.stop(audioCtx.currentTime+dur);
        }

        // ============================================================
        //  PROCEDURAL TEXTURES
        // ============================================================
        function createStoneBlockTexture(){
            const c=document.createElement('canvas');c.width=512;c.height=512;const ctx=c.getContext('2d');
            const bW=128,bH=64;ctx.fillStyle='#1b2d1b';ctx.fillRect(0,0,512,512);
            for(let row=0;row<8;row++){for(let col=-1;col<5;col++){
                const ox=(row%2===0)?0:bW/2,bx=col*bW+ox,by=row*bH,sh=Math.floor(Math.random()*16);
                ctx.fillStyle=`rgb(${24+sh},${44+sh},${24+sh})`;ctx.fillRect(bx+3,by+3,bW-6,bH-6);
                for(let i=0;i<70;i++){ctx.fillStyle=`rgba(0,0,0,${Math.random()*0.2})`;ctx.fillRect(bx+3+Math.random()*(bW-6),by+3+Math.random()*(bH-6),Math.random()*7+1,Math.random()*7+1);}
                if(Math.random()>0.55){const sx=bx+10+Math.random()*(bW-20);const gr=ctx.createLinearGradient(sx,by,sx+2,by+bH);gr.addColorStop(0,'rgba(90,42,8,0)');gr.addColorStop(0.3,'rgba(95,46,8,0.4)');gr.addColorStop(1,'rgba(70,32,5,0)');ctx.fillStyle=gr;ctx.fillRect(sx,by,4,bH);}
                ctx.fillStyle='rgba(255,255,255,0.03)';ctx.fillRect(bx+3,by+3,bW-6,3);
            }}
            ctx.strokeStyle='#091209';ctx.lineWidth=3;
            for(let r=0;r<=8;r++){ctx.beginPath();ctx.moveTo(0,r*bH);ctx.lineTo(512,r*bH);ctx.stroke();}
            for(let r=0;r<8;r++){const ox=(r%2===0)?0:bW/2;for(let col=-1;col<=5;col++){const bx=col*bW+ox;ctx.beginPath();ctx.moveTo(bx,r*bH);ctx.lineTo(bx,(r+1)*bH);ctx.stroke();}}
            const tex=new THREE.CanvasTexture(c);tex.wrapS=tex.wrapT=THREE.RepeatWrapping;tex.repeat.set(1,1.2);return tex;
        }
        function createFloorTexture(){
            const c=document.createElement('canvas');c.width=512;c.height=512;const ctx=c.getContext('2d');
            ctx.fillStyle='#161616';ctx.fillRect(0,0,512,512);const ps=128;
            for(let r=0;r<4;r++){for(let col=0;col<4;col++){
                const sh=Math.floor(Math.random()*14);ctx.fillStyle=`rgb(${26+sh},${26+sh},${28+sh})`;ctx.fillRect(col*ps+2,r*ps+2,ps-4,ps-4);
                [[col*ps+9,r*ps+9],[col*ps+ps-9,r*ps+9],[col*ps+9,r*ps+ps-9],[col*ps+ps-9,r*ps+ps-9]].forEach(([sx,sy])=>{
                    ctx.fillStyle='#272727';ctx.beginPath();ctx.arc(sx,sy,5.5,0,Math.PI*2);ctx.fill();
                    ctx.fillStyle='#0f0f0f';ctx.beginPath();ctx.arc(sx,sy,2.8,0,Math.PI*2);ctx.fill();
                    ctx.strokeStyle='#333';ctx.lineWidth=1.2;ctx.beginPath();ctx.moveTo(sx-3,sy);ctx.lineTo(sx+3,sy);ctx.stroke();ctx.beginPath();ctx.moveTo(sx,sy-3);ctx.lineTo(sx,sy+3);ctx.stroke();
                });
                for(let i=0;i<22;i++){ctx.fillStyle=`rgba(0,0,0,${Math.random()*0.13})`;ctx.fillRect(col*ps+Math.random()*ps,r*ps+Math.random()*ps,Math.random()*25+2,Math.random()*2+1);}
                ctx.fillStyle='rgba(255,255,255,0.025)';ctx.fillRect(col*ps+2,r*ps+2,ps-4,2);
            }}
            ctx.strokeStyle='#0d0d0d';ctx.lineWidth=3;
            for(let i=0;i<=4;i++){ctx.beginPath();ctx.moveTo(i*ps,0);ctx.lineTo(i*ps,512);ctx.stroke();ctx.beginPath();ctx.moveTo(0,i*ps);ctx.lineTo(512,i*ps);ctx.stroke();}
            const tex=new THREE.CanvasTexture(c);tex.wrapS=tex.wrapT=THREE.RepeatWrapping;tex.repeat.set(7,7);return tex;
        }
        function createGrimeTexture(){
            const c=document.createElement('canvas');c.width=512;c.height=512;const ctx=c.getContext('2d');
            ctx.fillStyle='#2a2a2a';ctx.fillRect(0,0,512,512);
            for(let i=0;i<10000;i++){ctx.fillStyle=Math.random()>0.5?'rgba(0,0,0,0.1)':'rgba(80,60,40,0.1)';ctx.beginPath();ctx.arc(Math.random()*512,Math.random()*512,Math.random()*4,0,Math.PI*2);ctx.fill();}
            const tex=new THREE.CanvasTexture(c);tex.wrapS=tex.wrapT=THREE.RepeatWrapping;tex.repeat.set(2,2);return tex;
        }
        function createHazardTexture(){
            const c=document.createElement('canvas');c.width=256;c.height=256;const ctx=c.getContext('2d');
            ctx.fillStyle='#d4af37';ctx.fillRect(0,0,256,256);ctx.fillStyle='#111';
            for(let i=-256;i<512;i+=64){ctx.beginPath();ctx.moveTo(i,0);ctx.lineTo(i+32,0);ctx.lineTo(i+288,256);ctx.lineTo(i+256,256);ctx.fill();}
            const tex=new THREE.CanvasTexture(c);tex.wrapS=tex.wrapT=THREE.RepeatWrapping;return tex;
        }

        // ============================================================
        //  SCENE + RENDERER + LIGHTS
        // ============================================================
        const scene=new THREE.Scene();scene.background=new THREE.Color(0x0c121a);scene.fog=new THREE.Fog(0x0c121a,15,120);
        const camera=new THREE.PerspectiveCamera(75,window.innerWidth/window.innerHeight,0.1,1000);camera.rotation.order='YXZ';
        const renderer=new THREE.WebGLRenderer({antialias:true});renderer.setSize(window.innerWidth,window.innerHeight);
        renderer.shadowMap.enabled=true;renderer.shadowMap.type=THREE.PCFSoftShadowMap;document.body.appendChild(renderer.domElement);
        const hemiLight=new THREE.HemisphereLight(0xffffff,0x444444,0.6);scene.add(hemiLight);
        const flashLight=new THREE.SpotLight(0xffffe6,50.0,500,Math.PI/5,0.6,1.0);
        flashLight.position.set(0,0,0);flashLight.castShadow=true;flashLight.shadow.bias=-0.001;
        camera.add(flashLight);camera.add(flashLight.target);flashLight.target.position.set(0,0,-1);scene.add(camera);

        // ============================================================
        //  MATERIALS
        // ============================================================
        const matDarkMetal=new THREE.MeshStandardMaterial({map:createGrimeTexture(),metalness:0.8,roughness:0.7});
        const matRustyFrame=new THREE.MeshStandardMaterial({color:0x3d352b,metalness:0.9,roughness:0.9});
        const matBrightSteel=new THREE.MeshStandardMaterial({color:0xaaaaaa,metalness:1.0,roughness:0.2});
        const matHazard=new THREE.MeshStandardMaterial({map:createHazardTexture(),metalness:0.3,roughness:0.8});
        const matWarningYellow=new THREE.MeshStandardMaterial({color:0xffaa00,metalness:0.4,roughness:0.7});
        const matBlackHole=new THREE.MeshStandardMaterial({color:0x030303,roughness:1.0});
        const matGlassRed=new THREE.MeshStandardMaterial({color:0xff0000,emissive:0x550000,transparent:true,opacity:0.8});
        const matIndicator=new THREE.MeshBasicMaterial({color:0xff0000});
        const matPipe=new THREE.MeshStandardMaterial({color:0x4a3828,metalness:0.8,roughness:0.5});

        // ============================================================
        //  PARTICLES
        // ============================================================
        const particles=[];
        const sparkGeo=new THREE.BoxGeometry(0.1,0.1,0.1);const sparkMat=new THREE.MeshBasicMaterial({color:0xffaa00});
        const steamGeo=new THREE.PlaneGeometry(1.5,1.5);const steamMat=new THREE.MeshBasicMaterial({color:0xdddddd,transparent:true,opacity:0.5,depthWrite:false});
        function emitSpark(x,y,z){const s=new THREE.Mesh(sparkGeo,sparkMat);s.position.set(x,y,z);s.userData={vel:new THREE.Vector3((Math.random()-0.5)*5,Math.random()*5+2,(Math.random()-0.5)*5),life:1.0,type:'spark'};scene.add(s);particles.push(s);}
        function emitSteam(x,y,z){const s=new THREE.Mesh(steamGeo,steamMat.clone());s.position.set(x,y,z);s.userData={vel:new THREE.Vector3((Math.random()-0.5)*2,Math.random()*3+1,(Math.random()-0.5)*2),life:1.0,type:'steam',mat:s.material};scene.add(s);particles.push(s);}
        function emitAfterimage(x,y,z){
            const mat=new THREE.MeshBasicMaterial({color:0xff1100,transparent:true,opacity:0.3,depthWrite:false});
            const m=new THREE.Mesh(new THREE.SphereGeometry(1.2,8,8),mat);m.position.set(x,y,z);
            m.userData={life:0.55,type:'afterimage',mat};scene.add(m);particles.push(m);
        }

        // ============================================================
        //  LEVEL BUILDING
        // ============================================================
        const solidDoorParts=[];const partBoxHelper=new THREE.Box3();
        function registerSolid(m){solidDoorParts.push(m);}
        function createGearMesh(radius,depth,teethCount){
            const g=new THREE.Group();
            const core=new THREE.Mesh(new THREE.CylinderGeometry(radius*0.85,radius*0.85,depth,16),matBrightSteel);core.rotation.x=Math.PI/2;core.castShadow=true;g.add(core);
            const tGeo=new THREE.BoxGeometry((Math.PI*radius*2)/(teethCount*2),radius*0.25,depth);
            for(let i=0;i<teethCount;i++){const a=(i/teethCount)*Math.PI*2;const t=new THREE.Mesh(tGeo,matBrightSteel);t.position.set(Math.cos(a)*radius*0.95,Math.sin(a)*radius*0.95,0);t.rotation.z=a+Math.PI/2;t.castShadow=true;g.add(t);}
            const ax=new THREE.Mesh(new THREE.CylinderGeometry(radius*0.3,radius*0.3,depth+0.2,12),matDarkMetal);ax.rotation.x=Math.PI/2;g.add(ax);
            const hb=new THREE.Mesh(new THREE.BoxGeometry(radius*2,radius*2,depth),new THREE.MeshBasicMaterial({visible:false}));g.add(hb);registerSolid(hb);return g;
        }

        // Floor
        const floor=new THREE.Mesh(new THREE.PlaneGeometry(MAZE_SIZE*TILE_SIZE,MAZE_SIZE*TILE_SIZE),new THREE.MeshStandardMaterial({map:createFloorTexture(),roughness:0.85,metalness:0.4}));
        floor.rotation.x=-Math.PI/2;floor.receiveShadow=true;scene.add(floor);

        // Ceiling
        const ceiling=new THREE.Mesh(new THREE.PlaneGeometry(MAZE_SIZE*TILE_SIZE,MAZE_SIZE*TILE_SIZE),new THREE.MeshStandardMaterial({map:createStoneBlockTexture(),roughness:1.0,metalness:0.0}));
        ceiling.rotation.x=Math.PI/2;ceiling.position.y=14;scene.add(ceiling);

        // Walls
        const wallGeo=new THREE.BoxGeometry(TILE_SIZE,14,TILE_SIZE);
        const wallMat=new THREE.MeshStandardMaterial({map:createStoneBlockTexture(),roughness:0.85,metalness:0.1});
        for(let i=0;i<MAZE_SIZE;i++) for(let j=0;j<MAZE_SIZE;j++) if(maze[i][j]===1){const w=new THREE.Mesh(wallGeo,wallMat);const p=getPos(i,j);w.position.set(p.x,7,p.z);w.castShadow=true;w.receiveShadow=true;scene.add(w);}

        // Wall pipes — horizontal cylinders on corridor-facing wall faces
        const pipeGeo=new THREE.CylinderGeometry(0.18,0.18,TILE_SIZE*0.65,8);
        const pipeSet=new Set();let pipeCount=0;
        for(const cell of emptyCells){
            if(pipeCount>=28)break;
            const key=`${cell.x},${cell.z}`;if(pipeSet.has(key))continue;
            [[0,-1],[0,1],[-1,0],[1,0]].forEach(([dx,dz])=>{
                const wx=cell.x+dx,wz=cell.z+dz;
                if(wx>=0&&wx<MAZE_SIZE&&wz>=0&&wz<MAZE_SIZE&&maze[wx][wz]===1&&Math.random()>0.65){
                    const pos=getPos(cell.x,cell.z);
                    const pipe=new THREE.Mesh(pipeGeo,matPipe);
                    const wallOff=TILE_SIZE/2-0.25;
                    pipe.position.set(pos.x+dx*wallOff,2+Math.random()*7,pos.z+dz*wallOff);
                    if(dx!==0) pipe.rotation.x=Math.PI/2; else pipe.rotation.z=Math.PI/2;
                    scene.add(pipe);pipeCount++;
                }
            });
            pipeSet.add(key);
        }

        // Landmark props — unique stationary objects at intersections for orientation
        let landmarkCount=0;
        for(const cell of emptyCells){
            if(landmarkCount>=4)break;
            const pos=getPos(cell.x,cell.z);
            if(Math.hypot(pos.x-getPos(1,1).x,pos.z-getPos(1,1).z)<25)continue;
            if(Math.random()>0.97){
                const lg=new THREE.Group();
                const base=new THREE.Mesh(new THREE.BoxGeometry(3,0.8,3),matDarkMetal);lg.add(base);
                const col=new THREE.Mesh(new THREE.BoxGeometry(0.8,5,0.8),matRustyFrame);col.position.y=2.9;lg.add(col);
                const gear=createGearMesh(0.9,0.3,8);gear.position.set(0.4,5.2,0);gear.rotation.z=0.35;lg.add(gear);
                const lgt=new THREE.PointLight(0xffaa00,0.6,10);lgt.position.set(0,4,0);lg.add(lgt);
                lg.position.set(pos.x,0.4,pos.z);scene.add(lg);landmarkCount++;
            }
        }

        // Corridor flickering lights
        const corridorLights=[];
        let clCount=0;
        for(const cell of emptyCells){
            if(clCount>=8)break;
            const pos=getPos(cell.x,cell.z);
            if(Math.hypot(pos.x-getPos(1,1).x,pos.z-getPos(1,1).z)<15)continue;
            if(Math.random()>0.96){
                const cl=new THREE.PointLight(0xffd090,1.0,20);cl.position.set(pos.x,10,pos.z);scene.add(cl);
                corridorLights.push({light:cl,seed:Math.random()*100,base:0.4+Math.random()*0.8});clCount++;
            }
        }

        // Start position
        const startPos=getPos(1,1);camera.position.set(startPos.x,player.height,startPos.z);camera.rotation.set(0,yaw,0);

        // Drip sources — 5 random empty cells used for ambient drip sounds
        const dripSources=[];
        for(let i=0;i<5;i++){
            const cell=emptyCells[Math.floor(Math.random()*emptyCells.length)];
            const pos=getPos(cell.x,cell.z);
            dripSources.push({wx:pos.x,wz:pos.z,timer:Math.random()*6,interval:3+Math.random()*5});
        }

        // ============================================================
        //  TITAN DOOR
        // ============================================================
        let doorState='closed';const doorStartWorldPos=getPos(exitGridX,exitGridZ);
        const doorGroup=new THREE.Group();doorGroup.position.set(doorStartWorldPos.x,0,doorStartWorldPos.z);
        const frameHeight=16,frameZ=-1.5,doorZPos=0.5,panelWidth=5.0;
        const lintel=new THREE.Mesh(new THREE.BoxGeometry(16,4,2),matRustyFrame);lintel.position.set(0,frameHeight-2,frameZ);lintel.castShadow=true;doorGroup.add(lintel);registerSolid(lintel);
        const leftPillar=new THREE.Mesh(new THREE.BoxGeometry(4,frameHeight,2),matRustyFrame);leftPillar.position.set(-6,frameHeight/2,frameZ);leftPillar.castShadow=true;doorGroup.add(leftPillar);registerSolid(leftPillar);
        const rightPillar=new THREE.Mesh(new THREE.BoxGeometry(4,frameHeight,2),matRustyFrame);rightPillar.position.set(6,frameHeight/2,frameZ);rightPillar.castShadow=true;doorGroup.add(rightPillar);registerSolid(rightPillar);
        const sirens=[];
        const createSiren=(x,z)=>{const sg=new THREE.Group();sg.position.set(x,frameHeight-4,z);const bulb=new THREE.Mesh(new THREE.CylinderGeometry(0.5,0.5,1,16),matGlassRed);sg.add(bulb);const sp=new THREE.SpotLight(0xff0000,0,40,Math.PI/6,0.5,1);sp.position.set(0,0,0);sp.target.position.set(0,-10,10);sp.castShadow=true;sp.shadow.mapSize.width=512;sp.shadow.mapSize.height=512;sp.shadow.camera.near=1;sp.shadow.camera.far=40;sp.shadow.bias=-0.001;sg.add(sp);sg.add(sp.target);doorGroup.add(sg);sirens.push({group:sg,light:sp});};
        createSiren(-6,frameZ-1);createSiren(6,frameZ-1);createSiren(-6,frameZ+1);createSiren(6,frameZ+1);
        const indL=new THREE.Mesh(new THREE.BoxGeometry(0.2,6,0.2),matIndicator);indL.position.set(-4.1,7,frameZ);doorGroup.add(indL);
        const indR=new THREE.Mesh(new THREE.BoxGeometry(0.2,6,0.2),matIndicator);indR.position.set(4.1,7,frameZ);doorGroup.add(indR);
        const doorHalfLeftGroup=new THREE.Group();doorHalfLeftGroup.position.set(-panelWidth/2,7,doorZPos);
        const doorHalfRightGroup=new THREE.Group();doorHalfRightGroup.position.set(panelWidth/2,7,doorZPos);
        doorGroup.add(doorHalfLeftGroup,doorHalfRightGroup);
        const panelGeo=new THREE.BoxGeometry(panelWidth,14,1.0);
        const panelLeft=new THREE.Mesh(panelGeo,matDarkMetal);panelLeft.castShadow=true;
        const panelRight=new THREE.Mesh(panelGeo,matDarkMetal);panelRight.castShadow=true;
        doorHalfLeftGroup.add(panelLeft);doorHalfRightGroup.add(panelRight);registerSolid(panelLeft);registerSolid(panelRight);
        const deadboltsLeft=[],deadboltsRight=[];
        const boltGeo=new THREE.CylinderGeometry(0.3,0.3,3,16);boltGeo.rotateZ(Math.PI/2);
        for(const y of[-3,-1,1,3]){const bL=new THREE.Mesh(boltGeo,matBrightSteel);bL.position.set(1.5,y,0);doorHalfLeftGroup.add(bL);deadboltsLeft.push(bL);const bR=new THREE.Mesh(boltGeo,matBrightSteel);bR.position.set(-1.5,y,0);doorHalfRightGroup.add(bR);deadboltsRight.push(bR);}
        const vaultWheelGroup=new THREE.Group();vaultWheelGroup.position.set(panelWidth/2,0,-0.7);doorHalfLeftGroup.add(vaultWheelGroup);
        const vaultCore=createGearMesh(2.5,0.8,16);vaultWheelGroup.add(vaultCore);
        const vaultSocket=new THREE.Mesh(new THREE.CylinderGeometry(2.6,2.6,0.2,16),matBlackHole);vaultSocket.rotation.x=Math.PI/2;vaultSocket.position.set(-panelWidth/2,0,-0.6);doorHalfRightGroup.add(vaultSocket);
        const valves=[];
        for(const py of[-3,3]){const v=new THREE.Mesh(new THREE.TorusGeometry(0.6,0.15,8,16),matWarningYellow);v.position.set(-1.0,py,-0.7);doorHalfRightGroup.add(v);valves.push(v);}
        const latchGeo=new THREE.BoxGeometry(2,1.5,1.5);
        const latchL=new THREE.Mesh(latchGeo,matHazard);latchL.position.set(-4.5,7,-0.6);latchL.castShadow=true;doorGroup.add(latchL);registerSolid(latchL);
        const latchR=new THREE.Mesh(latchGeo,matHazard);latchR.position.set(4.5,7,-0.6);latchR.castShadow=true;doorGroup.add(latchR);registerSolid(latchR);
        const rackGeo=new THREE.BoxGeometry(panelWidth-0.5,0.8,0.5);
        const rackL=new THREE.Mesh(rackGeo,matBrightSteel);rackL.position.set(0,4,-0.8);doorHalfLeftGroup.add(rackL);
        const rackR=new THREE.Mesh(rackGeo,matBrightSteel);rackR.position.set(0,4,-0.8);doorHalfRightGroup.add(rackR);
        const gearRadius=1.6;
        const mainGearLeft=createGearMesh(gearRadius,0.6,12);mainGearLeft.position.set(-3,11+gearRadius,-0.8);doorGroup.add(mainGearLeft);
        const mainGearRight=createGearMesh(gearRadius,0.6,12);mainGearRight.position.set(3,11+gearRadius,-0.8);doorGroup.add(mainGearRight);
        const helperGearRadius=0.8;
        const helperGearLeft=createGearMesh(helperGearRadius,0.6,6);helperGearLeft.position.set(-3-gearRadius-helperGearRadius+0.2,11+gearRadius+1,-0.8);doorGroup.add(helperGearLeft);
        const helperGearRight=createGearMesh(helperGearRadius,0.6,6);helperGearRight.position.set(3+gearRadius+helperGearRadius-0.2,11+gearRadius+1,-0.8);doorGroup.add(helperGearRight);
        const pistonGroup=new THREE.Group();doorGroup.add(pistonGroup);const pistonGeo=new THREE.BoxGeometry(1.5,6,1.5);
        const pistonL=new THREE.Mesh(pistonGeo,matHazard);pistonL.position.set(-3.5,7,-0.8);pistonL.castShadow=true;pistonGroup.add(pistonL);registerSolid(pistonL);
        const pistonR=new THREE.Mesh(pistonGeo,matHazard);pistonR.position.set(3.5,7,-0.8);pistonR.castShadow=true;pistonGroup.add(pistonR);registerSolid(pistonR);
        scene.add(doorGroup);

        // ============================================================
        //  ORBS
        // ============================================================
        const orbs=[]; const SAFE_ZONE=20;
        const orbRingGeo=new THREE.RingGeometry(0.7,0.85,28);
        const orbRingMat=new THREE.MeshBasicMaterial({color:0x00eeff,side:THREE.DoubleSide,transparent:true,opacity:0.35,depthWrite:false});
        let orbAttempts=0;
        while(orbs.length<totalOrbs&&orbAttempts<2000){
            orbAttempts++;const cell=emptyCells[Math.floor(Math.random()*emptyCells.length)];const pos=getPos(cell.x,cell.z);
            if(Math.hypot(pos.x-startPos.x,pos.z-startPos.z)<SAFE_ZONE)continue;
            let tooClose=false;for(const o of orbs)if(Math.hypot(pos.x-o.position.x,pos.z-o.position.z)<20){tooClose=true;break;}
            if(!tooClose){
                const orbMesh=new THREE.Mesh(new THREE.SphereGeometry(0.5,16,16),new THREE.MeshStandardMaterial({color:0x00eeff,emissive:new THREE.Color(0x00eeff),emissiveIntensity:0.9,roughness:0.15,metalness:0.6}));
                orbMesh.position.set(pos.x,1.5,pos.z);
                const ring=new THREE.Mesh(orbRingGeo,orbRingMat.clone());ring.rotation.x=-Math.PI/2;ring.position.y=0.05;orbMesh.add(ring);
                orbMesh.userData.ring=ring;orbMesh.userData.ringMat=ring.material;orbMesh.userData.isGold=false;
                const oLight=new THREE.PointLight(0x00eeff,1.5,12);orbMesh.add(oLight);orbMesh.userData.light=oLight;
                scene.add(orbMesh);orbs.push(orbMesh);
            }
        }
        // Designate 3 random orbs as gold (stamina restore)
        const goldSet=new Set();while(goldSet.size<Math.min(3,orbs.length))goldSet.add(Math.floor(Math.random()*orbs.length));
        goldSet.forEach(idx=>{
            orbs[idx].material.color.setHex(0xffaa00);orbs[idx].material.emissive.setHex(0xffaa00);
            orbs[idx].userData.light.color.setHex(0xffaa00);orbs[idx].userData.ringMat.color.setHex(0xffaa00);
            orbs[idx].userData.isGold=true;
        });

        // ============================================================
        //  ENEMIES
        // ============================================================
        const ghostGeo=new THREE.SphereGeometry(1.2,20,20);
        const ghostMat=new THREE.MeshBasicMaterial({color:0xff0000,transparent:true,opacity:0.7});
        const auraGeo=new THREE.SphereGeometry(1.9,12,12);
        const enemies=[];let enemyAttempts=0;
        while(enemies.length<8&&enemyAttempts<2000){
            enemyAttempts++;const eCell=emptyCells[Math.floor(Math.random()*emptyCells.length)];const ePos=getPos(eCell.x,eCell.z);
            if(Math.hypot(ePos.x-startPos.x,ePos.z-startPos.z)<40)continue;
            let tooClose=false;for(const e of enemies)if(Math.hypot(ePos.x-e.position.x,ePos.z-e.position.z)<30){tooClose=true;break;}
            if(!tooClose){
                const enemy=new THREE.Mesh(ghostGeo,ghostMat.clone());enemy.position.set(ePos.x,2.0,ePos.z);
                const auraMat=new THREE.MeshBasicMaterial({color:0xff1100,transparent:true,opacity:0.12,depthWrite:false});
                const aura=new THREE.Mesh(auraGeo,auraMat);enemy.add(aura);
                const pLight=new THREE.PointLight(0xff0000,2,20);enemy.add(pLight);
                enemy.userData={
                    state:'patrol', alertTimer:0, pathQueue:[], pathUpdateTimer:0,
                    targetPos:new THREE.Vector3(ePos.x,2.0,ePos.z),
                    lastGrid:{x:eCell.x,z:eCell.z}, lastKnownPlayerGrid:null,
                    patrolSpeed:0.12, alertSpeed:0.22, searchSpeed:0.07,
                    afterimageTimer:0, facingAngle:0,
                    auraMat, light:pLight,
                    name:ENEMY_NAMES[enemies.length%ENEMY_NAMES.length]
                };
                scene.add(enemy);enemies.push(enemy);
            }
        }

        // ============================================================
        //  ALERT SYSTEM
        // ============================================================
        function triggerAlert(enemy){
            const ud=enemy.userData;
            if(ud.state==='alerted'){ud.alertTimer=ALERT_DURATION;return;}
            ud.state='alerted';ud.alertTimer=ALERT_DURATION;ud.pathUpdateTimer=0;
            ud.light.intensity=8;
            playEnemyScreech();
            lastKnownPlayerPos={wx:camera.position.x,wz:camera.position.z};
            lastKnownPlayerTime=performance.now();
        }
        function alertEnemiesInRadius(wx,wz,radius){
            enemies.forEach(e=>{if(Math.hypot(e.position.x-wx,e.position.z-wz)<radius&&e.userData.state!=='alerted')triggerAlert(e);});
        }
        function spawnEnemy(wx,wz){
            const enemy=new THREE.Mesh(ghostGeo,ghostMat.clone());enemy.position.set(wx,2.0,wz);
            const auraMat=new THREE.MeshBasicMaterial({color:0xff1100,transparent:true,opacity:0.12,depthWrite:false});
            enemy.add(new THREE.Mesh(auraGeo,auraMat));
            const pLight=new THREE.PointLight(0xff0000,8,20);enemy.add(pLight);
            const eg=worldToGrid(wx,wz);
            enemy.userData={
                state:'alerted',alertTimer:ALERT_DURATION,pathQueue:[],pathUpdateTimer:0,
                targetPos:new THREE.Vector3(wx,2.0,wz),
                lastGrid:eg,lastKnownPlayerGrid:worldToGrid(camera.position.x,camera.position.z),
                patrolSpeed:0.12+orbsCollected*0.007,alertSpeed:0.24,searchSpeed:0.08,
                afterimageTimer:0,facingAngle:0,auraMat,light:pLight,
                name:ENEMY_NAMES[Math.floor(Math.random()*ENEMY_NAMES.length)]
            };
            scene.add(enemy);enemies.push(enemy);
            playEnemyScreech();
        }

        // ============================================================
        //  INPUT + MENU
        // ============================================================
        const uiContainer=document.getElementById('main-ui');
        const engageBtn=document.getElementById('engage-btn');
        const nameInput=document.getElementById('name-input');
        const bgText=document.getElementById('input-bg-text');
        const quotes=["The corridors are wide, but the paths are many.","Do not trust the geometry.","Cyan light is a guide, but also a trap.","They only hunt what moves in the light.","The gold ones remember you."];
        document.getElementById('lore-text').innerText=`"${quotes[Math.floor(Math.random()*quotes.length)]}"`;
        nameInput.addEventListener('focus',()=>{if(nameInput.value===''){bgText.innerHTML='<div class="dots"><span>.</span><span>.</span><span>.</span></div>';bgText.style.opacity='1';}});
        nameInput.addEventListener('blur',()=>{if(nameInput.value===''){bgText.innerHTML='NAMETAG';bgText.style.opacity='1';}});
        nameInput.addEventListener('input',e=>{playUISound(90,1.2,0.25,'triangle');e.target.value=e.target.value.replace(/[^A-Za-z]/g,'').toUpperCase();if(nameInput.value.length>0)bgText.style.opacity='0';else{bgText.style.opacity='1';bgText.innerHTML='<div class="dots"><span>.</span><span>.</span><span>.</span></div>';}});
        nameInput.addEventListener('keydown',e=>e.stopPropagation());nameInput.addEventListener('keyup',e=>e.stopPropagation());
        document.querySelectorAll('#main-ui button,#main-ui input').forEach(el=>{
            el.addEventListener('mouseenter',()=>playUISound(500,0.5,0.08,'triangle'));
            if(el!==engageBtn)el.addEventListener('mousedown',()=>playUISound(180,1.5,0.2,'sine'));
            else el.addEventListener('mousedown',()=>playUISound(100,2.0,0.4,'sine'));
        });
        engageBtn.addEventListener('mousedown',()=>{const g=document.querySelector('.grid-container');g.classList.remove('shake-active');void g.offsetWidth;g.classList.add('shake-active');document.body.requestPointerLock();});
        document.addEventListener('pointerlockchange',()=>{
            if(document.pointerLockElement===document.body){
                uiContainer.style.display='none';gameActive=true;
                if(startTime===0)startTime=Date.now();
                prevTime=performance.now();
                startAmbientAudio();
                if(!introPlayed){
                    introPlayed=true;
                    const name=nameInput.value||'OPERATIVE';const fb=document.getElementById('fade-black');
                    fb.style.cssText='opacity:1;transition:none;display:flex;align-items:center;justify-content:center;';
                    fb.innerHTML=`<div style="text-align:center;font-family:'Courier New';letter-spacing:3px;"><div style="color:#d4af37;font-size:1.8em;margin-bottom:12px;">OPERATIVE: ${name}</div><div style="color:#5e4835;font-size:0.9em;">DEPLOYED</div></div>`;
                    setTimeout(()=>{fb.style.transition='opacity 1.5s ease-in-out';fb.style.opacity='0';setTimeout(()=>{fb.innerHTML='';fb.style.transition='opacity 3s ease-in-out';},1600);},1200);
                }
            } else if(!gameWon){
                uiContainer.style.display='flex';document.getElementById('main-title').innerText='SYSTEM PAUSED';engageBtn.innerText='RESUME';
                gameActive=false;accumulatedTime+=(Date.now()-startTime)/1000;
                document.getElementById('menuOrbCount').innerText=orbsCollected;
            }
        });
        document.addEventListener('mousemove',e=>{if(document.pointerLockElement===document.body){yaw-=e.movementX*SENSITIVITY;pitch-=e.movementY*SENSITIVITY;pitch=Math.max(-Math.PI/2,Math.min(Math.PI/2,pitch));}});
        document.addEventListener('keydown',e=>keys[e.code]=true);document.addEventListener('keyup',e=>keys[e.code]=false);

        // ============================================================
        //  COLLISION
        // ============================================================
        function isWall(x,z,radius){
            const offset=Math.floor(MAZE_SIZE/2);
            const minX=Math.floor((x-radius+TILE_SIZE/2)/TILE_SIZE)+offset-1,maxX=Math.floor((x+radius+TILE_SIZE/2)/TILE_SIZE)+offset+1;
            const minZ=Math.floor((z-radius+TILE_SIZE/2)/TILE_SIZE)+offset-1,maxZ=Math.floor((z+radius+TILE_SIZE/2)/TILE_SIZE)+offset+1;
            for(let i=minX;i<=maxX;i++)for(let j=minZ;j<=maxZ;j++){
                if(i>=0&&i<MAZE_SIZE&&j>=0&&j<MAZE_SIZE&&maze[i][j]===1){
                    const wcx=(i-offset)*TILE_SIZE,wcz=(j-offset)*TILE_SIZE;
                    const cx=Math.max(wcx-TILE_SIZE/2,Math.min(x,wcx+TILE_SIZE/2));const cz=Math.max(wcz-TILE_SIZE/2,Math.min(z,wcz+TILE_SIZE/2));
                    if(((x-cx)*(x-cx)+(z-cz)*(z-cz))<(radius*radius))return true;
                }
            }
            if(Math.abs(x-doorGroup.position.x)<TILE_SIZE&&Math.abs(z-doorGroup.position.z)<TILE_SIZE){
                const pb=new THREE.Box3(new THREE.Vector3(x-radius,0,z-radius),new THREE.Vector3(x+radius,player.height,z+radius));
                for(let i=0;i<solidDoorParts.length;i++){partBoxHelper.setFromObject(solidDoorParts[i]);if(pb.intersectsBox(partBoxHelper))return true;}
            }
            return false;
        }

        // ============================================================
        //  RECORDS (LOCALSTORAGE)
        // ============================================================
        function formatTime(s){const f=parseFloat(s),m=Math.floor(f/60),sc=Math.floor(f%60),ms=Math.round((f%1)*10);return`${String(m).padStart(2,'0')}:${String(sc).padStart(2,'0')}.${ms}`;}
        function saveRecord(name,time,orbs,outcome){
            const records=JSON.parse(localStorage.getItem('vigil_records')||'[]');
            records.unshift({name:name||'UNKNOWN',time,orbs,outcome,date:Date.now()});
            if(records.length>10)records.length=10;
            localStorage.setItem('vigil_records',JSON.stringify(records));
            const runs=parseInt(localStorage.getItem('vigil_runs')||'0')+1;
            localStorage.setItem('vigil_runs',runs);
            const best=localStorage.getItem('vigil_best');
            if(outcome==='ESCAPED'&&(!best||parseFloat(time)<parseFloat(best)))localStorage.setItem('vigil_best',time);
        }
        function loadRecords(){
            const records=JSON.parse(localStorage.getItem('vigil_records')||'[]');
            const arch=document.getElementById('archives-list');
            if(!records.length){arch.innerHTML='<div style="color:#3e2e21;text-align:center;margin-top:45px;font-weight:bold;font-size:0.8em;">NO ARCHIVES FOUND</div>';return;}
            arch.innerHTML=records.map(r=>`<div style="margin-bottom:8px;border-bottom:1px solid #3e2e21;padding-bottom:6px;font-size:0.8em;"><span style="color:#d4af37">${r.name}</span><span style="float:right;color:${r.outcome==='ESCAPED'?'#77ff77':'#ff5555'}">${r.outcome}</span><br><span style="color:#8b6b4a">${formatTime(r.time)} // ${r.orbs}/${totalOrbs} ORBS</span></div>`).join('');
            const best=localStorage.getItem('vigil_best');const runs=localStorage.getItem('vigil_runs')||'0';
            document.getElementById('bestTime').innerText=best?formatTime(best):'--:--';
            document.getElementById('tryCount').innerText=runs;
        }
        loadRecords();

        // ============================================================
        //  UPDATE LOOP — DOM REFS
        // ============================================================
        const elOrbCount=document.getElementById('orbCount');
        const elTimeVal=document.getElementById('timeVal');
        const elStaminaBar=document.getElementById('stamina-bar');
        const elStaminaCont=document.getElementById('stamina-container');
        const elCrosshair=document.getElementById('crosshair');
        const elThreatFill=document.getElementById('threat-fill');
        const elVignette=document.getElementById('vignette');
        const elUnitsCount=document.getElementById('unitsCount');
        const elUnitsAlerted=document.getElementById('unitsAlerted');
        const elDoorPrompt=document.getElementById('door-prompt');
        const elOrbsRemaining=document.getElementById('orbsRemaining');
        const elUI=document.getElementById('ui');
        let orbFlashTimeout=null;

        // ============================================================
        //  UPDATE LOOP
        // ============================================================
        function update(){
            if(!gameActive)return;
            const now=performance.now();const delta=Math.min((now-prevTime)/1000,0.05);prevTime=now;
            const totalElapsed=(accumulatedTime+(Date.now()-startTime)/1000).toFixed(1);
            if(!gameWon)elTimeVal.innerText=totalElapsed;

            // Mark explored cell for radar
            const pgE=worldToGrid(camera.position.x,camera.position.z);exploredCells.add(`${pgE.x},${pgE.z}`);

            // --- MOVEMENT ---
            if(!gameWon){
                const input=new THREE.Vector2(0,0);
                if(keys['KeyW'])input.y-=1;if(keys['KeyS'])input.y+=1;if(keys['KeyA'])input.x-=1;if(keys['KeyD'])input.x+=1;
                if(input.length()>0)input.normalize();
                const isTryingToMove=input.length()>0;
                const isSprinting=keys['ShiftLeft']&&isTryingToMove&&!player.isExhausted;
                currentlySprinting=isSprinting;

                if(isSprinting){player.stamina-=0.4;if(player.stamina<=0)player.isExhausted=true;}
                else{player.stamina=Math.min(MAX_STAMINA,player.stamina+0.9);if(player.stamina>=MAX_STAMINA*0.25)player.isExhausted=false;}

                const stPct=(player.stamina/MAX_STAMINA)*100;
                elStaminaBar.style.width=stPct+'%';
                elStaminaBar.style.background=player.isExhausted?'#8b0000':'linear-gradient(to bottom, #d4af37, #997a00)';
                elStaminaCont.classList.toggle('exhausted',player.isExhausted);

                // Flashlight flicker on low stamina
                if(stPct<28){const flick=0.7+0.3*Math.abs(Math.sin(now*0.025+Math.sin(now*0.007)*3));flashLight.intensity=50*flick;}
                else flashLight.intensity=50;

                const targetSpeed=isSprinting?player.runSpeed:(isTryingToMove?player.walkSpeed:0);
                const tVel=input.clone().multiplyScalar(targetSpeed);player.velocity.lerp(tVel,0.15);
                const moveX=player.velocity.x*Math.cos(yaw)+player.velocity.y*Math.sin(yaw);
                const moveZ=-player.velocity.x*Math.sin(yaw)+player.velocity.y*Math.cos(yaw);

                // Wall collision with stamina penalty
                const ax=camera.position.x+moveX,az=camera.position.z+moveZ;
                if(!isWall(ax,camera.position.z,player.radius))camera.position.x=ax;
                else if(isTryingToMove&&Math.abs(moveX)>0.001)player.stamina=Math.max(0,player.stamina-3);
                if(!isWall(camera.position.x,az,player.radius))camera.position.z=az;
                else if(isTryingToMove&&Math.abs(moveZ)>0.001)player.stamina=Math.max(0,player.stamina-3);

                const spd=player.velocity.length();
                if(spd>0.02){
                    const targetHz=isSprinting?3.5:1.5;const bobAmp=isSprinting?0.12:0.08;
                    player.headBobTimer+=delta*targetHz*Math.PI*2;
                    camera.position.y=player.height+Math.sin(player.headBobTimer)*bobAmp;
                    const bobCycle=Math.floor(player.headBobTimer/Math.PI);
                    if(bobCycle>player.lastFootstepCycle){
                        player.lastFootstepCycle=bobCycle;
                        playFootstep(isSprinting);
                        // Near-door footstep variation: higher pitch click
                        const distDoor=camera.position.distanceTo(doorGroup.position);
                        if(distDoor<20)playUISound(isSprinting?420:280,0.08,0.06,'square');
                        if(isSprinting){
                            sprintBreathCounter++;if(sprintBreathCounter%2===0)playSprintBreath();
                            // Log footstep echo
                            footstepEchoPositions.push({wx:camera.position.x,wz:camera.position.z});
                            if(footstepEchoPositions.length>3)footstepEchoPositions.shift();
                        }
                    }
                    // Sprint sound alert (throttled)
                    if(isSprinting){sprintAlertCooldown-=delta;if(sprintAlertCooldown<=0){sprintAlertCooldown=0.5;alertEnemiesInRadius(camera.position.x,camera.position.z,SOUND_SPRINT_RADIUS);}}
                }else{camera.position.y+=(player.height-camera.position.y)*0.1;player.headBobTimer+=delta;}

                // Camera lean based on yaw change
                const yawDelta=yaw-prevYaw;prevYaw=yaw;
                const targetLean=yawDelta*-18;leanAngle+=(targetLean-leanAngle)*0.12;leanAngle*=0.82;
            }

            // --- ORB ANIMATION + COLLECTION ---
            let nearbyOrb=false;
            const remainingOrbs=orbs.filter(o=>o.position.y>0).length;
            orbs.forEach(orb=>{
                if(orb.position.y>0){
                    orb.position.y=1.5+Math.sin(now*0.002+orb.position.x)*0.18;orb.rotation.y+=delta*1.2;
                    // Glow intensity scales with scarcity
                    const scarcity=1-(remainingOrbs/totalOrbs);
                    orb.material.emissiveIntensity=0.9+scarcity*0.7;orb.userData.light.intensity=1.5+scarcity*2.5;
                    if(orb.userData.ringMat)orb.userData.ringMat.opacity=0.25+scarcity*0.25;
                    const distO=camera.position.distanceTo(orb.position);
                    if(distO<6)nearbyOrb=true;
                    if(!gameWon&&distO<3){
                        orb.position.y=-1000;orbsCollected++;
                        elOrbCount.innerText=orbsCollected;
                        clearTimeout(orbFlashTimeout);elUI.classList.remove('flash');void elUI.offsetWidth;elUI.classList.add('flash');orbFlashTimeout=setTimeout(()=>elUI.classList.remove('flash'),400);
                        // Update enemy patrol speeds
                        const newPS=0.12+orbsCollected*0.007;enemies.forEach(e=>{e.userData.patrolSpeed=newPS;e.userData.alertSpeed=Math.min(0.32,0.22+orbsCollected*0.005);});
                        if(orb.userData.isGold){player.stamina=Math.min(MAX_STAMINA,player.stamina+MAX_STAMINA*0.6);player.isExhausted=false;playGoldOrbCollect();}
                        else{playOrbCollect();if(orbsCollected===6)playOrbMilestone(false);if(orbsCollected===11)playOrbMilestone(false);if(orbsCollected===totalOrbs)playOrbMilestone(true);}
                        alertEnemiesInRadius(orb.position.x,orb.position.z,SOUND_ORB_RADIUS);
                        if(orbsCollected===totalOrbs&&doorState==='closed'){
                            doorState='valves_pressure';initIndustrialAudio();
                            sirens.forEach(s=>s.light.intensity=50);
                            klaxonGain.gain.setTargetAtTime(0.015,audioCtx.currentTime,0.1);hissGain.gain.setTargetAtTime(0.1,audioCtx.currentTime,0.1);
                            // Spawn 2 new alerted enemies from far edge cells
                            const edgeCells=emptyCells.filter(c=>c.x===1||c.x===MAZE_SIZE-2||c.z===1||c.z===MAZE_SIZE-2);
                            for(let i=0;i<2;i++){const ec=edgeCells[Math.floor(Math.random()*edgeCells.length)];const ep=getPos(ec.x,ec.z);spawnEnemy(ep.x,ep.z);}
                        }
                    }
                }
            });
            elCrosshair.classList.toggle('nearby',nearbyOrb);

            // --- PARTICLES ---
            for(let i=particles.length-1;i>=0;i--){
                const p=particles[i];p.position.addScaledVector(p.userData.vel,delta);p.userData.life-=delta;
                if(p.userData.type==='steam'){p.userData.mat.opacity=(p.userData.life/1.0)*0.5;p.scale.setScalar(2.0-p.userData.life);}
                else if(p.userData.type==='spark'){p.userData.vel.y-=delta*15;if(p.position.y<0.1){p.position.y=0.1;p.userData.vel.y*=-0.5;}}
                else if(p.userData.type==='afterimage'){p.userData.mat.opacity=(p.userData.life/0.55)*0.3;}
                if(p.userData.life<=0){scene.remove(p);if(p.userData.type==='steam'||p.userData.type==='afterimage')p.userData.mat.dispose();particles.splice(i,1);}
            }

            // Ceiling drip particles
            ceilingDripTimer-=delta;
            if(ceilingDripTimer<=0){ceilingDripTimer=2+Math.random()*4;const dc=emptyCells[Math.floor(Math.random()*emptyCells.length)];const dp=getPos(dc.x,dc.z);emitSteam(dp.x,14,dp.z);}

            // Drip sounds
            dripSources.forEach(dr=>{dr.timer-=delta;if(dr.timer<=0){dr.timer=dr.interval;const dist=Math.hypot(camera.position.x-dr.wx,camera.position.z-dr.wz);if(dist<35)playDrip(Math.max(0.1,1-dist/35));}});

            // Corridor lights flicker
            corridorLights.forEach(cl=>{const flicker=Math.sin(now*0.012+cl.seed)*0.3+Math.sin(now*0.031+cl.seed*2)*0.15;cl.light.intensity=Math.max(0,cl.base+flicker);});

            // --- RADAR ---
            rCtx.clearRect(0,0,radarCanvas.width,radarCanvas.height);

            // Explored cell outlines
            rCtx.fillStyle='rgba(80,70,55,0.3)';
            exploredCells.forEach(key=>{
                const[gx,gz]=key.split(',').map(Number);const wp=getPos(gx,gz);
                const dx=wp.x-camera.position.x,dz=wp.z-camera.position.z;
                if(Math.hypot(dx,dz)>radarMaxDist)return;
                const lr=dx*Math.cos(yaw)-dz*Math.sin(yaw);const lf=-dx*Math.sin(yaw)-dz*Math.cos(yaw);
                const rx=rCenter+lr*radarScale,ry=rCenter-lf*radarScale;
                rCtx.fillRect(rx-1.2,ry-1.2,2.4,2.4);
            });

            // Crosshair lines
            rCtx.strokeStyle='rgba(212,196,168,0.2)';rCtx.lineWidth=1;
            rCtx.beginPath();rCtx.moveTo(rCenter,0);rCtx.lineTo(rCenter,radarCanvas.height);rCtx.moveTo(0,rCenter);rCtx.lineTo(radarCanvas.width,rCenter);rCtx.stroke();
            // Player blip
            rCtx.fillStyle='#d4c4a8';rCtx.beginPath();rCtx.moveTo(rCenter,rCenter-8);rCtx.lineTo(rCenter-5,rCenter+5);rCtx.lineTo(rCenter+5,rCenter+5);rCtx.fill();

            function drawBlip(wx,wz,color,size,isRect){
                const dx=wx-camera.position.x,dz=wz-camera.position.z;
                const lr=dx*Math.cos(yaw)-dz*Math.sin(yaw),lf=-dx*Math.sin(yaw)-dz*Math.cos(yaw);
                const dist=Math.sqrt(lr*lr+lf*lf);let dr=lr,df=lf;
                if(dist>radarMaxDist){dr=(lr/dist)*radarMaxDist;df=(lf/dist)*radarMaxDist;}
                const rx=rCenter+dr*radarScale,ry=rCenter-df*radarScale;
                rCtx.fillStyle=color;if(isRect)rCtx.fillRect(rx-size,ry-size,size*2,size*2);else{rCtx.beginPath();rCtx.arc(rx,ry,size,0,Math.PI*2);rCtx.fill();}
                return{rx,ry};
            }

            // Door blip
            const dxD=doorGroup.position.x-camera.position.x,dzD=doorGroup.position.z-camera.position.z;
            const lRD=dxD*Math.cos(yaw)-dzD*Math.sin(yaw),lFD=-dxD*Math.sin(yaw)-dzD*Math.cos(yaw);
            let dDist=Math.sqrt(lRD*lRD+lFD*lFD),rxD=rCenter+lRD*radarScale,ryD=rCenter-lFD*radarScale;
            if(dDist>radarMaxDist){rxD=rCenter+(lRD/dDist)*radarMaxDist*radarScale;ryD=rCenter-(lFD/dDist)*radarMaxDist*radarScale;}
            rCtx.fillStyle='#55aa55';rCtx.fillRect(rxD-5,ryD-7,10,14);rCtx.fillStyle='#112211';rCtx.fillRect(rxD-3,ryD-5,6,12);rCtx.fillStyle='#d4af37';rCtx.beginPath();rCtx.arc(rxD+1,ryD+1,1.5,0,Math.PI*2);rCtx.fill();

            // Orb blips
            orbs.forEach(orb=>{if(orb.position.y>0)drawBlip(orb.position.x,orb.position.z,orb.userData.isGold?'#ffaa00':'#d4af37',2.5,false);});

            // Last known player pos blip (blinking)
            if(lastKnownPlayerPos&&(now-lastKnownPlayerTime)<25000&&Math.floor(now/500)%2===0){
                drawBlip(lastKnownPlayerPos.wx,lastKnownPlayerPos.wz,'#ff3333',3.5,true);
            }

            // --- ENEMY STATE MACHINE ---
            let closestDist=100;let alertedCount=0;
            enemies.forEach((enemy,index)=>{
                const ud=enemy.userData;
                const toCam=new THREE.Vector3().subVectors(camera.position,enemy.position);
                const distE=toCam.length();

                // Update facing angle
                const toTgt=new THREE.Vector3().subVectors(ud.targetPos,enemy.position);
                if(toTgt.length()>0.5)ud.facingAngle=Math.atan2(toTgt.x,toTgt.z);

                // LIGHT DETECTION
                if(distE<LIGHT_DETECT_RANGE){
                    const camFwd=new THREE.Vector3(0,0,-1).applyQuaternion(camera.quaternion);
                    const camToE=toCam.clone().negate().normalize();
                    if(camFwd.dot(camToE)>FLASHLIGHT_CONE_COS&&hasLineOfSight(camera.position.x,camera.position.z,enemy.position.x,enemy.position.z)){
                        if(ud.state==='alerted'){ud.alertTimer=ALERT_DURATION;ud.lastKnownPlayerGrid=worldToGrid(camera.position.x,camera.position.z);}
                        else triggerAlert(enemy);
                    }
                }

                if(ud.state==='alerted')alertedCount++;

                // STATE TRANSITIONS
                if(ud.state==='alerted'){
                    ud.alertTimer-=delta;
                    if(ud.alertTimer<=0){ud.state='searching';ud.pathUpdateTimer=0;}
                    // BFS to player (throttled)
                    ud.pathUpdateTimer-=delta;
                    if(ud.pathUpdateTimer<=0){
                        ud.pathUpdateTimer=1.5;
                        const pg=worldToGrid(camera.position.x,camera.position.z);
                        const eg=worldToGrid(enemy.position.x,enemy.position.z);
                        const path=bfsPath(eg.x,eg.z,pg.x,pg.z);
                        if(path.length>0){ud.pathQueue=path;ud.lastKnownPlayerGrid=pg;lastKnownPlayerPos={wx:camera.position.x,wz:camera.position.z};lastKnownPlayerTime=now;}
                    }
                    if(ud.pathQueue.length>0){const nx=ud.pathQueue[0];const nw=getPos(nx.x,nx.z);const nPos=new THREE.Vector3(nw.x,2.0,nw.z);if(enemy.position.distanceTo(nPos)<TILE_SIZE*0.4)ud.pathQueue.shift();else ud.targetPos.copy(nPos);}
                    ud.light.intensity=6+Math.sin(now*0.008)*2;
                }
                else if(ud.state==='searching'){
                    enemy.rotation.y+=delta*0.7; // idle look-around
                    if(ud.lastKnownPlayerGrid){
                        const lkw=getPos(ud.lastKnownPlayerGrid.x,ud.lastKnownPlayerGrid.z);
                        const lkPos=new THREE.Vector3(lkw.x,2.0,lkw.z);
                        if(enemy.position.distanceTo(lkPos)<TILE_SIZE*0.5){
                            if(footstepEchoPositions.length>0){const echo=footstepEchoPositions.pop();ud.lastKnownPlayerGrid=worldToGrid(echo.wx,echo.wz);ud.pathQueue=[];ud.pathUpdateTimer=0;}
                            else{ud.state='patrol';ud.lastKnownPlayerGrid=null;ud.pathQueue=[];ud.light.intensity=2;}
                        }else{
                            ud.pathUpdateTimer-=delta;
                            if(ud.pathUpdateTimer<=0){ud.pathUpdateTimer=2.0;const eg=worldToGrid(enemy.position.x,enemy.position.z);ud.pathQueue=bfsPath(eg.x,eg.z,ud.lastKnownPlayerGrid.x,ud.lastKnownPlayerGrid.z);}
                            if(ud.pathQueue.length>0){const nx=ud.pathQueue[0];const nw=getPos(nx.x,nx.z);const nPos=new THREE.Vector3(nw.x,2.0,nw.z);if(enemy.position.distanceTo(nPos)<TILE_SIZE*0.4)ud.pathQueue.shift();else ud.targetPos.copy(nPos);}
                        }
                    }else{ud.state='patrol';ud.light.intensity=2;}
                }
                else{
                    // PATROL: random wander
                    ud.light.intensity=2;
                    if(enemy.position.distanceTo(ud.targetPos)<0.5){
                        const cx=Math.round(ud.targetPos.x/TILE_SIZE)+Math.floor(MAZE_SIZE/2);const cz=Math.round(ud.targetPos.z/TILE_SIZE)+Math.floor(MAZE_SIZE/2);
                        const nb=[];[[0,-1],[0,1],[-1,0],[1,0]].forEach(([dx,dz])=>{const nx=cx+dx,nz=cz+dz;if(nx>=0&&nx<MAZE_SIZE&&nz>=0&&nz<MAZE_SIZE&&maze[nx][nz]===0&&!(nx===ud.lastGrid.x&&nz===ud.lastGrid.z))nb.push({x:nx,z:nz});});
                        if(!nb.length&&maze[ud.lastGrid.x][ud.lastGrid.z]===0)nb.push(ud.lastGrid);
                        ud.lastGrid={x:cx,z:cz};const nc=nb.length?nb[Math.floor(Math.random()*nb.length)]:ud.lastGrid;
                        ud.targetPos.set(getPos(nc.x,nc.z).x,2.0,getPos(nc.x,nc.z).z);
                    }
                }

                // MOVEMENT
                const spd=ud.state==='alerted'?ud.alertSpeed:ud.state==='searching'?ud.searchSpeed:ud.patrolSpeed;
                const dir=new THREE.Vector3().subVectors(ud.targetPos,enemy.position);dir.y=0;
                if(dir.length()>0.01){dir.normalize();enemy.position.addScaledVector(dir,spd);}
                enemy.position.y=2.0+Math.sin(now*0.003+index)*0.4;

                // Aura pulse
                if(ud.auraMat){
                    const base=ud.state==='alerted'?0.18:0.08;
                    ud.auraMat.opacity=base+Math.sin(now*0.0025+index*1.7)*0.06;
                    const auraChild=enemy.children.find(c=>c.isMesh&&c.geometry===auraGeo);
                    if(auraChild)auraChild.scale.setScalar(1+Math.sin(now*0.002+index)*0.12);
                }

                // Afterimage trail (only when alerted or searching)
                if(ud.state!=='patrol'){
                    ud.afterimageTimer-=delta;if(ud.afterimageTimer<=0){ud.afterimageTimer=0.35;emitAfterimage(enemy.position.x,enemy.position.y,enemy.position.z);}
                }


                // Radar: ONLY draw alerted/searching enemies — no constant ping for patrol
                if(ud.state!=='patrol'){
                    const blipColor=ud.state==='alerted'?'#ff4444':'#ff8844';
                    const{rx,ry}=drawBlip(enemy.position.x,enemy.position.z,blipColor,3,false);
                    // FOV cone on radar
                    const fovLen=18*radarScale;const facing=ud.facingAngle-yaw;
                    const fovA=Math.PI/4;
                    rCtx.strokeStyle='rgba(255,60,60,0.28)';rCtx.lineWidth=1;
                    rCtx.beginPath();rCtx.moveTo(rx,ry);rCtx.lineTo(rx+Math.sin(facing-fovA)*fovLen,ry-Math.cos(facing-fovA)*fovLen);rCtx.moveTo(rx,ry);rCtx.lineTo(rx+Math.sin(facing+fovA)*fovLen,ry-Math.cos(facing+fovA)*fovLen);rCtx.stroke();
                    rCtx.beginPath();rCtx.arc(rx,ry,fovLen,-(facing+fovA)-Math.PI/2,-(facing-fovA)-Math.PI/2);rCtx.strokeStyle='rgba(255,60,60,0.12)';rCtx.stroke();
                }

                if(distE<closestDist)closestDist=distE;

                // DEATH CHECK
                if(!gameWon&&distE<3.0&&gameActive){
                    gameActive=false;document.exitPointerLock();
                    const t=(accumulatedTime+(Date.now()-startTime)/1000).toFixed(1);
                    document.getElementById('time-stat').innerText=formatTime(parseFloat(t));
                    document.getElementById('orb-stat').innerText=`${orbsCollected} / ${totalOrbs}`;
                    document.getElementById('death-cause').innerText=ud.name||'PHANTOM';
                    document.getElementById('death-operative').innerText=nameInput.value||'UNKNOWN';
                    document.getElementById('death-screen-ui').style.display='block';
                    saveRecord(nameInput.value||'UNKNOWN',t,orbsCollected,'KILLED');
                }
            });

            // Units HUD
            elUnitsCount.innerText=enemies.length;
            elUnitsAlerted.innerText=alertedCount>0?` // ${alertedCount} ⚠`:'';
            elUnitsAlerted.style.color=alertedCount>0?'#ff5555':'inherit';

            // Door proximity prompt
            const distToDoorUI=camera.position.distanceTo(doorGroup.position);
            if(distToDoorUI<20&&doorState==='closed'&&orbsCollected<totalOrbs){elDoorPrompt.style.display='block';elOrbsRemaining.innerText=totalOrbs-orbsCollected;}
            else elDoorPrompt.style.display='none';

            // Fog thickens near alerted enemies
            const hasAlerted=enemies.some(e=>e.userData.state==='alerted');
            const targetFog=hasAlerted?52:120;scene.fog.far+=(targetFog-scene.fog.far)*0.015;

            // Threat bar
            const threatLevel=closestDist<30?Math.max(0,(30-closestDist)/30):0;
            elThreatFill.style.width=(threatLevel*100)+'%';
            const isClose=closestDist<12,isMed=closestDist<22;
            elThreatFill.style.background=isClose?'linear-gradient(to right,#cc0000,#ff0000)':isMed?'linear-gradient(to right,#cc4400,#ff6600)':'linear-gradient(to right,#886600,#ffaa00)';
            elThreatFill.style.boxShadow=threatLevel>0.3?`0 0 ${Math.round(threatLevel*14)}px rgba(255,${isClose?0:100},0,0.8)`:'none';

            // Vignette — sprint chromatic + enemy proximity
            const sprintI=currentlySprinting?0.38:0;
            const enemyI=closestDist<18?((18-closestDist)/18)*0.52:0;
            elVignette.style.opacity=Math.min(0.92,sprintI+enemyI);
            elVignette.classList.toggle('chromatic',currentlySprinting);

            // Proximity breathing + growl
            if(proximityBreathGain){const bi=closestDist<20?Math.max(0,(20-closestDist)/20):0;proximityBreathGain.gain.setTargetAtTime(bi*0.07,audioCtx.currentTime,0.4);if(ambientGainNode)ambientGainNode.gain.setTargetAtTime(0.045+bi*0.03,audioCtx.currentTime,0.6);}
            if(enemyGrowlGain){const gi=alertedCount>0&&closestDist<35?Math.max(0,(35-closestDist)/35)*0.12:0;enemyGrowlGain.gain.setTargetAtTime(gi,audioCtx.currentTime,0.5);}

            // Sting
            if(!gameWon&&closestDist<12){camera.position.x+=(Math.random()-0.5)*((12-closestDist)*0.02);if(!hasPlayedSting){playSting();hasPlayedSting=true;}}
            else hasPlayedSting=false;

            // Apply camera lean + door shake
            camera.rotation.set(pitch,yaw,leanAngle+doorShakeZ);

            // --- DOOR SEQUENCE ---
            if(doorState!=='closed'&&doorState!=='open'){
                const distToDoor=camera.position.distanceTo(doorGroup.position);const vs=Math.max(0,1-(distToDoor/50));
                sirens.forEach((s,idx)=>{s.group.rotation.y+=delta*(idx%2===0?2:-2);});
                if(klaxonGain)klaxonGain.gain.setTargetAtTime(vs*0.015,audioCtx.currentTime,0.1);
                doorShakeZ=distToDoor<45?(Math.random()-0.5)*(45-distToDoor)*0.0015:0;
                if(doorState==='valves_pressure'){
                    if(valves[0].rotation.z<Math.PI*4){valves.forEach(v=>v.rotation.z+=delta*Math.PI);if(Math.random()>0.5)emitSteam(doorGroup.position.x,1,doorGroup.position.z);if(hissGain)hissGain.gain.setTargetAtTime(vs*0.1,audioCtx.currentTime,0.1);}
                    else{doorState='vault_unlock';if(hissGain)hissGain.gain.setTargetAtTime(0,audioCtx.currentTime,0.1);if(vaultGain)vaultGain.gain.setTargetAtTime(vs*0.04,audioCtx.currentTime,0.1);}
                }else if(doorState==='vault_unlock'){
                    if(vaultWheelGroup.rotation.z<Math.PI){vaultWheelGroup.rotation.z+=delta*(Math.PI/5);vaultWheelGroup.position.x-=delta*0.2;if(vaultGain)vaultGain.gain.setTargetAtTime(vs*0.04,audioCtx.currentTime,0.1);}
                    else{doorState='unlatching';matIndicator.color.setHex(0x00ff00);if(vaultGain)vaultGain.gain.setTargetAtTime(0,audioCtx.currentTime,0.1);if(latchGain)latchGain.gain.setTargetAtTime(vs*0.06,audioCtx.currentTime,0.1);}
                }else if(doorState==='unlatching'){
                    if(latchL.position.x>-6){const ls=delta*0.5;latchL.position.x-=ls;latchR.position.x+=ls;deadboltsLeft.forEach(b=>b.position.x-=ls*3);deadboltsRight.forEach(b=>b.position.x+=ls*3);if(latchGain)latchGain.gain.setTargetAtTime(vs*0.06,audioCtx.currentTime,0.1);}
                    else{doorState='retracting_pistons';if(latchGain)latchGain.gain.setTargetAtTime(0,audioCtx.currentTime,0.1);if(pistonGain)pistonGain.gain.setTargetAtTime(vs*0.15,audioCtx.currentTime,0.1);}
                }else if(doorState==='retracting_pistons'){
                    if(pistonGroup.position.y<5){pistonGroup.position.y+=delta*1.0;if(pistonGain)pistonGain.gain.setTargetAtTime(vs*0.15,audioCtx.currentTime,0.1);}
                    else{doorState='sliding';if(pistonGain)pistonGain.gain.setTargetAtTime(0,audioCtx.currentTime,0.1);if(gearGain)gearGain.gain.setTargetAtTime(vs*0.08,audioCtx.currentTime,0.1);}
                }else if(doorState==='sliding'){
                    if(doorHalfLeftGroup.position.x>-panelWidth-2){
                        const sl=delta*0.444;doorHalfLeftGroup.position.x-=sl;doorHalfRightGroup.position.x+=sl;
                        const gr=sl/gearRadius;mainGearLeft.rotation.z-=gr;mainGearRight.rotation.z+=gr;
                        const hr=gearRadius/helperGearRadius;helperGearLeft.rotation.z+=gr*hr;helperGearRight.rotation.z-=gr*hr;
                        if(Math.random()>0.4)emitSpark(doorGroup.position.x-3,11+gearRadius,doorGroup.position.z-0.8);
                        if(Math.random()>0.4)emitSpark(doorGroup.position.x+3,11+gearRadius,doorGroup.position.z-0.8);
                        if(gearGain)gearGain.gain.setTargetAtTime(vs*0.08,audioCtx.currentTime,0.1);
                    }else{doorState='open';sirens.forEach(s=>s.light.intensity=0);matGlassRed.emissive.setHex(0x110000);doorShakeZ=0;
                        const fot=audioCtx.currentTime+1.5;if(klaxonGain)klaxonGain.gain.linearRampToValueAtTime(0,fot);if(gearGain)gearGain.gain.linearRampToValueAtTime(0,fot);}
                }
            }else{doorShakeZ=0;}

            // --- WIN ---
            if(doorState==='open'&&camera.position.z>doorGroup.position.z+1.5&&!gameWon){
                gameWon=true;document.exitPointerLock();
                const ws=document.getElementById('win-screen');const fb=document.getElementById('fade-black');
                ws.style.display='flex';
                setTimeout(()=>{fb.style.opacity='1';ws.style.opacity='1';},50);
                document.getElementById('finalTime').innerText=`FINAL TIME: ${formatTime(parseFloat(totalElapsed))}`;
                document.getElementById('finalOrbs').innerText=`ORBS RECOVERED: ${orbsCollected} / ${totalOrbs}`;
                saveRecord(nameInput.value||'UNKNOWN',totalElapsed,orbsCollected,'ESCAPED');
                if(klaxonOsc)klaxonOsc.stop();if(latchOsc)latchOsc.stop();if(pistonOsc)pistonOsc.stop();if(gearOsc)gearOsc.stop();if(vaultOsc)vaultOsc.stop();if(hissSrc)hissSrc.stop();
            }
        }

        function animate(){requestAnimationFrame(animate);update();renderer.render(scene,camera);}animate();

        window.addEventListener('resize',()=>{camera.aspect=window.innerWidth/window.innerHeight;camera.updateProjectionMatrix();renderer.setSize(window.innerWidth,window.innerHeight);});

        document.getElementById('reboot-btn').addEventListener('click',()=>{
            const d=document.getElementById('death-screen-ui');d.style.transition='opacity 0.5s';d.style.opacity='0';setTimeout(()=>location.reload(),500);
        });
