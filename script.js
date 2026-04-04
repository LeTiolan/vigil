
        import * as THREE from 'three';

        // ================================================================
        //  MAZE GENERATION  (original — untouched)
        // ================================================================
        const MAZE_SIZE = 25; const TILE_SIZE = 12;
        const maze = Array(MAZE_SIZE).fill(null).map(() => Array(MAZE_SIZE).fill(1));
        const emptyCells = [];

        function carveMaze(x, y) {
            maze[x][y] = 0;
            const dirs = [[0,-1],[0,1],[-1,0],[1,0]].sort(() => Math.random() - 0.5);
            for (let [dx, dy] of dirs) {
                const nx = x + dx*2, ny = y + dy*2;
                if (nx>0 && nx<MAZE_SIZE-1 && ny>0 && ny<MAZE_SIZE-1 && maze[nx][ny]===1) {
                    maze[x+dx][y+dy] = 0; carveMaze(nx, ny);
                }
            }
        }
        carveMaze(1, 1);
        for (let i=1;i<MAZE_SIZE-1;i++) for (let j=1;j<MAZE_SIZE-1;j++)
            if (maze[i][j]===1 && ((maze[i-1][j]===0&&maze[i+1][j]===0)||(maze[i][j-1]===0&&maze[i][j+1]===0)) && Math.random()<0.25)
                maze[i][j]=0;

        const exitGridX = Math.floor(MAZE_SIZE/2), exitGridZ = MAZE_SIZE-1;
        for (let i=-1;i<=1;i++) for (let j=-3;j<=-1;j++) maze[exitGridX+i][exitGridZ+j]=0;
        maze[exitGridX][exitGridZ]=0;
        for (let i=0;i<MAZE_SIZE;i++) for (let j=0;j<MAZE_SIZE;j++) if (maze[i][j]===0) emptyCells.push({x:i,z:j});

        // ================================================================
        //  PATHFINDING — BFS with parent-map (O(n) memory, not O(n^2))
        // ================================================================
        function worldToGrid(wx, wz) {
            const o = Math.floor(MAZE_SIZE/2);
            return { x: Math.max(0,Math.min(MAZE_SIZE-1, Math.round(wx/TILE_SIZE)+o)),
                     z: Math.max(0,Math.min(MAZE_SIZE-1, Math.round(wz/TILE_SIZE)+o)) };
        }
        function bfsPath(sx,sz,gx,gz) {
            if (sx===gx&&sz===gz) return [];
            const queue=[{x:sx,z:sz}], parent=new Map();
            parent.set(`${sx},${sz}`, null);
            let it=0;
            while (queue.length && it++<2500) {
                const {x,z}=queue.shift();
                for (const [dx,dz] of [[0,-1],[0,1],[-1,0],[1,0]]) {
                    const nx=x+dx, nz=z+dz, k=`${nx},${nz}`;
                    if (nx<0||nx>=MAZE_SIZE||nz<0||nz>=MAZE_SIZE||maze[nx][nz]!==0||parent.has(k)) continue;
                    parent.set(k,`${x},${z}`);
                    if (nx===gx&&nz===gz) {
                        const path=[]; let cur=k;
                        while(cur){ const [px,pz]=cur.split(',').map(Number); path.unshift({x:px,z:pz}); cur=parent.get(cur); }
                        if (path.length&&path[0].x===sx&&path[0].z===sz) path.shift();
                        return path;
                    }
                    queue.push({x:nx,z:nz});
                }
            }
            return [];
        }
        function hasLOS(ax,az,bx,bz) {
            const g0=worldToGrid(ax,az), g1=worldToGrid(bx,bz);
            const steps=Math.max(Math.abs(g1.x-g0.x),Math.abs(g1.z-g0.z));
            if (!steps) return true;
            for (let i=1;i<steps;i++) {
                const t=i/steps, cx=Math.round(g0.x+(g1.x-g0.x)*t), cz=Math.round(g0.z+(g1.z-g0.z)*t);
                if (cx>=0&&cx<MAZE_SIZE&&cz>=0&&cz<MAZE_SIZE&&maze[cx][cz]===1) return false;
            }
            return true;
        }

        // ================================================================
        //  GAME CONSTANTS & STATE
        // ================================================================
        const totalOrbs=12, MAX_STAMINA=200;
        const ALERT_DURATION=10.0, LIGHT_RANGE=34, CONE_COS=Math.cos(60*Math.PI/180), SPRINT_R=24;
        const ENEMY_NAMES=['REVENANT','UNIT-07','SPECTER-X','THE HOLLOW','SHADE-03','ECHO-NULL'];

        let orbsCollected=0, gameActive=false, gameWon=false;
        let startTime=0, accumulatedTime=0, hasPlayedSting=false, prevTime=performance.now();
        let yaw=Math.PI, pitch=0;
        const SENSITIVITY=0.002;
        let introShown=false, sprintAlertCD=0, lastFootCycle=0;
        let terminalActivated=false, terminalButtonT=0;
        let currentlySprinting=false;
        const exploredCells=new Set();
        const keys={};

        const player={
            height:2.1, radius:0.8, walkSpeed:0.22, runSpeed:0.46,
            stamina:MAX_STAMINA, isExhausted:false,
            velocity:new THREE.Vector2(0,0), headBobTimer:0
        };

        document.getElementById('totalOrbsUI').innerText=totalOrbs;

        // DOM refs (cached)
        const elOrbCount=document.getElementById('orbCount');
        const elTimeVal=document.getElementById('timeVal');
        const elStBar=document.getElementById('stamina-bar');
        const elStCont=document.getElementById('stamina-container');
        const elCross=document.getElementById('crosshair');
        const elPrompt=document.getElementById('interact-prompt');
        const radarCanvas=document.getElementById('radar');
        const rCtx=radarCanvas.getContext('2d');
        const rC=radarCanvas.width/2, rMax=100, rScl=(rC-8)/rMax;

        // ================================================================
        //  SCENE, RENDERER, CAMERA
        //  PSX aesthetic: pixel ratio 0.55, no AA, NearestFilter textures
        // ================================================================
        const scene=new THREE.Scene();
        scene.background=new THREE.Color(0x08090f);
        scene.fog=new THREE.FogExp2(0x08090f, 0.025); // exponential fog = PSX feel

        const camera=new THREE.PerspectiveCamera(75,innerWidth/innerHeight,0.1,300);
        camera.rotation.order='YXZ';

        const renderer=new THREE.WebGLRenderer({antialias:false}); // no AA = PSX
        renderer.setPixelRatio(Math.min(window.devicePixelRatio,1)*0.65); // chunky pixels
        renderer.setSize(innerWidth,innerHeight);
        renderer.shadowMap.enabled=true;
        renderer.shadowMap.type=THREE.BasicShadowMap; // cheapest shadows
        document.body.appendChild(renderer.domElement);

        // Lights
        const hemi=new THREE.HemisphereLight(0x1a2030,0x0a0810,0.5); scene.add(hemi);
        const flash=new THREE.SpotLight(0xffe8c0,80,180,Math.PI/7,0.45,1.5);
        flash.castShadow=true; flash.shadow.mapSize.setScalar(512); flash.shadow.bias=-0.002;
        camera.add(flash); camera.add(flash.target); flash.target.position.set(0,0,-1); scene.add(camera);

        // ================================================================
        //  AUDIO ENGINE  (original + new sounds)
        // ================================================================
        const audioCtx=new (window.AudioContext||window.webkitAudioContext)();
        let klaxonOsc,klaxonGain,vaultOsc,vaultGain,latchOsc,latchGain;
        let pistonOsc,pistonGain,gearOsc,gearGain,hissSrc,hissGain;

        function resumeAudio(){ if(audioCtx.state==='suspended') audioCtx.resume(); }

        function initIndustrialAudio() {
            resumeAudio();
            klaxonOsc=audioCtx.createOscillator(); klaxonOsc.type='triangle'; klaxonOsc.frequency.value=450;
            const kL=audioCtx.createOscillator(); kL.frequency.value=2;
            const kM=audioCtx.createGain(); kM.gain.value=150; kL.connect(kM); kM.connect(klaxonOsc.frequency); kL.start();
            klaxonGain=audioCtx.createGain(); klaxonGain.gain.value=0;
            klaxonOsc.connect(klaxonGain); klaxonGain.connect(audioCtx.destination); klaxonOsc.start();
            vaultOsc=audioCtx.createOscillator(); vaultOsc.type='sawtooth'; vaultOsc.frequency.value=180;
            vaultGain=audioCtx.createGain(); vaultGain.gain.value=0;
            vaultOsc.connect(vaultGain); vaultGain.connect(audioCtx.destination); vaultOsc.start();
            latchOsc=audioCtx.createOscillator(); latchOsc.type='sawtooth'; latchOsc.frequency.value=90;
            latchGain=audioCtx.createGain(); latchGain.gain.value=0;
            latchOsc.connect(latchGain); latchGain.connect(audioCtx.destination); latchOsc.start();
            pistonOsc=audioCtx.createOscillator(); pistonOsc.type='square'; pistonOsc.frequency.value=35;
            pistonGain=audioCtx.createGain(); pistonGain.gain.value=0;
            const filt=audioCtx.createBiquadFilter(); filt.type='lowpass'; filt.frequency.value=150;
            pistonOsc.connect(filt); filt.connect(pistonGain); pistonGain.connect(audioCtx.destination); pistonOsc.start();
            gearOsc=audioCtx.createOscillator(); gearOsc.type='square'; gearOsc.frequency.value=18;
            gearGain=audioCtx.createGain(); gearGain.gain.value=0;
            gearOsc.connect(gearGain); gearGain.connect(audioCtx.destination); gearOsc.start();
            const bsz=audioCtx.sampleRate*2, nb=audioCtx.createBuffer(1,bsz,audioCtx.sampleRate);
            const nd=nb.getChannelData(0); for(let i=0;i<bsz;i++) nd[i]=Math.random()*2-1;
            hissSrc=audioCtx.createBufferSource(); hissSrc.buffer=nb; hissSrc.loop=true;
            const hf=audioCtx.createBiquadFilter(); hf.type='highpass'; hf.frequency.value=1000;
            hissGain=audioCtx.createGain(); hissGain.gain.value=0;
            hissSrc.connect(hf); hf.connect(hissGain); hissGain.connect(audioCtx.destination); hissSrc.start();
        }

        function playSting() {
            resumeAudio();
            const o=audioCtx.createOscillator(), g=audioCtx.createGain(); o.type='sawtooth';
            o.frequency.setValueAtTime(120,audioCtx.currentTime); o.frequency.exponentialRampToValueAtTime(30,audioCtx.currentTime+1);
            g.gain.setValueAtTime(0.2,audioCtx.currentTime); g.gain.exponentialRampToValueAtTime(0.01,audioCtx.currentTime+1);
            o.connect(g); g.connect(audioCtx.destination); o.start(); o.stop(audioCtx.currentTime+1);
        }

        // Footstep — distinct walk vs sprint using filtered noise burst
        function playFootstep(sprint) {
            resumeAudio();
            const dur = sprint ? 0.038 : 0.05;
            const sz=Math.floor(audioCtx.sampleRate*dur);
            const buf=audioCtx.createBuffer(1,sz,audioCtx.sampleRate);
            const d=buf.getChannelData(0);
            for(let i=0;i<sz;i++) d[i]=(Math.random()*2-1)*Math.pow(1-i/sz, sprint?4:6);
            const src=audioCtx.createBufferSource(); src.buffer=buf;
            const lp=audioCtx.createBiquadFilter(); lp.type='lowpass';
            lp.frequency.value=sprint?900:380; // sprint=hard thud, walk=soft thud
            const g=audioCtx.createGain(); g.gain.value=sprint?0.48:0.22;
            src.connect(lp); lp.connect(g); g.connect(audioCtx.destination); src.start();
        }

        // Alert screech
        function playScreech() {
            resumeAudio();
            const o=audioCtx.createOscillator(), g=audioCtx.createGain(); o.type='sawtooth';
            o.frequency.setValueAtTime(280,audioCtx.currentTime); o.frequency.exponentialRampToValueAtTime(50,audioCtx.currentTime+0.4);
            g.gain.setValueAtTime(0.14,audioCtx.currentTime); g.gain.exponentialRampToValueAtTime(0.001,audioCtx.currentTime+0.4);
            o.connect(g); g.connect(audioCtx.destination); o.start(); o.stop(audioCtx.currentTime+0.4);
        }

        // Terminal activation click
        function playTerminalClick() {
            resumeAudio();
            [180,120,80].forEach((f,i)=>{
                const o=audioCtx.createOscillator(), g=audioCtx.createGain(); o.type='square'; o.frequency.value=f;
                const t=audioCtx.currentTime+i*0.06;
                g.gain.setValueAtTime(0.18,t); g.gain.exponentialRampToValueAtTime(0.001,t+0.1);
                o.connect(g); g.connect(audioCtx.destination); o.start(t); o.stop(t+0.1);
            });
        }

        function playUISound(freq,vol,dur,type='triangle') {
            resumeAudio();
            const o=audioCtx.createOscillator(), g=audioCtx.createGain(); o.type=type;
            o.frequency.setValueAtTime(freq,audioCtx.currentTime); o.frequency.exponentialRampToValueAtTime(freq/2,audioCtx.currentTime+dur);
            g.gain.setValueAtTime(vol,audioCtx.currentTime); g.gain.exponentialRampToValueAtTime(0.001,audioCtx.currentTime+dur);
            o.connect(g); g.connect(audioCtx.destination); o.start(); o.stop(audioCtx.currentTime+dur);
        }

        // ================================================================
        //  PROCEDURAL TEXTURES — PSX style: 128x128, NearestFilter
        // ================================================================
        function makeTex(canvas) {
            const t=new THREE.CanvasTexture(canvas);
            t.magFilter=THREE.NearestFilter;
            t.minFilter=THREE.NearestFilter;
            t.generateMipmaps=false;
            t.wrapS=t.wrapT=THREE.RepeatWrapping;
            return t;
        }

        // Stone wall texture — visible blocks with grime
        function createWallTexture() {
            const c=document.createElement('canvas'); c.width=128; c.height=128;
            const ctx=c.getContext('2d');
            // Base dark stone
            ctx.fillStyle='#1c2c1c'; ctx.fillRect(0,0,128,128);
            // Stone blocks — two rows of offset bricks
            const bW=64, bH=32;
            for (let row=0;row<4;row++) {
                for (let col=-1;col<3;col++) {
                    const ox=(row%2===0)?0:bW/2;
                    const bx=col*bW+ox, by=row*bH;
                    const shade=Math.floor(Math.random()*20);
                    ctx.fillStyle=`rgb(${28+shade},${45+shade},${25+shade})`;
                    ctx.fillRect(bx+2,by+2,bW-4,bH-4);
                    // Grime noise
                    for(let i=0;i<30;i++){
                        ctx.fillStyle=`rgba(0,0,0,${Math.random()*0.25})`;
                        ctx.fillRect(bx+2+Math.random()*(bW-4),by+2+Math.random()*(bH-4),Math.random()*5+1,Math.random()*4+1);
                    }
                    // Moisture streak
                    if(Math.random()>0.5){
                        const sx=bx+8+Math.random()*(bW-16);
                        const gr=ctx.createLinearGradient(sx,by,sx+2,by+bH);
                        gr.addColorStop(0,'rgba(60,30,5,0)'); gr.addColorStop(0.4,'rgba(80,40,5,0.5)'); gr.addColorStop(1,'rgba(50,25,3,0)');
                        ctx.fillStyle=gr; ctx.fillRect(sx,by,3,bH);
                    }
                    // Top highlight
                    ctx.fillStyle='rgba(255,255,255,0.04)'; ctx.fillRect(bx+2,by+2,bW-4,2);
                }
            }
            // Mortar lines
            ctx.strokeStyle='#080e08'; ctx.lineWidth=2;
            for(let r=0;r<=4;r++){ctx.beginPath();ctx.moveTo(0,r*bH);ctx.lineTo(128,r*bH);ctx.stroke();}
            for(let r=0;r<4;r++){
                const ox=(r%2===0)?0:bW/2;
                for(let col=-1;col<=3;col++){const bx=col*bW+ox;ctx.beginPath();ctx.moveTo(bx,r*bH);ctx.lineTo(bx,(r+1)*bH);ctx.stroke();}
            }
            const t=makeTex(c); t.repeat.set(1.5,1.5); return t;
        }

        // Metal floor texture — plates with bolts
        function createFloorTexture() {
            const c=document.createElement('canvas'); c.width=128; c.height=128;
            const ctx=c.getContext('2d');
            ctx.fillStyle='#141414'; ctx.fillRect(0,0,128,128);
            const ps=64;
            for(let r=0;r<2;r++) for(let col=0;col<2;col++){
                const sh=Math.floor(Math.random()*12);
                ctx.fillStyle=`rgb(${22+sh},${22+sh},${24+sh})`; ctx.fillRect(col*ps+1,r*ps+1,ps-2,ps-2);
                // Bolts
                for(const[sx,sy]of[[col*ps+8,r*ps+8],[col*ps+ps-8,r*ps+8],[col*ps+8,r*ps+ps-8],[col*ps+ps-8,r*ps+ps-8]]){
                    ctx.fillStyle='#1e1e1e'; ctx.beginPath(); ctx.arc(sx,sy,4,0,Math.PI*2); ctx.fill();
                    ctx.fillStyle='#0c0c0c'; ctx.beginPath(); ctx.arc(sx,sy,2,0,Math.PI*2); ctx.fill();
                }
                // Scuffs
                for(let i=0;i<12;i++){ctx.fillStyle=`rgba(0,0,0,${Math.random()*0.12})`;ctx.fillRect(col*ps+Math.random()*ps,r*ps+Math.random()*ps,Math.random()*14+2,1);}
                ctx.fillStyle='rgba(255,255,255,0.02)'; ctx.fillRect(col*ps+1,r*ps+1,ps-2,1);
            }
            ctx.strokeStyle='#0a0a0a'; ctx.lineWidth=2;
            for(let i=0;i<=2;i++){ctx.beginPath();ctx.moveTo(i*ps,0);ctx.lineTo(i*ps,128);ctx.stroke();ctx.beginPath();ctx.moveTo(0,i*ps);ctx.lineTo(128,i*ps);ctx.stroke();}
            const t=makeTex(c); t.repeat.set(5,5); return t;
        }

        // Ceiling texture — concrete panels
        function createCeilingTexture() {
            const c=document.createElement('canvas'); c.width=128; c.height=128;
            const ctx=c.getContext('2d');
            ctx.fillStyle='#111213'; ctx.fillRect(0,0,128,128);
            // Panel seams
            ctx.strokeStyle='#0a0a0b'; ctx.lineWidth=3;
            for(let x=0;x<=128;x+=32){ctx.beginPath();ctx.moveTo(x,0);ctx.lineTo(x,128);ctx.stroke();}
            for(let y=0;y<=128;y+=32){ctx.beginPath();ctx.moveTo(0,y);ctx.lineTo(128,y);ctx.stroke();}
            // Noise
            for(let i=0;i<3000;i++){ctx.fillStyle=`rgba(0,0,0,${Math.random()*0.2})`;ctx.fillRect(Math.random()*128,Math.random()*128,Math.random()*2+1,Math.random()*2+1);}
            const t=makeTex(c); t.repeat.set(3,3); return t;
        }

        // Grime (for door panels)
        function createGrimeTexture() {
            const c=document.createElement('canvas'); c.width=128; c.height=128;
            const ctx=c.getContext('2d'); ctx.fillStyle='#222'; ctx.fillRect(0,0,128,128);
            for(let i=0;i<4000;i++){ctx.fillStyle=Math.random()>0.5?'rgba(0,0,0,0.12)':'rgba(70,55,35,0.12)';ctx.beginPath();ctx.arc(Math.random()*128,Math.random()*128,Math.random()*3,0,Math.PI*2);ctx.fill();}
            const t=makeTex(c); t.repeat.set(2,2); return t;
        }

        // Hazard stripes
        function createHazardTexture() {
            const c=document.createElement('canvas'); c.width=128; c.height=128;
            const ctx=c.getContext('2d');
            ctx.fillStyle='#c4a030'; ctx.fillRect(0,0,128,128); ctx.fillStyle='#111';
            for(let i=-128;i<256;i+=32){ctx.beginPath();ctx.moveTo(i,0);ctx.lineTo(i+16,0);ctx.lineTo(i+144,128);ctx.lineTo(i+128,128);ctx.fill();}
            const t=makeTex(c); return t;
        }

        // ================================================================
        //  MATERIALS
        // ================================================================
        const wallTex=createWallTexture(), floorTex=createFloorTexture();
        const ceilTex=createCeilingTexture(), grimeTex=createGrimeTexture();
        const hazardTex=createHazardTexture();

        const matWall    =new THREE.MeshLambertMaterial({map:wallTex});
        const matFloor   =new THREE.MeshLambertMaterial({map:floorTex});
        const matCeil    =new THREE.MeshLambertMaterial({map:ceilTex});
        const matDarkMetal=new THREE.MeshLambertMaterial({map:grimeTex});
        const matRustyFrame=new THREE.MeshLambertMaterial({color:0x3a2e20});
        const matBrightSteel=new THREE.MeshLambertMaterial({color:0x999999});
        const matHazard  =new THREE.MeshLambertMaterial({map:hazardTex});
        const matWarnYellow=new THREE.MeshLambertMaterial({color:0xcc9900});
        const matBlackHole=new THREE.MeshLambertMaterial({color:0x030303});
        const matGlassRed=new THREE.MeshBasicMaterial({color:0xff0000,transparent:true,opacity:0.8});
        const matIndicator=new THREE.MeshBasicMaterial({color:0xff0000});

        // ================================================================
        //  PARTICLES  (original — untouched)
        // ================================================================
        const particles=[];
        const sparkGeo=new THREE.BoxGeometry(0.1,0.1,0.1);
        const sparkMat=new THREE.MeshBasicMaterial({color:0xffaa00});
        const steamGeo=new THREE.PlaneGeometry(1.5,1.5);
        const steamMatB=new THREE.MeshBasicMaterial({color:0xcccccc,transparent:true,opacity:0.4,depthWrite:false});

        function emitSpark(x,y,z){
            const s=new THREE.Mesh(sparkGeo,sparkMat); s.position.set(x,y,z);
            s.userData={vel:new THREE.Vector3((Math.random()-0.5)*5,Math.random()*5+2,(Math.random()-0.5)*5),life:1.0,type:'spark'};
            scene.add(s); particles.push(s);
        }
        function emitSteam(x,y,z){
            const mat=steamMatB.clone(), s=new THREE.Mesh(steamGeo,mat); s.position.set(x,y,z);
            s.userData={vel:new THREE.Vector3((Math.random()-0.5)*2,Math.random()*3+1,(Math.random()-0.5)*2),life:1.0,type:'steam',mat};
            scene.add(s); particles.push(s);
        }

        // ================================================================
        //  COLLISION  (original — untouched)
        // ================================================================
        const solidDoorParts=[], partBox=new THREE.Box3();
        function registerSolid(m){solidDoorParts.push(m);}

        function isWall(x,z,r){
            const off=Math.floor(MAZE_SIZE/2);
            const x0=Math.floor((x-r+TILE_SIZE/2)/TILE_SIZE)+off-1;
            const x1=Math.floor((x+r+TILE_SIZE/2)/TILE_SIZE)+off+1;
            const z0=Math.floor((z-r+TILE_SIZE/2)/TILE_SIZE)+off-1;
            const z1=Math.floor((z+r+TILE_SIZE/2)/TILE_SIZE)+off+1;
            for(let i=x0;i<=x1;i++) for(let j=z0;j<=z1;j++){
                if(i<0||i>=MAZE_SIZE||j<0||j>=MAZE_SIZE||maze[i][j]!==1) continue;
                const wx=(i-off)*TILE_SIZE, wz=(j-off)*TILE_SIZE;
                const cx=Math.max(wx-TILE_SIZE/2,Math.min(x,wx+TILE_SIZE/2));
                const cz=Math.max(wz-TILE_SIZE/2,Math.min(z,wz+TILE_SIZE/2));
                if((x-cx)*(x-cx)+(z-cz)*(z-cz)<r*r) return true;
            }
            if(Math.abs(x-doorGroup.position.x)<TILE_SIZE&&Math.abs(z-doorGroup.position.z)<TILE_SIZE){
                const pb=new THREE.Box3(new THREE.Vector3(x-r,0,z-r),new THREE.Vector3(x+r,player.height,z+r));
                for(const sp of solidDoorParts){partBox.setFromObject(sp);if(pb.intersectsBox(partBox))return true;}
            }
            return false;
        }

        // ================================================================
        //  GEAR FACTORY
        // ================================================================
        function createGearMesh(radius,depth,teeth){
            const g=new THREE.Group();
            const core=new THREE.Mesh(new THREE.CylinderGeometry(radius*0.85,radius*0.85,depth,16),matBrightSteel);
            core.rotation.x=Math.PI/2; g.add(core);
            const tGeo=new THREE.BoxGeometry((Math.PI*radius*2)/(teeth*2),radius*0.25,depth);
            for(let i=0;i<teeth;i++){
                const a=(i/teeth)*Math.PI*2, tooth=new THREE.Mesh(tGeo,matBrightSteel);
                tooth.position.set(Math.cos(a)*radius*0.95,Math.sin(a)*radius*0.95,0);
                tooth.rotation.z=a+Math.PI/2; g.add(tooth);
            }
            const axle=new THREE.Mesh(new THREE.CylinderGeometry(radius*0.3,radius*0.3,depth+0.2,12),matDarkMetal);
            axle.rotation.x=Math.PI/2; g.add(axle);
            const hb=new THREE.Mesh(new THREE.BoxGeometry(radius*2,radius*2,depth),new THREE.MeshBasicMaterial({visible:false}));
            g.add(hb); registerSolid(hb); return g;
        }

        function getPos(i,j){return{x:(i-Math.floor(MAZE_SIZE/2))*TILE_SIZE,z:(j-Math.floor(MAZE_SIZE/2))*TILE_SIZE};}

        // ================================================================
        //  LEVEL GEOMETRY
        //  Walls use InstancedMesh for massive draw-call reduction
        // ================================================================
        // Floor
        const floor=new THREE.Mesh(new THREE.PlaneGeometry(MAZE_SIZE*TILE_SIZE,MAZE_SIZE*TILE_SIZE),matFloor);
        floor.rotation.x=-Math.PI/2; floor.receiveShadow=true; scene.add(floor);

        // Ceiling
        const ceil=new THREE.Mesh(new THREE.PlaneGeometry(MAZE_SIZE*TILE_SIZE,MAZE_SIZE*TILE_SIZE),matCeil);
        ceil.rotation.x=Math.PI/2; ceil.position.y=14; scene.add(ceil);

        // Walls — count first, then InstancedMesh (1 draw call for all walls)
        let wallCount=0;
        for(let i=0;i<MAZE_SIZE;i++) for(let j=0;j<MAZE_SIZE;j++) if(maze[i][j]===1) wallCount++;
        const wallGeo=new THREE.BoxGeometry(TILE_SIZE,14,TILE_SIZE);
        const wallMesh=new THREE.InstancedMesh(wallGeo,matWall,wallCount);
        wallMesh.castShadow=true; wallMesh.receiveShadow=true;
        const _dummy=new THREE.Object3D();
        let _wi=0;
        for(let i=0;i<MAZE_SIZE;i++) for(let j=0;j<MAZE_SIZE;j++) if(maze[i][j]===1){
            const p=getPos(i,j); _dummy.position.set(p.x,7,p.z); _dummy.updateMatrix();
            wallMesh.setMatrixAt(_wi++,_dummy.matrix);
        }
        wallMesh.instanceMatrix.needsUpdate=true; scene.add(wallMesh);

        // Corridor point lights — atmospheric fill, no shadows
        const corridorLights=[];
        {
            const sp=getPos(1,1); let added=0;
            for(const cell of emptyCells){
                if(added>=12) break;
                const pos=getPos(cell.x,cell.z);
                if(Math.hypot(pos.x-sp.x,pos.z-sp.z)<15) continue;
                if(Math.random()>0.92){
                    // Light strip on ceiling
                    const stripMat=new THREE.MeshBasicMaterial({color:0x5566aa});
                    const strip=new THREE.Mesh(new THREE.BoxGeometry(2,0.08,0.5),stripMat);
                    strip.position.set(pos.x,13.9,pos.z); scene.add(strip);
                    const cl=new THREE.PointLight(0x4455aa,0,40);
                    cl.position.set(pos.x,13,pos.z); scene.add(cl);
                    const baseI=1.8+Math.random()*1.2;
                    corridorLights.push({light:cl,strip:stripMat,seed:Math.random()*100,base:baseI,
                        rate:Math.random()>0.35?0.6+Math.random()*1.0:14+Math.random()*8,broken:Math.random()>0.55});
                    added++;
                }
            }
        }

        const startPos=getPos(1,1);
        camera.position.set(startPos.x,player.height,startPos.z); camera.rotation.set(0,yaw,0);

        // ================================================================
        //  TITAN DOOR  (original — untouched)
        // ================================================================
        let doorState='closed';
        const doorWP=getPos(exitGridX,exitGridZ);
        const doorGroup=new THREE.Group(); doorGroup.position.set(doorWP.x,0,doorWP.z);

        const FH=16,FZ=-1.5,DZ=0.5,PW=5.0;
        const lintel=new THREE.Mesh(new THREE.BoxGeometry(16,4,2),matRustyFrame); lintel.position.set(0,FH-2,FZ); lintel.castShadow=true; doorGroup.add(lintel); registerSolid(lintel);
        const lPillar=new THREE.Mesh(new THREE.BoxGeometry(4,FH,2),matRustyFrame); lPillar.position.set(-6,FH/2,FZ); lPillar.castShadow=true; doorGroup.add(lPillar); registerSolid(lPillar);
        const rPillar=new THREE.Mesh(new THREE.BoxGeometry(4,FH,2),matRustyFrame); rPillar.position.set(6,FH/2,FZ); rPillar.castShadow=true; doorGroup.add(rPillar); registerSolid(rPillar);

        const sirens=[];
        const createSiren=(x,z)=>{
            const sg=new THREE.Group(); sg.position.set(x,FH-4,z);
            sg.add(new THREE.Mesh(new THREE.CylinderGeometry(0.5,0.5,1,16),matGlassRed));
            const sp=new THREE.SpotLight(0xff0000,0,40,Math.PI/6,0.5,1);
            sp.target.position.set(0,-10,10); sp.castShadow=true;
            sp.shadow.mapSize.setScalar(256); sp.shadow.camera.near=1; sp.shadow.camera.far=40; sp.shadow.bias=-0.001;
            sg.add(sp); sg.add(sp.target); doorGroup.add(sg); sirens.push({group:sg,light:sp});
        };
        createSiren(-6,FZ-1); createSiren(6,FZ-1); createSiren(-6,FZ+1); createSiren(6,FZ+1);

        const indL=new THREE.Mesh(new THREE.BoxGeometry(0.2,6,0.2),matIndicator); indL.position.set(-4.1,7,FZ); doorGroup.add(indL);
        const indR=new THREE.Mesh(new THREE.BoxGeometry(0.2,6,0.2),matIndicator); indR.position.set(4.1,7,FZ); doorGroup.add(indR);

        const doorHL=new THREE.Group(); doorHL.position.set(-PW/2,7,DZ); doorGroup.add(doorHL);
        const doorHR=new THREE.Group(); doorHR.position.set(PW/2,7,DZ); doorGroup.add(doorHR);

        const panelGeo=new THREE.BoxGeometry(PW,14,1.0);
        const pL=new THREE.Mesh(panelGeo,matDarkMetal); pL.castShadow=true; doorHL.add(pL); registerSolid(pL);
        const pR=new THREE.Mesh(panelGeo,matDarkMetal); pR.castShadow=true; doorHR.add(pR); registerSolid(pR);

        const deadboltsL=[], deadboltsR=[];
        const boltGeo=new THREE.CylinderGeometry(0.3,0.3,3,16); boltGeo.rotateZ(Math.PI/2);
        for(const y of[-3,-1,1,3]){
            const bL=new THREE.Mesh(boltGeo,matBrightSteel); bL.position.set(1.5,y,0); doorHL.add(bL); deadboltsL.push(bL);
            const bR=new THREE.Mesh(boltGeo,matBrightSteel); bR.position.set(-1.5,y,0); doorHR.add(bR); deadboltsR.push(bR);
        }

        const vaultWG=new THREE.Group(); vaultWG.position.set(PW/2,0,-0.7); doorHL.add(vaultWG);
        vaultWG.add(createGearMesh(2.5,0.8,16));
        const vSocket=new THREE.Mesh(new THREE.CylinderGeometry(2.6,2.6,0.2,16),matBlackHole);
        vSocket.rotation.x=Math.PI/2; vSocket.position.set(-PW/2,0,-0.6); doorHR.add(vSocket);

        const valves=[];
        for(const py of[-3,3]){
            const v=new THREE.Mesh(new THREE.TorusGeometry(0.6,0.15,8,16),matWarnYellow);
            v.position.set(-1.0,py,-0.7); doorHR.add(v); valves.push(v);
        }

        const latchGeo=new THREE.BoxGeometry(2,1.5,1.5);
        const latchL=new THREE.Mesh(latchGeo,matHazard); latchL.position.set(-4.5,7,-0.6); latchL.castShadow=true; doorGroup.add(latchL); registerSolid(latchL);
        const latchR=new THREE.Mesh(latchGeo,matHazard); latchR.position.set(4.5,7,-0.6); latchR.castShadow=true; doorGroup.add(latchR); registerSolid(latchR);

        const rackGeo=new THREE.BoxGeometry(PW-0.5,0.8,0.5);
        const rL=new THREE.Mesh(rackGeo,matBrightSteel); rL.position.set(0,4,-0.8); doorHL.add(rL);
        const rRk=new THREE.Mesh(rackGeo,matBrightSteel); rRk.position.set(0,4,-0.8); doorHR.add(rRk);

        const GR=1.6;
        const mgL=createGearMesh(GR,0.6,12); mgL.position.set(-3,11+GR,-0.8); doorGroup.add(mgL);
        const mgR=createGearMesh(GR,0.6,12); mgR.position.set(3,11+GR,-0.8); doorGroup.add(mgR);
        const HGR=0.8;
        const hgL=createGearMesh(HGR,0.6,6); hgL.position.set(-3-GR-HGR+0.2,11+GR+1,-0.8); doorGroup.add(hgL);
        const hgR=createGearMesh(HGR,0.6,6); hgR.position.set(3+GR+HGR-0.2,11+GR+1,-0.8); doorGroup.add(hgR);

        const pistonGrp=new THREE.Group(); doorGroup.add(pistonGrp);
        const pistonGeo=new THREE.BoxGeometry(1.5,6,1.5);
        const pistonL=new THREE.Mesh(pistonGeo,matHazard); pistonL.position.set(-3.5,7,-0.8); pistonGrp.add(pistonL); registerSolid(pistonL);
        const pistonR=new THREE.Mesh(pistonGeo,matHazard); pistonR.position.set(3.5,7,-0.8); pistonGrp.add(pistonR); registerSolid(pistonR);
        scene.add(doorGroup);

        // ================================================================
        //  TERMINAL PANEL — physical wall-mounted interactive object
        // ================================================================
        // Find an open cell near the door approach for the terminal
        const termTargetX=exitGridX-2, termTargetZ=exitGridZ-3;
        const termCellX=Math.max(1,Math.min(MAZE_SIZE-2,termTargetX));
        const termCellZ=Math.max(1,Math.min(MAZE_SIZE-2,termTargetZ));
        const termWorldPos=getPos(termCellX,termCellZ);
        const TERM_WX=termWorldPos.x+4, TERM_WZ=termWorldPos.z;

        const termGrp=new THREE.Group();
        termGrp.position.set(TERM_WX,0,TERM_WZ);
        termGrp.rotation.y=Math.PI/2; // faces the player approaching from south

        // Back plate
        const termBodyMat=new THREE.MeshLambertMaterial({color:0x111008});
        const termBody=new THREE.Mesh(new THREE.BoxGeometry(2.8,4.0,0.22),termBodyMat);
        termBody.position.set(0,2.4,0); termGrp.add(termBody);

        // Outer frame/bezel
        const termFrameMat=new THREE.MeshLambertMaterial({color:0x2a200a});
        const termFrame=new THREE.Mesh(new THREE.BoxGeometry(3.1,4.3,0.15),termFrameMat);
        termFrame.position.set(0,2.4,-0.1); termGrp.add(termFrame);

        // Screen (glowing, starts dark red = locked)
        const termScreenMat=new THREE.MeshBasicMaterial({color:0x220008});
        const termScreen=new THREE.Mesh(new THREE.BoxGeometry(2.0,2.4,0.04),termScreenMat);
        termScreen.position.set(0,3.0,0.12); termGrp.add(termScreen);

        // Screen glow light (starts low, red)
        const termLight=new THREE.PointLight(0x440010,1.5,8);
        termLight.position.set(0,2.8,1.2); termGrp.add(termLight);

        // Button housing
        const btnHousingMat=new THREE.MeshLambertMaterial({color:0x1a1408});
        const btnHousing=new THREE.Mesh(new THREE.BoxGeometry(0.7,0.7,0.18),btnHousingMat);
        btnHousing.position.set(0,1.1,0.1); termGrp.add(btnHousing);

        // The physical button — red, protruding, can animate
        const termBtnMat=new THREE.MeshLambertMaterial({color:0xaa0000});
        const termBtn=new THREE.Mesh(new THREE.CylinderGeometry(0.22,0.22,0.14,16),termBtnMat);
        termBtn.rotation.x=Math.PI/2; termBtn.position.set(0,1.1,0.22); termGrp.add(termBtn);

        // LED strips on sides of screen
        const ledMat=new THREE.MeshBasicMaterial({color:0x880010});
        const ledL=new THREE.Mesh(new THREE.BoxGeometry(0.08,2.4,0.04),ledMat); ledL.position.set(-1.1,3.0,0.12); termGrp.add(ledL);
        const ledR=new THREE.Mesh(new THREE.BoxGeometry(0.08,2.4,0.04),ledMat); ledR.position.set(1.1,3.0,0.12); termGrp.add(ledR);

        scene.add(termGrp);

        // ================================================================
        //  ORBS
        // ================================================================
        const orbs=[], SAFE=20;
        let oAt=0;
        while(orbs.length<totalOrbs&&oAt<2000){
            oAt++;
            const cell=emptyCells[Math.floor(Math.random()*emptyCells.length)];
            const pos=getPos(cell.x,cell.z);
            if(Math.hypot(pos.x-startPos.x,pos.z-startPos.z)<SAFE) continue;
            let near=false;
            for(const o of orbs) if(Math.hypot(pos.x-o.position.x,pos.z-o.position.z)<20){near=true;break;}
            if(!near){
                const mat=new THREE.MeshBasicMaterial({color:0x00eeff});
                const orb=new THREE.Mesh(new THREE.SphereGeometry(0.45,10,10),mat);
                orb.position.set(pos.x,1.5,pos.z);
                // Floor ring for pickup clarity
                const rMat=new THREE.MeshBasicMaterial({color:0x00eeff,transparent:true,opacity:0.3,depthWrite:false});
                const ring=new THREE.Mesh(new THREE.RingGeometry(0.6,0.75,24),rMat);
                ring.rotation.x=-Math.PI/2; ring.position.y=-1.4; orb.add(ring);
                orb.userData.ringMat=rMat;
                const oL=new THREE.PointLight(0x00eeff,1.2,12); orb.add(oL);
                scene.add(orb); orbs.push(orb);
            }
        }

        // ================================================================
        //  ENEMIES — with AI state machine
        // ================================================================
        const ghostGeo=new THREE.SphereGeometry(1.2,12,12);
        const enemies=[];
        let eAt=0;
        while(enemies.length<8&&eAt<2000){
            eAt++;
            const eCell=emptyCells[Math.floor(Math.random()*emptyCells.length)];
            const ePos=getPos(eCell.x,eCell.z);
            if(Math.hypot(ePos.x-startPos.x,ePos.z-startPos.z)<40) continue;
            let near=false;
            for(const e of enemies) if(Math.hypot(ePos.x-e.position.x,ePos.z-e.position.z)<30){near=true;break;}
            if(!near){
                const mat=new THREE.MeshBasicMaterial({color:0xcc0000,transparent:true,opacity:0.75});
                const enemy=new THREE.Mesh(ghostGeo,mat); enemy.position.set(ePos.x,2.0,ePos.z);
                const pL=new THREE.PointLight(0xff0000,1.5,18); enemy.add(pL);
                enemy.userData={
                    state:'patrol', alertTimer:0, pathQueue:[], pathUpdateT:0,
                    targetPos:new THREE.Vector3(ePos.x,2.0,ePos.z),
                    lastGrid:{x:eCell.x,z:eCell.z}, lastKnownGrid:null,
                    light:pL, name:ENEMY_NAMES[enemies.length%ENEMY_NAMES.length]
                };
                scene.add(enemy); enemies.push(enemy);
            }
        }

        // AI helpers
        function triggerAlert(e){
            const ud=e.userData;
            if(ud.state==='alerted'){ud.alertTimer=ALERT_DURATION;return;}
            ud.state='alerted'; ud.alertTimer=ALERT_DURATION; ud.pathUpdateT=0;
            ud.light.intensity=5; e.material.color.setHex(0xff2200);
            playScreech();
        }
        function alertRadius(wx,wz,r){
            enemies.forEach(e=>{if(e.userData.state!=='alerted'&&Math.hypot(e.position.x-wx,e.position.z-wz)<r)triggerAlert(e);});
        }

        // ================================================================
        //  MENU & INPUT  (original — untouched)
        // ================================================================
        const uiContainer=document.getElementById('main-ui');
        const engageBtn=document.getElementById('engage-btn');
        const nameInput=document.getElementById('name-input');
        const bgText=document.getElementById('input-bg-text');

        const quotes=["The corridors are wide, but the paths are many.","Do not trust the geometry.","Cyan light is a guide, but also a trap."];
        document.getElementById('lore-text').innerText=`"${quotes[Math.floor(Math.random()*quotes.length)]}"`;

        nameInput.addEventListener('focus',()=>{if(!nameInput.value){bgText.innerHTML='<div class="dots"><span>.</span><span>.</span><span>.</span></div>';bgText.style.opacity='1';}});
        nameInput.addEventListener('blur',()=>{if(!nameInput.value){bgText.innerHTML='NAMETAG';bgText.style.opacity='1';}});
        nameInput.addEventListener('input',e=>{
            playUISound(90,1.2,0.25,'triangle');
            e.target.value=e.target.value.replace(/[^A-Za-z]/g,'').toUpperCase();
            if(nameInput.value.length>0) bgText.style.opacity='0';
            else{bgText.style.opacity='1';bgText.innerHTML='<div class="dots"><span>.</span><span>.</span><span>.</span></div>';}
        });
        nameInput.addEventListener('keydown',e=>e.stopPropagation());
        nameInput.addEventListener('keyup',e=>e.stopPropagation());

        document.querySelectorAll('#main-ui button,#main-ui input').forEach(el=>{
            el.addEventListener('mouseenter',()=>playUISound(500,0.5,0.08,'triangle'));
            if(el!==engageBtn) el.addEventListener('mousedown',()=>playUISound(180,1.5,0.2,'sine'));
            else el.addEventListener('mousedown',()=>playUISound(100,2.0,0.4,'sine'));
        });

        engageBtn.addEventListener('mousedown',()=>{
            const g=document.querySelector('.grid-container');
            g.classList.remove('shake-active'); void g.offsetWidth; g.classList.add('shake-active');
            document.body.requestPointerLock();
        });

        document.addEventListener('pointerlockchange',()=>{
            if(document.pointerLockElement===document.body){
                uiContainer.style.display='none'; gameActive=true;
                if(startTime===0) startTime=Date.now();
                prevTime=performance.now();
                // Intro fade sequence — one-time on first play
                if(!introShown){
                    introShown=true;
                    const name=nameInput.value||'OPERATIVE';
                    const fb=document.getElementById('fade-black');
                    fb.style.cssText='position:fixed;top:0;left:0;width:100%;height:100%;background:#000;z-index:200;opacity:1;display:flex;align-items:center;justify-content:center;pointer-events:none;transition:none;';
                    fb.innerHTML=`<div style="text-align:center;font-family:'Courier New',monospace;color:#c4a860;letter-spacing:4px;"><div style="font-size:1.5em;font-weight:bold;margin-bottom:8px;">OPERATIVE: ${name}</div><div style="font-size:0.75em;color:#5e4835;letter-spacing:6px;">SIGNAL LOCKED — DEPLOYING</div></div>`;
                    setTimeout(()=>{
                        fb.style.transition='opacity 1.5s ease-in-out'; fb.style.opacity='0';
                        setTimeout(()=>{fb.style.cssText='position:fixed;top:0;left:0;width:100%;height:100%;background:#000;opacity:0;z-index:105;transition:opacity 3s ease-in-out;pointer-events:none;';fb.innerHTML='';},1600);
                    },1500);
                }
            } else if(!gameWon){
                uiContainer.style.display='flex';
                document.getElementById('main-title').innerText='SYSTEM PAUSED';
                engageBtn.innerText='RESUME';
                gameActive=false;
                accumulatedTime+=(Date.now()-startTime)/1000;
                document.getElementById('menuOrbCount').innerText=orbsCollected;
                elPrompt.style.display='none';
            }
        });

        document.addEventListener('mousemove',e=>{
            if(document.pointerLockElement===document.body){
                yaw-=e.movementX*SENSITIVITY; pitch-=e.movementY*SENSITIVITY;
                pitch=Math.max(-Math.PI/2,Math.min(Math.PI/2,pitch));
                camera.rotation.set(pitch,yaw,0);
            }
        });

        document.addEventListener('keydown',e=>{
            keys[e.code]=true;
            // E — activate terminal
            if(e.code==='KeyE'&&gameActive&&!gameWon&&doorState==='ready_terminal'){
                const dist=Math.hypot(camera.position.x-TERM_WX,camera.position.z-TERM_WZ);
                if(dist<9){
                    terminalActivated=true; terminalButtonT=0.2;
                    // Button depresses
                    termBtn.position.z=0.08;
                    // Activate door sequence after short delay
                    termScreenMat.color.setHex(0xff4400); termLight.color.setHex(0xff6600); termLight.intensity=4;
                    ledMat.color.setHex(0xff4400); ledR.material.color.setHex(0xff4400);
                    playTerminalClick();
                    setTimeout(()=>{
                        doorState='valves_pressure';
                        initIndustrialAudio();
                        sirens.forEach(s=>s.light.intensity=50);
                        klaxonGain.gain.setTargetAtTime(0.015,audioCtx.currentTime,0.1);
                        hissGain.gain.setTargetAtTime(0.1,audioCtx.currentTime,0.1);
                    },600);
                }
            }
        });
        document.addEventListener('keyup',e=>keys[e.code]=false);

        // ================================================================
        //  UPDATE LOOP
        // ================================================================
        function update(){
            if(!gameActive) return;

            const now=performance.now();
            const delta=Math.min((now-prevTime)/1000,0.05); // clamp prevents large jumps after pause
            prevTime=now;
            const totalElapsed=(accumulatedTime+(Date.now()-startTime)/1000).toFixed(1);
            if(!gameWon) elTimeVal.innerText=totalElapsed;

            // Mark explored cells for radar
            const pg=worldToGrid(camera.position.x,camera.position.z);
            exploredCells.add(`${pg.x},${pg.z}`);

            // ---- PLAYER MOVEMENT (original logic, + footstep timing + sprint FOV) ----
            if(!gameWon){
                const input=new THREE.Vector2(0,0);
                if(keys['KeyW']) input.y-=1; if(keys['KeyS']) input.y+=1;
                if(keys['KeyA']) input.x-=1; if(keys['KeyD']) input.x+=1;
                if(input.length()>0) input.normalize();

                const moving=input.length()>0;
                const isSprinting=keys['ShiftLeft']&&moving&&!player.isExhausted;
                currentlySprinting=isSprinting;

                // Stamina
                if(isSprinting){player.stamina-=0.4;if(player.stamina<=0)player.isExhausted=true;}
                else{player.stamina=Math.min(MAX_STAMINA,player.stamina+0.9);if(player.stamina>=MAX_STAMINA*0.25)player.isExhausted=false;}
                const stPct=(player.stamina/MAX_STAMINA)*100;
                elStBar.style.height=stPct+'%'; // vertical bar — height not width
                elStBar.style.background=player.isExhausted?'#8b0000':'linear-gradient(to top, #7a5c00, #d4af37)';
                elStCont.classList.toggle('exhausted',player.isExhausted);

                // Flashlight flickers below 28% stamina
                flash.intensity=stPct<28 ? 80*(0.65+0.35*Math.abs(Math.sin(now*0.03+Math.sin(now*0.008)*3))) : 80;

                // Movement
                const spd=isSprinting?player.runSpeed:(moving?player.walkSpeed:0);
                const tv=input.clone().multiplyScalar(spd); player.velocity.lerp(tv,0.14);
                const mx=player.velocity.x*Math.cos(yaw)+player.velocity.y*Math.sin(yaw);
                const mz=-player.velocity.x*Math.sin(yaw)+player.velocity.y*Math.cos(yaw);
                let tx=camera.position.x, tz=camera.position.z;
                if(!isWall(tx+mx,tz,player.radius)) tx+=mx;
                if(!isWall(tx,tz+mz,player.radius)) tz+=mz;
                camera.position.x=tx; camera.position.z=tz;

                // Head bob + footstep sounds tied to bob cycle
                const spd2=player.velocity.length();
                if(spd2>0.02){
                    const hz=isSprinting?3.5:1.5, amp=isSprinting?0.11:0.07;
                    player.headBobTimer+=delta*hz*Math.PI*2;
                    camera.position.y=player.height+Math.sin(player.headBobTimer)*amp;
                    // Footstep fires at each half-bob minimum (floor of timer/PI changes)
                    const cycle=Math.floor(player.headBobTimer/Math.PI);
                    if(cycle>lastFootCycle){ lastFootCycle=cycle; playFootstep(isSprinting); }
                    // Sprint alerts nearby enemies
                    if(isSprinting){
                        sprintAlertCD-=delta;
                        if(sprintAlertCD<=0){sprintAlertCD=0.55;alertRadius(camera.position.x,camera.position.z,SPRINT_R);}
                    }
                } else {
                    camera.position.y+=(player.height-camera.position.y)*0.1;
                    player.headBobTimer+=delta;
                }

                // FOV expands when sprinting — tunnel rush effect
                const targetFOV=isSprinting?84:75;
                camera.fov+=(targetFOV-camera.fov)*0.09;
                camera.updateProjectionMatrix();
            }

            // ---- PARTICLES ----
            for(let i=particles.length-1;i>=0;i--){
                const p=particles[i]; p.position.addScaledVector(p.userData.vel,delta); p.userData.life-=delta;
                if(p.userData.type==='steam'){p.userData.mat.opacity=(p.userData.life/1.0)*0.4;p.scale.setScalar(2.0-p.userData.life);}
                else if(p.userData.type==='spark'){p.userData.vel.y-=delta*15;if(p.position.y<0.1){p.position.y=0.1;p.userData.vel.y*=-0.5;}}
                if(p.userData.life<=0){scene.remove(p);if(p.userData.type==='steam')p.userData.mat.dispose();particles.splice(i,1);}
            }

            // ---- CORRIDOR LIGHTS FLICKER ----
            for(const cl of corridorLights){
                if(cl.broken){
                    const t=now*0.001*cl.rate+cl.seed;
                    const f=Math.abs(Math.sin(t*7.4)*Math.sin(t*3.2));
                    cl.light.intensity=Math.random()>0.04?cl.base*f:0;
                } else {
                    cl.light.intensity=cl.base*(0.72+0.28*Math.sin(now*0.001*cl.rate+cl.seed));
                }
            }

            // Terminal button animation (spring back)
            if(terminalButtonT>0){
                terminalButtonT-=delta;
                if(terminalButtonT<=0) termBtn.position.z=0.22; // spring back
            }

            // ---- RADAR ----
            rCtx.clearRect(0,0,radarCanvas.width,radarCanvas.height);

            // Explored cell footprint
            rCtx.fillStyle='rgba(80,100,70,0.22)';
            exploredCells.forEach(k=>{
                const[gx,gz]=k.split(',').map(Number);
                const wp=getPos(gx,gz);
                const dx=wp.x-camera.position.x, dz=wp.z-camera.position.z;
                if(Math.hypot(dx,dz)>rMax) return;
                const lr=dx*Math.cos(yaw)-dz*Math.sin(yaw), lf=-dx*Math.sin(yaw)-dz*Math.cos(yaw);
                rCtx.fillRect(rC+lr*rScl-1.5,rC-lf*rScl-1.5,3,3);
            });

            // Grid lines
            rCtx.strokeStyle='rgba(140,160,130,0.12)'; rCtx.lineWidth=1;
            rCtx.beginPath(); rCtx.moveTo(rC,0); rCtx.lineTo(rC,radarCanvas.height);
            rCtx.moveTo(0,rC); rCtx.lineTo(radarCanvas.width,rC); rCtx.stroke();
            // Player arrow
            rCtx.fillStyle='rgba(200,180,140,0.7)';
            rCtx.beginPath(); rCtx.moveTo(rC,rC-7); rCtx.lineTo(rC-4,rC+5); rCtx.lineTo(rC+4,rC+5); rCtx.fill();

            function drawBlip(wx,wz,color,sz){
                const dx=wx-camera.position.x, dz=wz-camera.position.z;
                let lr=dx*Math.cos(yaw)-dz*Math.sin(yaw), lf=-dx*Math.sin(yaw)-dz*Math.cos(yaw);
                const d=Math.hypot(lr,lf);
                if(d>rMax){lr=(lr/d)*rMax;lf=(lf/d)*rMax;}
                const rx=rC+lr*rScl, ry=rC-lf*rScl;
                rCtx.fillStyle=color; rCtx.beginPath(); rCtx.arc(rx,ry,sz,0,Math.PI*2); rCtx.fill();
            }
            function drawDoorBlip(wx,wz){
                const dx=wx-camera.position.x, dz=wz-camera.position.z;
                let lr=dx*Math.cos(yaw)-dz*Math.sin(yaw), lf=-dx*Math.sin(yaw)-dz*Math.cos(yaw);
                const d=Math.hypot(lr,lf); if(d>rMax){lr=(lr/d)*rMax;lf=(lf/d)*rMax;}
                const rx=rC+lr*rScl, ry=rC-lf*rScl;
                rCtx.fillStyle='#448844'; rCtx.fillRect(rx-4,ry-6,8,12);
                rCtx.fillStyle='#112211'; rCtx.fillRect(rx-2.5,ry-4.5,5,10);
            }

            drawDoorBlip(doorGroup.position.x,doorGroup.position.z);
            // Terminal blip (cyan when ready)
            if(doorState==='ready_terminal') drawBlip(TERM_WX,TERM_WZ,'rgba(0,220,255,0.8)',3);
            orbs.forEach(o=>{if(o.position.y>0)drawBlip(o.position.x,o.position.z,'rgba(200,180,80,0.7)',2);});

            // ---- CROSSHAIR — near orb reaction ----
            let nearOrb=false;
            orbs.forEach(o=>{if(o.position.y>0&&camera.position.distanceTo(o.position)<6)nearOrb=true;});
            elCross.classList.toggle('nearby',nearOrb);

            // ---- ENEMY AI STATE MACHINE ----
            let closestDist=100;
            enemies.forEach((enemy,idx)=>{
                const ud=enemy.userData;
                const dist=camera.position.distanceTo(enemy.position);
                if(dist<closestDist) closestDist=dist;

                // Light detection — only when not already alerted
                if(ud.state!=='alerted'&&dist<LIGHT_RANGE){
                    const fwd=new THREE.Vector3(0,0,-1).applyQuaternion(camera.quaternion);
                    const toE=new THREE.Vector3().subVectors(enemy.position,camera.position).normalize();
                    if(fwd.dot(toE)>CONE_COS&&hasLOS(camera.position.x,camera.position.z,enemy.position.x,enemy.position.z))
                        triggerAlert(enemy);
                }

                // State machine
                if(ud.state==='alerted'){
                    ud.alertTimer-=delta; ud.light.intensity=5+Math.sin(now*0.012)*1.5;
                    if(ud.alertTimer<=0){ud.state='searching';ud.light.intensity=2.5;ud.pathUpdateT=0;}
                    else{
                        ud.pathUpdateT-=delta;
                        if(ud.pathUpdateT<=0){
                            ud.pathUpdateT=1.4;
                            const pg2=worldToGrid(camera.position.x,camera.position.z);
                            const eg=worldToGrid(enemy.position.x,enemy.position.z);
                            const path=bfsPath(eg.x,eg.z,pg2.x,pg2.z);
                            if(path.length>0){ud.pathQueue=path;ud.lastKnownGrid=pg2;}
                        }
                    }
                    // Radar — bright red when alerted
                    drawBlip(enemy.position.x,enemy.position.z,'rgba(255,30,30,0.9)',4);
                } else if(ud.state==='searching'){
                    ud.light.intensity=2.5;
                    if(ud.lastKnownGrid){
                        const lk=getPos(ud.lastKnownGrid.x,ud.lastKnownGrid.z);
                        if(Math.hypot(enemy.position.x-lk.x,enemy.position.z-lk.z)<TILE_SIZE*0.55){
                            ud.state='patrol'; ud.lastKnownGrid=null; ud.pathQueue=[]; ud.light.intensity=1.5;
                            enemy.material.color.setHex(0xcc0000);
                        } else {
                            ud.pathUpdateT-=delta;
                            if(ud.pathUpdateT<=0){
                                ud.pathUpdateT=2.0;
                                const eg=worldToGrid(enemy.position.x,enemy.position.z);
                                ud.pathQueue=bfsPath(eg.x,eg.z,ud.lastKnownGrid.x,ud.lastKnownGrid.z);
                            }
                        }
                    } else {ud.state='patrol'; ud.pathQueue=[];}
                    // Radar — orange when searching
                    drawBlip(enemy.position.x,enemy.position.z,'rgba(255,120,30,0.7)',3);
                } else {
                    // PATROL: original random wander
                    ud.light.intensity=1.5;
                    if(!gameWon&&enemy.position.distanceTo(ud.targetPos)<0.5){
                        const cx=Math.round(ud.targetPos.x/TILE_SIZE)+Math.floor(MAZE_SIZE/2);
                        const cz=Math.round(ud.targetPos.z/TILE_SIZE)+Math.floor(MAZE_SIZE/2);
                        const nb=[]; [[0,-1],[0,1],[-1,0],[1,0]].forEach(([dx2,dz2])=>{
                            const nx=cx+dx2,nz=cz+dz2;
                            if(nx>=0&&nx<MAZE_SIZE&&nz>=0&&nz<MAZE_SIZE&&maze[nx][nz]===0&&!(nx===ud.lastGrid.x&&nz===ud.lastGrid.z)) nb.push({x:nx,z:nz});
                        });
                        if(!nb.length&&maze[ud.lastGrid.x]&&maze[ud.lastGrid.x][ud.lastGrid.z]===0) nb.push(ud.lastGrid);
                        ud.lastGrid={x:cx,z:cz};
                        const nc=nb.length?nb[Math.floor(Math.random()*nb.length)]:ud.lastGrid;
                        ud.targetPos.set(getPos(nc.x,nc.z).x,2.0,getPos(nc.x,nc.z).z);
                    }
                    // Patrol enemies NOT shown on radar — no constant ping
                }

                // Follow BFS path (shared by alerted/searching)
                if(ud.pathQueue.length>0){
                    const nc=ud.pathQueue[0], nw=getPos(nc.x,nc.z);
                    const nPos=new THREE.Vector3(nw.x,2.0,nw.z);
                    if(enemy.position.distanceTo(nPos)<TILE_SIZE*0.45) ud.pathQueue.shift();
                    else ud.targetPos.copy(nPos);
                }

                // Move
                const moveSpd=ud.state==='alerted'?0.19:ud.state==='searching'?0.10:0.12;
                const dir=new THREE.Vector3().subVectors(ud.targetPos,enemy.position); dir.y=0;
                if(dir.length()>0.01){dir.normalize();enemy.position.addScaledVector(dir,moveSpd);}
                enemy.position.y=2.0+Math.sin(now*0.003+idx)*0.35;

                // Death check
                if(!gameWon&&dist<3.0&&gameActive){
                    gameActive=false; document.exitPointerLock();
                    const t=(accumulatedTime+(Date.now()-startTime)/1000).toFixed(1);
                    document.getElementById('time-stat').innerText=t+'s';
                    document.getElementById('orb-stat').innerText=`${orbsCollected} / 12`;
                    document.getElementById('death-screen-ui').style.display='block';
                }
            });

            // Proximity shake + sting
            if(!gameWon&&closestDist<12){
                camera.position.x+=(Math.random()-0.5)*((12-closestDist)*0.02);
                if(!hasPlayedSting){playSting();hasPlayedSting=true;}
            } else hasPlayedSting=false;

            // ---- ORB COLLECTION ----
            orbs.forEach(orb=>{
                if(!gameWon&&orb.position.y>0&&camera.position.distanceTo(orb.position)<3){
                    orb.position.y=-1000; orbsCollected++;
                    elOrbCount.innerText=orbsCollected;
                    alertRadius(orb.position.x,orb.position.z,18);
                    if(orbsCollected===totalOrbs&&doorState==='closed'){
                        doorState='ready_terminal';
                        // Terminal glows green to signal readiness
                        termScreenMat.color.setHex(0x002200);
                        termLight.color.setHex(0x00ff44); termLight.intensity=3.5;
                        ledMat.color.setHex(0x00aa22);
                        termBtnMat.color.setHex(0x00cc00);
                        playUISound(280,0.8,0.6,'sine');
                    }
                }
            });

            // ---- ORBS: pulse ring opacity ----
            orbs.forEach(orb=>{
                if(orb.position.y>0&&orb.userData.ringMat)
                    orb.userData.ringMat.opacity=0.2+0.15*Math.sin(now*0.005+orb.position.x);
            });

            // ---- TERMINAL PROXIMITY PROMPT ----
            if(gameActive&&!gameWon&&!terminalActivated){
                const dt=Math.hypot(camera.position.x-TERM_WX,camera.position.z-TERM_WZ);
                elPrompt.style.display=(doorState==='ready_terminal'&&dt<9)?'block':'none';
            }

            // Terminal light pulse when ready
            if(doorState==='ready_terminal'&&!terminalActivated)
                termLight.intensity=3.5+1.5*Math.sin(now*0.006);

            // ---- DOOR ANIMATION (original — untouched) ----
            if(!gameWon) camera.rotation.z=0;
            if(doorState!=='closed'&&doorState!=='open'&&doorState!=='ready_terminal'){
                const dtd=camera.position.distanceTo(doorGroup.position), vs=Math.max(0,1-dtd/50);
                sirens.forEach((s,i)=>s.group.rotation.y+=delta*(i%2===0?2:-2));
                if(klaxonGain) klaxonGain.gain.setTargetAtTime(vs*0.015,audioCtx.currentTime,0.1);
                if(!gameWon&&dtd<45){const si=(45-dtd)*0.0015;camera.rotation.z=(Math.random()-0.5)*si;}

                if(doorState==='valves_pressure'){
                    if(valves[0].rotation.z<Math.PI*4){
                        valves.forEach(v=>v.rotation.z+=delta*Math.PI);
                        if(Math.random()>0.5) emitSteam(doorGroup.position.x,1,doorGroup.position.z);
                        if(hissGain) hissGain.gain.setTargetAtTime(vs*0.1,audioCtx.currentTime,0.1);
                    } else {
                        doorState='vault_unlock';
                        if(hissGain) hissGain.gain.setTargetAtTime(0,audioCtx.currentTime,0.1);
                        if(vaultGain) vaultGain.gain.setTargetAtTime(vs*0.04,audioCtx.currentTime,0.1);
                    }
                } else if(doorState==='vault_unlock'){
                    if(vaultWG.rotation.z<Math.PI){
                        vaultWG.rotation.z+=delta*(Math.PI/5); vaultWG.position.x-=delta*0.2;
                        if(vaultGain) vaultGain.gain.setTargetAtTime(vs*0.04,audioCtx.currentTime,0.1);
                    } else {
                        doorState='unlatching'; matIndicator.color.setHex(0x00ff00);
                        if(vaultGain) vaultGain.gain.setTargetAtTime(0,audioCtx.currentTime,0.1);
                        if(latchGain) latchGain.gain.setTargetAtTime(vs*0.06,audioCtx.currentTime,0.1);
                    }
                } else if(doorState==='unlatching'){
                    if(latchL.position.x>-6){
                        const ls=delta*0.5; latchL.position.x-=ls; latchR.position.x+=ls;
                        deadboltsL.forEach(b=>b.position.x-=ls*3); deadboltsR.forEach(b=>b.position.x+=ls*3);
                        if(latchGain) latchGain.gain.setTargetAtTime(vs*0.06,audioCtx.currentTime,0.1);
                    } else {
                        doorState='retracting_pistons';
                        if(latchGain) latchGain.gain.setTargetAtTime(0,audioCtx.currentTime,0.1);
                        if(pistonGain) pistonGain.gain.setTargetAtTime(vs*0.15,audioCtx.currentTime,0.1);
                    }
                } else if(doorState==='retracting_pistons'){
                    if(pistonGrp.position.y<5){
                        pistonGrp.position.y+=delta*1.0;
                        if(pistonGain) pistonGain.gain.setTargetAtTime(vs*0.15,audioCtx.currentTime,0.1);
                    } else {
                        doorState='sliding';
                        if(pistonGain) pistonGain.gain.setTargetAtTime(0,audioCtx.currentTime,0.1);
                        if(gearGain) gearGain.gain.setTargetAtTime(vs*0.08,audioCtx.currentTime,0.1);
                    }
                } else if(doorState==='sliding'){
                    if(doorHL.position.x>-PW-2){
                        const sl=delta*0.444;
                        doorHL.position.x-=sl; doorHR.position.x+=sl;
                        const gr=sl/GR; mgL.rotation.z-=gr; mgR.rotation.z+=gr;
                        const hr=GR/HGR; hgL.rotation.z+=gr*hr; hgR.rotation.z-=gr*hr;
                        if(Math.random()>0.4) emitSpark(doorGroup.position.x-3,11+GR,doorGroup.position.z-0.8);
                        if(Math.random()>0.4) emitSpark(doorGroup.position.x+3,11+GR,doorGroup.position.z-0.8);
                        if(gearGain) gearGain.gain.setTargetAtTime(vs*0.08,audioCtx.currentTime,0.1);
                    } else {
                        doorState='open'; sirens.forEach(s=>s.light.intensity=0); matGlassRed.color.setHex(0x110000);
                        const fot=audioCtx.currentTime+1.5;
                        if(klaxonGain) klaxonGain.gain.linearRampToValueAtTime(0,fot);
                        if(gearGain) gearGain.gain.linearRampToValueAtTime(0,fot);
                    }
                }
            }

            // ---- WIN ----
            if(doorState==='open'&&camera.position.z>doorGroup.position.z+1.5&&!gameWon){
                gameWon=true; document.exitPointerLock();
                const ws=document.getElementById('win-screen');
                const fb=document.getElementById('fade-black');
                ws.style.display='flex';
                setTimeout(()=>{fb.style.opacity='1';ws.style.opacity='1';},50);
                document.getElementById('finalTime').innerText=`FINAL TIME: ${totalElapsed}s`;
                elPrompt.style.display='none';
                try{if(klaxonOsc)klaxonOsc.stop();if(latchOsc)latchOsc.stop();if(pistonOsc)pistonOsc.stop();if(gearOsc)gearOsc.stop();if(vaultOsc)vaultOsc.stop();if(hissSrc)hissSrc.stop();}catch(_){}
            }
        }

        function animate(){ requestAnimationFrame(animate); update(); renderer.render(scene,camera); }
        animate();

        window.addEventListener('resize',()=>{
            camera.aspect=innerWidth/innerHeight; camera.updateProjectionMatrix();
            renderer.setSize(innerWidth,innerHeight);
        });

        document.getElementById('reboot-btn').addEventListener('click',()=>{
            const d=document.getElementById('death-screen-ui');
            d.style.transition='opacity 0.5s'; d.style.opacity='0';
            setTimeout(()=>location.reload(),500);
        });
