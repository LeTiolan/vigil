import * as THREE from 'three';

// ================================================================
// MAZE GENERATION  (runs before any THREE geometry so no ordering issues)
// ================================================================
const MAZE_SIZE = 25, TILE_SIZE = 12;
const maze = Array(MAZE_SIZE).fill(null).map(() => Array(MAZE_SIZE).fill(1));
const emptyCells = [];

function carveMaze(x, y) {
    maze[x][y] = 0;
    const dirs = [[0,-1],[0,1],[-1,0],[1,0]].sort(() => Math.random() - 0.5);
    for (const [dx, dy] of dirs) {
        const nx = x + dx*2, ny = y + dy*2;
        if (nx>0 && nx<MAZE_SIZE-1 && ny>0 && ny<MAZE_SIZE-1 && maze[nx][ny]===1) {
            maze[x+dx][y+dy] = 0; carveMaze(nx, ny);
        }
    }
}
carveMaze(1,1);
for (let i=1;i<MAZE_SIZE-1;i++) for (let j=1;j<MAZE_SIZE-1;j++)
    if (maze[i][j]===1 && ((maze[i-1][j]===0&&maze[i+1][j]===0)||(maze[i][j-1]===0&&maze[i][j+1]===0)) && Math.random()<0.25) maze[i][j]=0;

const exitGridX = Math.floor(MAZE_SIZE/2), exitGridZ = MAZE_SIZE-1;
for (let i=-1;i<=1;i++) for (let j=-3;j<=-1;j++) maze[exitGridX+i][exitGridZ+j]=0;
maze[exitGridX][exitGridZ]=0;
for (let i=0;i<MAZE_SIZE;i++) for (let j=0;j<MAZE_SIZE;j++) if (maze[i][j]===0) emptyCells.push({x:i,z:j});

// ================================================================
// UTILITY FUNCTIONS
// ================================================================
function getPos(i, j) {
    return { x: (i - Math.floor(MAZE_SIZE/2))*TILE_SIZE, z: (j - Math.floor(MAZE_SIZE/2))*TILE_SIZE };
}
function worldToGrid(wx, wz) {
    const o = Math.floor(MAZE_SIZE/2);
    return { x: Math.max(0,Math.min(MAZE_SIZE-1, Math.round(wx/TILE_SIZE)+o)), z: Math.max(0,Math.min(MAZE_SIZE-1, Math.round(wz/TILE_SIZE)+o)) };
}

// BFS using parent-map reconstruction — O(n) memory, not O(n²)
function bfsPath(sx, sz, gx, gz) {
    if (sx===gx && sz===gz) return [];
    const q = [{x:sx,z:sz}];
    const parent = new Map();
    parent.set(`${sx},${sz}`, null);
    let it = 0;
    while (q.length && it++ < 2000) {
        const {x,z} = q.shift();
        for (const [dx,dz] of [[0,-1],[0,1],[-1,0],[1,0]]) {
            const nx=x+dx, nz=z+dz, k=`${nx},${nz}`;
            if (nx<0||nx>=MAZE_SIZE||nz<0||nz>=MAZE_SIZE) continue;
            if (maze[nx][nz]!==0 || parent.has(k)) continue;
            parent.set(k, `${x},${z}`);
            if (nx===gx && nz===gz) {
                // Reconstruct path from parent map
                const path = [];
                let cur = k;
                while (cur) {
                    const [px,pz] = cur.split(',').map(Number);
                    path.unshift({x:px,z:pz});
                    cur = parent.get(cur);
                }
                path.shift(); // remove start node
                return path;
            }
            q.push({x:nx,z:nz});
        }
    }
    return [];
}

function hasLOS(ax, az, bx, bz) {
    const g0=worldToGrid(ax,az), g1=worldToGrid(bx,bz);
    const steps=Math.max(Math.abs(g1.x-g0.x),Math.abs(g1.z-g0.z));
    if (steps===0) return true;
    for (let i=1;i<steps;i++) {
        const t=i/steps, cx=Math.round(g0.x+(g1.x-g0.x)*t), cz=Math.round(g0.z+(g1.z-g0.z)*t);
        if (cx>=0&&cx<MAZE_SIZE&&cz>=0&&cz<MAZE_SIZE&&maze[cx][cz]===1) return false;
    }
    return true;
}

function formatTime(secs) {
    const f=parseFloat(secs), m=Math.floor(f/60), s=Math.floor(f%60), ms=Math.round((f%1)*10);
    return `${String(m).padStart(2,'0')}:${String(s).padStart(2,'0')}.${ms}`;
}

// ================================================================
// CONSTANTS
// ================================================================
const TOTAL_ORBS       = 12;
const MAX_STAMINA      = 200;
const ALERT_DURATION   = 12.0;
const LIGHT_RANGE      = 38;
const FLASH_CONE_COS   = Math.cos(65 * Math.PI/180); // flashlight half-cone in dot-product space
const SPRINT_ALERT_R   = 28;
const ORB_ALERT_R      = 22;
const ENEMY_NAMES      = ['REVENANT','UNIT-07','SPECTER-X','THE HOLLOW','SHADE-03','REMNANT','ECHO-NULL','VOID-TRACE'];

// ================================================================
// GAME STATE  (only primitive values at top level — no THREE refs)
// ================================================================
let orbsCollected=0, gameActive=false, gameWon=false;
let startTime=0, accumulatedTime=0, hasPlayedSting=false, prevTime=performance.now();
let yaw=Math.PI, pitch=0;
const SENSITIVITY=0.002;
let prevYaw=Math.PI, leanAngle=0, doorShakeZ=0;
let currentlySprinting=false, introPlayed=false;
let sprintAlertCooldown=0, sprintBreathStep=0;
let lastKnownPos=null, lastKnownTime=0;
const echoPositions=[]; // sprint footstep echo trail (last 3)
const exploredCells=new Set();
let ceilingDripTimer=3+Math.random()*3;
let orbFlashTimeout=null;
const keys={};

// Player as plain object with scalar velocity — avoids any THREE dependency at top level
const player={
    height:2.1, radius:0.8, walkSpeed:0.22, runSpeed:0.48,
    stamina:MAX_STAMINA, isExhausted:false,
    velX:0, velZ:0, // replaces THREE.Vector2 to avoid init-order issues
    headBobTimer:0, lastFootstepCycle:0
};

// ================================================================
// SCENE, RENDERER, CAMERA  (after all primitives so THREE is definitely loaded)
// ================================================================
const scene  = new THREE.Scene();
scene.background = new THREE.Color(0x0c121a);
scene.fog = new THREE.Fog(0x0c121a, 15, 120);

const camera = new THREE.PerspectiveCamera(75, window.innerWidth/window.innerHeight, 0.1, 1000);
camera.rotation.order = 'YXZ';

const renderer = new THREE.WebGLRenderer({antialias:true});
renderer.setSize(window.innerWidth, window.innerHeight);
renderer.shadowMap.enabled = true;
renderer.shadowMap.type = THREE.PCFSoftShadowMap;
document.body.appendChild(renderer.domElement);

// Lights
const hemiLight = new THREE.HemisphereLight(0xffffff,0x444444,0.6);
scene.add(hemiLight);
const flashLight = new THREE.SpotLight(0xffffe6,50.0,500,Math.PI/5,0.6,1.0);
flashLight.castShadow=true; flashLight.shadow.bias=-0.001;
camera.add(flashLight);
camera.add(flashLight.target);
flashLight.target.position.set(0,0,-1);
scene.add(camera);

// DOM ref for totalOrbs (DOM is ready since module scripts are deferred)
document.getElementById('totalOrbsUI').innerText = TOTAL_ORBS;

// ================================================================
// AUDIO ENGINE
// ================================================================
const audioCtx = new (window.AudioContext||window.webkitAudioContext)();
let klaxonOsc,klaxonGain,vaultOsc,vaultGain,latchOsc,latchGain;
let pistonOsc,pistonGain,gearOsc,gearGain,hissSrc,hissGain;
let ambientGain,breathGain,growlGain,ambientStarted=false;

function resumeAudio(){ if(audioCtx.state==='suspended') audioCtx.resume(); }

function makeNoise(sec){
    const sz=Math.floor(audioCtx.sampleRate*sec);
    const b=audioCtx.createBuffer(1,sz,audioCtx.sampleRate);
    const d=b.getChannelData(0);
    for(let i=0;i<sz;i++) d[i]=Math.random()*2-1;
    return b;
}

function initIndustrialAudio(){
    resumeAudio();
    klaxonOsc=audioCtx.createOscillator(); klaxonOsc.type='triangle'; klaxonOsc.frequency.value=450;
    const kLFO=audioCtx.createOscillator(); kLFO.frequency.value=2;
    const kMod=audioCtx.createGain(); kMod.gain.value=150;
    kLFO.connect(kMod); kMod.connect(klaxonOsc.frequency); kLFO.start();
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
    const pf=audioCtx.createBiquadFilter(); pf.type='lowpass'; pf.frequency.value=150;
    pistonOsc.connect(pf); pf.connect(pistonGain); pistonGain.connect(audioCtx.destination); pistonOsc.start();
    gearOsc=audioCtx.createOscillator(); gearOsc.type='square'; gearOsc.frequency.value=18;
    gearGain=audioCtx.createGain(); gearGain.gain.value=0;
    gearOsc.connect(gearGain); gearGain.connect(audioCtx.destination); gearOsc.start();
    const hn=audioCtx.createBufferSource(); hn.buffer=makeNoise(2); hn.loop=true;
    const hf=audioCtx.createBiquadFilter(); hf.type='highpass'; hf.frequency.value=1000;
    hissGain=audioCtx.createGain(); hissGain.gain.value=0;
    hn.connect(hf); hf.connect(hissGain); hissGain.connect(audioCtx.destination); hn.start(); hissSrc=hn;
}

function startAmbient(){
    if(ambientStarted) return; ambientStarted=true; resumeAudio();
    // Drone
    ambientGain=audioCtx.createGain(); ambientGain.gain.setValueAtTime(0,audioCtx.currentTime);
    for(const f of[40.0,41.4,80.7]){const o=audioCtx.createOscillator();o.type='sine';o.frequency.value=f;o.connect(ambientGain);o.start();}
    const sw=audioCtx.createOscillator(); sw.frequency.value=0.07;
    const sg=audioCtx.createGain(); sg.gain.value=0.007;
    sw.connect(sg); sg.connect(ambientGain.gain); sw.start();
    ambientGain.connect(audioCtx.destination);
    ambientGain.gain.linearRampToValueAtTime(0.045, audioCtx.currentTime+4);
    // Proximity breath
    const bs=audioCtx.createBufferSource(); bs.buffer=makeNoise(2); bs.loop=true;
    const bp=audioCtx.createBiquadFilter(); bp.type='bandpass'; bp.frequency.value=260; bp.Q.value=4;
    const tr=audioCtx.createOscillator(); tr.frequency.value=5.5;
    const tg=audioCtx.createGain(); tg.gain.value=0; tr.connect(tg);
    breathGain=audioCtx.createGain(); breathGain.gain.value=0; tg.connect(breathGain.gain);
    tr.start(); bs.start(); bs.connect(bp); bp.connect(breathGain); breathGain.connect(audioCtx.destination);
    // Enemy growl
    const gs=audioCtx.createBufferSource(); gs.buffer=makeNoise(2); gs.loop=true;
    const gf=audioCtx.createBiquadFilter(); gf.type='lowpass'; gf.frequency.value=120;
    const gl=audioCtx.createOscillator(); gl.frequency.value=3.2;
    const gg=audioCtx.createGain(); gg.gain.value=0; gl.connect(gg);
    growlGain=audioCtx.createGain(); growlGain.gain.value=0; gg.connect(growlGain.gain);
    gl.start(); gs.start(); gs.connect(gf); gf.connect(growlGain); growlGain.connect(audioCtx.destination);
}

function playFootstep(sprint){
    resumeAudio();
    const sz=Math.floor(audioCtx.sampleRate*0.045);
    const b=audioCtx.createBuffer(1,sz,audioCtx.sampleRate); const d=b.getChannelData(0);
    for(let i=0;i<sz;i++) d[i]=(Math.random()*2-1)*Math.pow(1-i/sz,5);
    const s=audioCtx.createBufferSource(); s.buffer=b;
    const f=audioCtx.createBiquadFilter(); f.type='lowpass'; f.frequency.value=sprint?750:460;
    const g=audioCtx.createGain(); g.gain.value=sprint?0.55:0.32;
    s.connect(f); f.connect(g); g.connect(audioCtx.destination); s.start();
}
function playSprintBreath(){
    resumeAudio();
    const sz=Math.floor(audioCtx.sampleRate*0.065);
    const b=audioCtx.createBuffer(1,sz,audioCtx.sampleRate); const d=b.getChannelData(0);
    for(let i=0;i<sz;i++) d[i]=(Math.random()*2-1)*Math.pow(1-i/sz,2);
    const s=audioCtx.createBufferSource(); s.buffer=b;
    const f=audioCtx.createBiquadFilter(); f.type='bandpass'; f.frequency.value=380; f.Q.value=1.5;
    const g=audioCtx.createGain(); g.gain.value=0.22;
    s.connect(f); f.connect(g); g.connect(audioCtx.destination); s.start();
}
function playChime(freqs,ivl){
    resumeAudio();
    freqs.forEach((freq,i)=>{
        const o=audioCtx.createOscillator(),g=audioCtx.createGain();
        o.type='triangle'; o.frequency.value=freq;
        const t=audioCtx.currentTime+i*ivl;
        g.gain.setValueAtTime(0,t); g.gain.linearRampToValueAtTime(0.28,t+0.01); g.gain.exponentialRampToValueAtTime(0.001,t+0.22);
        o.connect(g); g.connect(audioCtx.destination); o.start(t); o.stop(t+0.22);
    });
}
function playGoldChime(){
    resumeAudio();
    [330,495,660,880,1100].forEach((freq,i)=>{
        const o=audioCtx.createOscillator(),g=audioCtx.createGain(); o.type='sine'; o.frequency.value=freq;
        const t=audioCtx.currentTime+i*0.07;
        g.gain.setValueAtTime(0,t); g.gain.linearRampToValueAtTime(0.22,t+0.01); g.gain.exponentialRampToValueAtTime(0.001,t+0.3);
        o.connect(g); g.connect(audioCtx.destination); o.start(t); o.stop(t+0.3);
    });
}
function playScreech(){
    resumeAudio();
    const o=audioCtx.createOscillator(),g=audioCtx.createGain(); o.type='sawtooth';
    o.frequency.setValueAtTime(280,audioCtx.currentTime); o.frequency.exponentialRampToValueAtTime(60,audioCtx.currentTime+0.4);
    g.gain.setValueAtTime(0.18,audioCtx.currentTime); g.gain.exponentialRampToValueAtTime(0.001,audioCtx.currentTime+0.4);
    o.connect(g); g.connect(audioCtx.destination); o.start(); o.stop(audioCtx.currentTime+0.4);
}
function playDrip(vol){
    resumeAudio();
    const sz=Math.floor(audioCtx.sampleRate*0.03);
    const b=audioCtx.createBuffer(1,sz,audioCtx.sampleRate); const d=b.getChannelData(0);
    for(let i=0;i<sz;i++) d[i]=(Math.random()*2-1)*Math.pow(1-i/sz,8);
    const s=audioCtx.createBufferSource(); s.buffer=b;
    const f=audioCtx.createBiquadFilter(); f.type='highpass'; f.frequency.value=1200+Math.random()*400;
    const g=audioCtx.createGain(); g.gain.value=vol*0.4;
    s.connect(f); f.connect(g); g.connect(audioCtx.destination); s.start();
}
function playSting(){
    resumeAudio();
    const o=audioCtx.createOscillator(),g=audioCtx.createGain(); o.type='sawtooth';
    o.frequency.setValueAtTime(120,audioCtx.currentTime); o.frequency.exponentialRampToValueAtTime(30,audioCtx.currentTime+1);
    g.gain.setValueAtTime(0.2,audioCtx.currentTime); g.gain.exponentialRampToValueAtTime(0.01,audioCtx.currentTime+1);
    o.connect(g); g.connect(audioCtx.destination); o.start(); o.stop(audioCtx.currentTime+1);
}
function playUI(freq,vol,dur,type='triangle'){
    resumeAudio();
    const o=audioCtx.createOscillator(),g=audioCtx.createGain(); o.type=type;
    o.frequency.setValueAtTime(freq,audioCtx.currentTime); o.frequency.exponentialRampToValueAtTime(freq/2,audioCtx.currentTime+dur);
    g.gain.setValueAtTime(vol,audioCtx.currentTime); g.gain.exponentialRampToValueAtTime(0.001,audioCtx.currentTime+dur);
    o.connect(g); g.connect(audioCtx.destination); o.start(); o.stop(audioCtx.currentTime+dur);
}

// ================================================================
// PROCEDURAL TEXTURES
// ================================================================
function makeStoneTex(){
    const c=document.createElement('canvas'); c.width=512; c.height=512;
    const ctx=c.getContext('2d'); const bW=128,bH=64;
    ctx.fillStyle='#1b2d1b'; ctx.fillRect(0,0,512,512);
    for(let row=0;row<8;row++) for(let col=-1;col<5;col++){
        const ox=(row%2===0)?0:bW/2, bx=col*bW+ox, by=row*bH;
        const sh=Math.floor(Math.random()*16);
        ctx.fillStyle=`rgb(${24+sh},${44+sh},${24+sh})`; ctx.fillRect(bx+3,by+3,bW-6,bH-6);
        for(let i=0;i<60;i++){ctx.fillStyle=`rgba(0,0,0,${Math.random()*0.18})`;ctx.fillRect(bx+3+Math.random()*(bW-6),by+3+Math.random()*(bH-6),Math.random()*6+1,Math.random()*6+1);}
        if(Math.random()>0.55){const sx=bx+10+Math.random()*(bW-20);const gr=ctx.createLinearGradient(sx,by,sx+2,by+bH);gr.addColorStop(0,'rgba(90,42,8,0)');gr.addColorStop(0.3,'rgba(95,46,8,0.4)');gr.addColorStop(1,'rgba(70,32,5,0)');ctx.fillStyle=gr;ctx.fillRect(sx,by,4,bH);}
        ctx.fillStyle='rgba(255,255,255,0.03)'; ctx.fillRect(bx+3,by+3,bW-6,3);
    }
    ctx.strokeStyle='#091209'; ctx.lineWidth=3;
    for(let r=0;r<=8;r++){ctx.beginPath();ctx.moveTo(0,r*bH);ctx.lineTo(512,r*bH);ctx.stroke();}
    for(let r=0;r<8;r++){const ox=(r%2===0)?0:bW/2;for(let col=-1;col<=5;col++){const bx=col*bW+ox;ctx.beginPath();ctx.moveTo(bx,r*bH);ctx.lineTo(bx,(r+1)*bH);ctx.stroke();}}
    const t=new THREE.CanvasTexture(c); t.wrapS=t.wrapT=THREE.RepeatWrapping; t.repeat.set(1,1.2); return t;
}
function makeFloorTex(){
    const c=document.createElement('canvas'); c.width=512; c.height=512;
    const ctx=c.getContext('2d'); const ps=128;
    ctx.fillStyle='#161616'; ctx.fillRect(0,0,512,512);
    for(let r=0;r<4;r++) for(let col=0;col<4;col++){
        const sh=Math.floor(Math.random()*14);
        ctx.fillStyle=`rgb(${26+sh},${26+sh},${28+sh})`; ctx.fillRect(col*ps+2,r*ps+2,ps-4,ps-4);
        for(const [sx,sy] of[[col*ps+9,r*ps+9],[col*ps+ps-9,r*ps+9],[col*ps+9,r*ps+ps-9],[col*ps+ps-9,r*ps+ps-9]]){
            ctx.fillStyle='#272727'; ctx.beginPath(); ctx.arc(sx,sy,5.5,0,Math.PI*2); ctx.fill();
            ctx.fillStyle='#0f0f0f'; ctx.beginPath(); ctx.arc(sx,sy,2.8,0,Math.PI*2); ctx.fill();
            ctx.strokeStyle='#333'; ctx.lineWidth=1.2;
            ctx.beginPath(); ctx.moveTo(sx-3,sy); ctx.lineTo(sx+3,sy); ctx.stroke();
            ctx.beginPath(); ctx.moveTo(sx,sy-3); ctx.lineTo(sx,sy+3); ctx.stroke();
        }
        for(let i=0;i<18;i++){ctx.fillStyle=`rgba(0,0,0,${Math.random()*0.12})`;ctx.fillRect(col*ps+Math.random()*ps,r*ps+Math.random()*ps,Math.random()*22+2,Math.random()*2+1);}
        ctx.fillStyle='rgba(255,255,255,0.025)'; ctx.fillRect(col*ps+2,r*ps+2,ps-4,2);
    }
    ctx.strokeStyle='#0d0d0d'; ctx.lineWidth=3;
    for(let i=0;i<=4;i++){ctx.beginPath();ctx.moveTo(i*ps,0);ctx.lineTo(i*ps,512);ctx.stroke();ctx.beginPath();ctx.moveTo(0,i*ps);ctx.lineTo(512,i*ps);ctx.stroke();}
    const t=new THREE.CanvasTexture(c); t.wrapS=t.wrapT=THREE.RepeatWrapping; t.repeat.set(7,7); return t;
}
function makeGrimeTex(){
    const c=document.createElement('canvas'); c.width=512; c.height=512; const ctx=c.getContext('2d');
    ctx.fillStyle='#2a2a2a'; ctx.fillRect(0,0,512,512);
    for(let i=0;i<10000;i++){ctx.fillStyle=Math.random()>0.5?'rgba(0,0,0,0.1)':'rgba(80,60,40,0.1)';ctx.beginPath();ctx.arc(Math.random()*512,Math.random()*512,Math.random()*4,0,Math.PI*2);ctx.fill();}
    const t=new THREE.CanvasTexture(c); t.wrapS=t.wrapT=THREE.RepeatWrapping; t.repeat.set(2,2); return t;
}
function makeHazardTex(){
    const c=document.createElement('canvas'); c.width=256; c.height=256; const ctx=c.getContext('2d');
    ctx.fillStyle='#d4af37'; ctx.fillRect(0,0,256,256); ctx.fillStyle='#111';
    for(let i=-256;i<512;i+=64){ctx.beginPath();ctx.moveTo(i,0);ctx.lineTo(i+32,0);ctx.lineTo(i+288,256);ctx.lineTo(i+256,256);ctx.fill();}
    const t=new THREE.CanvasTexture(c); t.wrapS=t.wrapT=THREE.RepeatWrapping; return t;
}

// ================================================================
// MATERIALS
// ================================================================
const matDarkMetal   = new THREE.MeshStandardMaterial({map:makeGrimeTex(),metalness:0.8,roughness:0.7});
const matRustyFrame  = new THREE.MeshStandardMaterial({color:0x3d352b,metalness:0.9,roughness:0.9});
const matBrightSteel = new THREE.MeshStandardMaterial({color:0xaaaaaa,metalness:1.0,roughness:0.2});
const matHazard      = new THREE.MeshStandardMaterial({map:makeHazardTex(),metalness:0.3,roughness:0.8});
const matWarnYellow  = new THREE.MeshStandardMaterial({color:0xffaa00,metalness:0.4,roughness:0.7});
const matBlackHole   = new THREE.MeshStandardMaterial({color:0x030303,roughness:1.0});
const matGlassRed    = new THREE.MeshStandardMaterial({color:0xff0000,emissive:new THREE.Color(0x550000),transparent:true,opacity:0.8});
const matIndicator   = new THREE.MeshBasicMaterial({color:0xff0000});
const matPipe        = new THREE.MeshStandardMaterial({color:0x4a3828,metalness:0.8,roughness:0.5});

// ================================================================
// PARTICLES
// ================================================================
const particles=[];
const sparkGeo=new THREE.BoxGeometry(0.1,0.1,0.1);
const sparkMat=new THREE.MeshBasicMaterial({color:0xffaa00});
const steamGeoBase=new THREE.PlaneGeometry(1.5,1.5);
const steamMatBase=new THREE.MeshBasicMaterial({color:0xdddddd,transparent:true,opacity:0.5,depthWrite:false});

function emitSpark(x,y,z){
    const m=new THREE.Mesh(sparkGeo,sparkMat); m.position.set(x,y,z);
    m.userData={vel:new THREE.Vector3((Math.random()-0.5)*5,Math.random()*5+2,(Math.random()-0.5)*5),life:1.0,type:'spark'};
    scene.add(m); particles.push(m);
}
function emitSteam(x,y,z){
    const mat=steamMatBase.clone(); const m=new THREE.Mesh(steamGeoBase,mat); m.position.set(x,y,z);
    m.userData={vel:new THREE.Vector3((Math.random()-0.5)*1.5,Math.random()*2+1,(Math.random()-0.5)*1.5),life:1.0,type:'steam',mat};
    scene.add(m); particles.push(m);
}
function emitAfterimage(x,y,z){
    const mat=new THREE.MeshBasicMaterial({color:0xff1100,transparent:true,opacity:0.3,depthWrite:false});
    const m=new THREE.Mesh(new THREE.SphereGeometry(1.2,8,8),mat); m.position.set(x,y,z);
    m.userData={life:0.55,type:'afterimage',mat};
    scene.add(m); particles.push(m);
}

// ================================================================
// COLLISION SYSTEM
// ================================================================
const solidDoorParts=[];
const partBox=new THREE.Box3();
function registerSolid(mesh){ solidDoorParts.push(mesh); }

function isWall(x,z,r){
    const off=Math.floor(MAZE_SIZE/2);
    const x0=Math.floor((x-r+TILE_SIZE/2)/TILE_SIZE)+off-1, x1=Math.floor((x+r+TILE_SIZE/2)/TILE_SIZE)+off+1;
    const z0=Math.floor((z-r+TILE_SIZE/2)/TILE_SIZE)+off-1, z1=Math.floor((z+r+TILE_SIZE/2)/TILE_SIZE)+off+1;
    for(let i=x0;i<=x1;i++) for(let j=z0;j<=z1;j++){
        if(i<0||i>=MAZE_SIZE||j<0||j>=MAZE_SIZE||maze[i][j]!==1) continue;
        const wcx=(i-off)*TILE_SIZE, wcz=(j-off)*TILE_SIZE;
        const cx=Math.max(wcx-TILE_SIZE/2,Math.min(x,wcx+TILE_SIZE/2));
        const cz=Math.max(wcz-TILE_SIZE/2,Math.min(z,wcz+TILE_SIZE/2));
        if((x-cx)*(x-cx)+(z-cz)*(z-cz)<r*r) return true;
    }
    if(Math.abs(x-doorGroup.position.x)<TILE_SIZE&&Math.abs(z-doorGroup.position.z)<TILE_SIZE){
        const pb=new THREE.Box3(new THREE.Vector3(x-r,0,z-r),new THREE.Vector3(x+r,player.height,z+r));
        for(const sp of solidDoorParts){partBox.setFromObject(sp);if(pb.intersectsBox(partBox))return true;}
    }
    return false;
}

// ================================================================
// GEAR FACTORY
// ================================================================
function makeGear(radius,depth,teeth){
    const g=new THREE.Group();
    const core=new THREE.Mesh(new THREE.CylinderGeometry(radius*0.85,radius*0.85,depth,16),matBrightSteel);
    core.rotation.x=Math.PI/2; core.castShadow=true; g.add(core);
    const tGeo=new THREE.BoxGeometry((Math.PI*radius*2)/(teeth*2),radius*0.25,depth);
    for(let i=0;i<teeth;i++){
        const a=(i/teeth)*Math.PI*2; const t=new THREE.Mesh(tGeo,matBrightSteel);
        t.position.set(Math.cos(a)*radius*0.95,Math.sin(a)*radius*0.95,0); t.rotation.z=a+Math.PI/2; t.castShadow=true; g.add(t);
    }
    const axle=new THREE.Mesh(new THREE.CylinderGeometry(radius*0.3,radius*0.3,depth+0.2,12),matDarkMetal);
    axle.rotation.x=Math.PI/2; g.add(axle);
    const hb=new THREE.Mesh(new THREE.BoxGeometry(radius*2,radius*2,depth),new THREE.MeshBasicMaterial({visible:false}));
    g.add(hb); registerSolid(hb); return g;
}

// ================================================================
// LEVEL GEOMETRY
// ================================================================
// Floor
const floor=new THREE.Mesh(new THREE.PlaneGeometry(MAZE_SIZE*TILE_SIZE,MAZE_SIZE*TILE_SIZE),new THREE.MeshStandardMaterial({map:makeFloorTex(),roughness:0.85,metalness:0.4}));
floor.rotation.x=-Math.PI/2; floor.receiveShadow=true; scene.add(floor);

// Ceiling
const ceiling=new THREE.Mesh(new THREE.PlaneGeometry(MAZE_SIZE*TILE_SIZE,MAZE_SIZE*TILE_SIZE),new THREE.MeshStandardMaterial({map:makeStoneTex(),roughness:1.0}));
ceiling.rotation.x=Math.PI/2; ceiling.position.y=14; scene.add(ceiling);

// Walls
const wallGeo=new THREE.BoxGeometry(TILE_SIZE,14,TILE_SIZE);
const wallMat=new THREE.MeshStandardMaterial({map:makeStoneTex(),roughness:0.85,metalness:0.1});
for(let i=0;i<MAZE_SIZE;i++) for(let j=0;j<MAZE_SIZE;j++) if(maze[i][j]===1){
    const w=new THREE.Mesh(wallGeo,wallMat); const p=getPos(i,j);
    w.position.set(p.x,7,p.z); w.castShadow=true; w.receiveShadow=true; scene.add(w);
}

// Decorative wall pipes
const pipeGeo=new THREE.CylinderGeometry(0.18,0.18,TILE_SIZE*0.65,8);
let pipeCount=0;
for(const cell of emptyCells){
    if(pipeCount>=25) break;
    const pos=getPos(cell.x,cell.z);
    for(const[dx,dz]of[[0,-1],[0,1],[-1,0],[1,0]]){
        const wx=cell.x+dx, wz=cell.z+dz;
        if(wx<0||wx>=MAZE_SIZE||wz<0||wz>=MAZE_SIZE||maze[wx][wz]!==1||Math.random()>0.72) continue;
        const pipe=new THREE.Mesh(pipeGeo,matPipe);
        pipe.position.set(pos.x+dx*(TILE_SIZE/2-0.3), 2+Math.random()*7, pos.z+dz*(TILE_SIZE/2-0.3));
        if(dx!==0) pipe.rotation.x=Math.PI/2; else pipe.rotation.z=Math.PI/2;
        scene.add(pipe); pipeCount++;
    }
}

// Corridor flickering point lights
const corridorLights=[];
{
    const sp=getPos(1,1); let added=0;
    for(const cell of emptyCells){
        if(added>=8) break;
        const pos=getPos(cell.x,cell.z);
        if(Math.hypot(pos.x-sp.x,pos.z-sp.z)<15) continue;
        if(Math.random()>0.96){
            const cl=new THREE.PointLight(0xffd090,1.0,20); cl.position.set(pos.x,10,pos.z); scene.add(cl);
            corridorLights.push({light:cl,seed:Math.random()*100,base:0.4+Math.random()*0.8}); added++;
        }
    }
}

// Landmark props (unique intersection markers for orientation)
{
    const sp=getPos(1,1); let added=0;
    for(const cell of emptyCells){
        if(added>=4) break;
        const pos=getPos(cell.x,cell.z);
        if(Math.hypot(pos.x-sp.x,pos.z-sp.z)<25||Math.random()>0.975) continue;
        const lg=new THREE.Group();
        const base=new THREE.Mesh(new THREE.BoxGeometry(3,0.8,3),matDarkMetal); lg.add(base);
        const col=new THREE.Mesh(new THREE.BoxGeometry(0.8,5,0.8),matRustyFrame); col.position.y=2.9; lg.add(col);
        const gear=makeGear(0.9,0.3,8); gear.position.set(0.4,5.2,0); lg.add(gear);
        const lgt=new THREE.PointLight(0xffaa00,0.6,10); lgt.position.set(0,4,0); lg.add(lgt);
        lg.position.set(pos.x,0.4,pos.z); scene.add(lg); added++;
    }
}

// Ambient drip sound sources
const dripSources=[];
for(let i=0;i<5;i++){
    const cell=emptyCells[Math.floor(Math.random()*emptyCells.length)];
    const pos=getPos(cell.x,cell.z);
    dripSources.push({wx:pos.x,wz:pos.z,timer:Math.random()*6,interval:3+Math.random()*5});
}

// Player start position
const startPos=getPos(1,1);
camera.position.set(startPos.x,player.height,startPos.z);
camera.rotation.set(0,yaw,0);

// ================================================================
// TITAN DOOR
// ================================================================
let doorState='closed';
const doorWP=getPos(exitGridX,exitGridZ);
const doorGroup=new THREE.Group(); doorGroup.position.set(doorWP.x,0,doorWP.z);

const FH=16,FZ=-1.5,DZ=0.5,PW=5.0;

const lintel=new THREE.Mesh(new THREE.BoxGeometry(16,4,2),matRustyFrame); lintel.position.set(0,FH-2,FZ); lintel.castShadow=true; doorGroup.add(lintel); registerSolid(lintel);
const lPillar=new THREE.Mesh(new THREE.BoxGeometry(4,FH,2),matRustyFrame); lPillar.position.set(-6,FH/2,FZ); lPillar.castShadow=true; doorGroup.add(lPillar); registerSolid(lPillar);
const rPillar=new THREE.Mesh(new THREE.BoxGeometry(4,FH,2),matRustyFrame); rPillar.position.set(6,FH/2,FZ); rPillar.castShadow=true; doorGroup.add(rPillar); registerSolid(rPillar);

const sirens=[];
function addSiren(x,z){
    const sg=new THREE.Group(); sg.position.set(x,FH-4,z);
    sg.add(new THREE.Mesh(new THREE.CylinderGeometry(0.5,0.5,1,16),matGlassRed));
    const sp=new THREE.SpotLight(0xff0000,0,40,Math.PI/6,0.5,1);
    sp.target.position.set(0,-10,10); sp.castShadow=true;
    sp.shadow.mapSize.width=512; sp.shadow.mapSize.height=512; sp.shadow.camera.near=1; sp.shadow.camera.far=40; sp.shadow.bias=-0.001;
    sg.add(sp); sg.add(sp.target); doorGroup.add(sg); sirens.push({group:sg,light:sp});
}
addSiren(-6,FZ-1); addSiren(6,FZ-1); addSiren(-6,FZ+1); addSiren(6,FZ+1);

const indL=new THREE.Mesh(new THREE.BoxGeometry(0.2,6,0.2),matIndicator); indL.position.set(-4.1,7,FZ); doorGroup.add(indL);
const indR=new THREE.Mesh(new THREE.BoxGeometry(0.2,6,0.2),matIndicator); indR.position.set(4.1,7,FZ); doorGroup.add(indR);

const doorHL=new THREE.Group(); doorHL.position.set(-PW/2,7,DZ); doorGroup.add(doorHL);
const doorHR=new THREE.Group(); doorHR.position.set(PW/2,7,DZ); doorGroup.add(doorHR);

const panelGeo=new THREE.BoxGeometry(PW,14,1.0);
const panelL=new THREE.Mesh(panelGeo,matDarkMetal); panelL.castShadow=true; doorHL.add(panelL); registerSolid(panelL);
const panelR=new THREE.Mesh(panelGeo,matDarkMetal); panelR.castShadow=true; doorHR.add(panelR); registerSolid(panelR);

const deadboltsL=[], deadboltsR=[];
const boltGeo=new THREE.CylinderGeometry(0.3,0.3,3,16); boltGeo.rotateZ(Math.PI/2);
for(const y of[-3,-1,1,3]){
    const bL=new THREE.Mesh(boltGeo,matBrightSteel); bL.position.set(1.5,y,0); doorHL.add(bL); deadboltsL.push(bL);
    const bR=new THREE.Mesh(boltGeo,matBrightSteel); bR.position.set(-1.5,y,0); doorHR.add(bR); deadboltsR.push(bR);
}

const vaultWG=new THREE.Group(); vaultWG.position.set(PW/2,0,-0.7); doorHL.add(vaultWG);
vaultWG.add(makeGear(2.5,0.8,16));
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
const rackL=new THREE.Mesh(rackGeo,matBrightSteel); rackL.position.set(0,4,-0.8); doorHL.add(rackL);
const rackR=new THREE.Mesh(rackGeo,matBrightSteel); rackR.position.set(0,4,-0.8); doorHR.add(rackR);

const GR=1.6;
const mainGL=makeGear(GR,0.6,12); mainGL.position.set(-3,11+GR,-0.8); doorGroup.add(mainGL);
const mainGR2=makeGear(GR,0.6,12); mainGR2.position.set(3,11+GR,-0.8); doorGroup.add(mainGR2);
const HGR=0.8;
const helpGL=makeGear(HGR,0.6,6); helpGL.position.set(-3-GR-HGR+0.2,11+GR+1,-0.8); doorGroup.add(helpGL);
const helpGR=makeGear(HGR,0.6,6); helpGR.position.set(3+GR+HGR-0.2,11+GR+1,-0.8); doorGroup.add(helpGR);

const pistonGroup=new THREE.Group(); doorGroup.add(pistonGroup);
const pistonGeoMesh=new THREE.BoxGeometry(1.5,6,1.5);
const pistonL=new THREE.Mesh(pistonGeoMesh,matHazard); pistonL.position.set(-3.5,7,-0.8); pistonL.castShadow=true; pistonGroup.add(pistonL); registerSolid(pistonL);
const pistonR=new THREE.Mesh(pistonGeoMesh,matHazard); pistonR.position.set(3.5,7,-0.8); pistonR.castShadow=true; pistonGroup.add(pistonR); registerSolid(pistonR);

scene.add(doorGroup);

// ================================================================
// ORBS
// ================================================================
const orbs=[];
const orbRingGeo=new THREE.RingGeometry(0.7,0.85,28);

{
    let attempts=0;
    while(orbs.length<TOTAL_ORBS && attempts<2000){
        attempts++;
        const cell=emptyCells[Math.floor(Math.random()*emptyCells.length)];
        const pos=getPos(cell.x,cell.z);
        if(Math.hypot(pos.x-startPos.x,pos.z-startPos.z)<20) continue;
        let tooClose=false;
        for(const o of orbs) if(Math.hypot(pos.x-o.position.x,pos.z-o.position.z)<20){tooClose=true;break;}
        if(tooClose) continue;
        const orbMesh=new THREE.Mesh(new THREE.SphereGeometry(0.5,16,16),new THREE.MeshStandardMaterial({color:0x00eeff,emissive:new THREE.Color(0x00eeff),emissiveIntensity:0.9,roughness:0.15,metalness:0.6}));
        orbMesh.position.set(pos.x,1.5,pos.z);
        const ringMat=new THREE.MeshBasicMaterial({color:0x00eeff,side:THREE.DoubleSide,transparent:true,opacity:0.35,depthWrite:false});
        const ring=new THREE.Mesh(orbRingGeo,ringMat);
        ring.rotation.x=-Math.PI/2; ring.position.y=0.05; orbMesh.add(ring);
        const oLight=new THREE.PointLight(0x00eeff,1.5,12); orbMesh.add(oLight);
        orbMesh.userData={isGold:false,light:oLight,ring,ringMat};
        scene.add(orbMesh); orbs.push(orbMesh);
    }
}
// Designate 3 random orbs as gold (stamina restore bonus)
const goldIdxs=new Set();
while(goldIdxs.size<Math.min(3,orbs.length)) goldIdxs.add(Math.floor(Math.random()*orbs.length));
for(const idx of goldIdxs){
    const o=orbs[idx];
    o.material.color.setHex(0xffaa00); o.material.emissive.setHex(0xffaa00);
    o.userData.light.color.setHex(0xffaa00); o.userData.ringMat.color.setHex(0xffaa00);
    o.userData.isGold=true;
}

// ================================================================
// ENEMIES
// ================================================================
const ghostGeo=new THREE.SphereGeometry(1.2,20,20);
const ghostMat=new THREE.MeshBasicMaterial({color:0xff0000,transparent:true,opacity:0.7});
const auraGeo=new THREE.SphereGeometry(1.9,12,12);
const enemies=[];

function spawnEnemy(wx,wz,gridCell,initialState){
    const enemy=new THREE.Mesh(ghostGeo,ghostMat.clone()); enemy.position.set(wx,2.0,wz);
    const auraMat=new THREE.MeshBasicMaterial({color:0xff1100,transparent:true,opacity:0.12,depthWrite:false});
    enemy.add(new THREE.Mesh(auraGeo,auraMat));
    const pLight=new THREE.PointLight(0xff0000,2,20); enemy.add(pLight);
    enemy.userData={
        state:initialState||'patrol', alertTimer:0, pathQueue:[],
        pathUpdateTimer:0, targetPos:new THREE.Vector3(wx,2.0,wz),
        lastGrid:gridCell||worldToGrid(wx,wz), lastKnownGrid:null,
        patrolSpeed:0.12, alertSpeed:0.22, searchSpeed:0.07,
        afterimageTimer:0, facingAngle:0, auraMat, light:pLight,
        name:ENEMY_NAMES[enemies.length%ENEMY_NAMES.length]
    };
    if(initialState==='alerted'){enemy.userData.alertTimer=ALERT_DURATION; pLight.intensity=8;}
    scene.add(enemy); enemies.push(enemy); return enemy;
}

{   // Initial enemy placement
    let attempts=0;
    while(enemies.length<8 && attempts<2000){
        attempts++;
        const eCell=emptyCells[Math.floor(Math.random()*emptyCells.length)];
        const ePos=getPos(eCell.x,eCell.z);
        if(Math.hypot(ePos.x-startPos.x,ePos.z-startPos.z)<40) continue;
        let tooClose=false;
        for(const e of enemies) if(Math.hypot(ePos.x-e.position.x,ePos.z-e.position.z)<30){tooClose=true;break;}
        if(!tooClose) spawnEnemy(ePos.x,ePos.z,{x:eCell.x,z:eCell.z},'patrol');
    }
}

// ================================================================
// ALERT HELPERS
// ================================================================
function triggerAlert(enemy){
    const ud=enemy.userData;
    if(ud.state==='alerted'){ud.alertTimer=ALERT_DURATION;return;}
    ud.state='alerted'; ud.alertTimer=ALERT_DURATION; ud.pathUpdateTimer=0; ud.light.intensity=8;
    playScreech();
    lastKnownPos={wx:camera.position.x,wz:camera.position.z}; lastKnownTime=performance.now();
}
function alertRadius(wx,wz,radius){
    for(const e of enemies) if(e.userData.state!=='alerted'&&Math.hypot(e.position.x-wx,e.position.z-wz)<radius) triggerAlert(e);
}

// ================================================================
// RECORDS (localStorage)
// ================================================================
function saveRecord(name,time,orbs,outcome){
    try{
        const recs=JSON.parse(localStorage.getItem('vigil_records')||'[]');
        recs.unshift({name:name||'UNKNOWN',time,orbs,outcome,date:Date.now()});
        if(recs.length>10) recs.length=10;
        localStorage.setItem('vigil_records',JSON.stringify(recs));
        const runs=parseInt(localStorage.getItem('vigil_runs')||'0')+1;
        localStorage.setItem('vigil_runs',String(runs));
        if(outcome==='ESCAPED'){const b=localStorage.getItem('vigil_best');if(!b||parseFloat(time)<parseFloat(b))localStorage.setItem('vigil_best',time);}
    }catch(e){}
}
function loadRecords(){
    try{
        const recs=JSON.parse(localStorage.getItem('vigil_records')||'[]');
        const arch=document.getElementById('archives-list');
        if(!recs.length){arch.innerHTML='<div style="color:#3e2e21;text-align:center;margin-top:45px;font-weight:bold;font-size:0.8em;">NO ARCHIVES FOUND</div>';return;}
        arch.innerHTML=recs.map(r=>`<div style="margin-bottom:8px;border-bottom:1px solid #3e2e21;padding-bottom:6px;font-size:0.8em;"><span style="color:#d4af37">${r.name}</span><span style="float:right;color:${r.outcome==='ESCAPED'?'#77ff77':'#ff5555'}">${r.outcome}</span><br><span style="color:#8b6b4a">${formatTime(r.time)} // ${r.orbs}/${TOTAL_ORBS}</span></div>`).join('');
        const best=localStorage.getItem('vigil_best');
        document.getElementById('bestTime').innerText=best?formatTime(best):'--:--';
        document.getElementById('tryCount').innerText=localStorage.getItem('vigil_runs')||'0';
    }catch(e){}
}
loadRecords();

// ================================================================
// MENU + INPUT
// ================================================================
const uiContainer=document.getElementById('main-ui');
const engageBtn=document.getElementById('engage-btn');
const nameInput=document.getElementById('name-input');
const bgText=document.getElementById('input-bg-text');

const quotes=["The corridors are wide, but the paths are many.","Do not trust the geometry.","Cyan light is a guide, but also a trap.","They only hunt what moves in the light.","The gold ones remember you."];
document.getElementById('lore-text').innerText=`"${quotes[Math.floor(Math.random()*quotes.length)]}"`;

nameInput.addEventListener('focus',()=>{if(!nameInput.value){bgText.innerHTML='<div class="dots"><span>.</span><span>.</span><span>.</span></div>';bgText.style.opacity='1';}});
nameInput.addEventListener('blur',()=>{if(!nameInput.value){bgText.innerHTML='NAMETAG';bgText.style.opacity='1';}});
nameInput.addEventListener('input',e=>{
    playUI(90,1.2,0.25,'triangle');
    e.target.value=e.target.value.replace(/[^A-Za-z]/g,'').toUpperCase();
    bgText.style.opacity=nameInput.value.length?'0':'1';
    if(!nameInput.value) bgText.innerHTML='<div class="dots"><span>.</span><span>.</span><span>.</span></div>';
});
nameInput.addEventListener('keydown',e=>e.stopPropagation());
nameInput.addEventListener('keyup',e=>e.stopPropagation());

document.querySelectorAll('#main-ui button,#main-ui input').forEach(el=>{
    el.addEventListener('mouseenter',()=>playUI(500,0.5,0.08,'triangle'));
    if(el!==engageBtn) el.addEventListener('mousedown',()=>playUI(180,1.5,0.2,'sine'));
    else el.addEventListener('mousedown',()=>playUI(100,2.0,0.4,'sine'));
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
        startAmbient();
        if(!introPlayed){
            introPlayed=true;
            const name=nameInput.value||'OPERATIVE';
            const fb=document.getElementById('fade-black');
            fb.style.display='flex'; fb.style.alignItems='center'; fb.style.justifyContent='center';
            fb.style.transition='none'; fb.style.opacity='1';
            fb.innerHTML=`<div style="text-align:center;font-family:'Courier New';letter-spacing:3px;pointer-events:none;"><div style="color:#d4af37;font-size:1.8em;margin-bottom:12px;">OPERATIVE: ${name}</div><div style="color:#5e4835;font-size:0.9em;">DEPLOYED</div></div>`;
            setTimeout(()=>{fb.style.transition='opacity 1.5s ease-in-out';fb.style.opacity='0';setTimeout(()=>{fb.innerHTML='';fb.style.display='';},1600);},1200);
        }
    } else if(!gameWon){
        uiContainer.style.display='flex';
        document.getElementById('main-title').innerText='SYSTEM PAUSED';
        engageBtn.innerText='RESUME';
        gameActive=false; accumulatedTime+=(Date.now()-startTime)/1000;
        document.getElementById('menuOrbCount').innerText=orbsCollected;
    }
});

document.addEventListener('mousemove',e=>{
    if(document.pointerLockElement===document.body){
        yaw-=e.movementX*SENSITIVITY; pitch-=e.movementY*SENSITIVITY;
        pitch=Math.max(-Math.PI/2,Math.min(Math.PI/2,pitch));
    }
});
document.addEventListener('keydown',e=>keys[e.code]=true);
document.addEventListener('keyup',e=>keys[e.code]=false);

// ================================================================
// RADAR CANVAS
// ================================================================
const radarCanvas=document.getElementById('radar');
const rCtx=radarCanvas.getContext('2d');
const rC=radarCanvas.width/2, radarMaxDist=120, rScale=(rC-10)/radarMaxDist;

// ================================================================
// HUD DOM REFS (cached for performance)
// ================================================================
const elOrbCount=document.getElementById('orbCount');
const elTime=document.getElementById('timeVal');
const elStBar=document.getElementById('stamina-bar');
const elStCont=document.getElementById('stamina-container');
const elCross=document.getElementById('crosshair');
const elThreat=document.getElementById('threat-fill');
const elVignette=document.getElementById('vignette');
const elUnitsN=document.getElementById('unitsCount');
const elUnitsA=document.getElementById('unitsAlerted');
const elDoorPrompt=document.getElementById('door-prompt');
const elOrbsRem=document.getElementById('orbsRemaining');
const elUI=document.getElementById('ui');

// ================================================================
// UPDATE LOOP
// ================================================================
function update(){
    if(!gameActive) return;

    const now=performance.now();
    const delta=Math.min((now-prevTime)/1000,0.05);
    prevTime=now;
    const totalElapsed=(accumulatedTime+(Date.now()-startTime)/1000).toFixed(1);
    if(!gameWon) elTime.innerText=totalElapsed;

    // Track explored cells for radar wall outlines
    const pg=worldToGrid(camera.position.x,camera.position.z);
    exploredCells.add(`${pg.x},${pg.z}`);

    // ==== PLAYER MOVEMENT ====
    if(!gameWon){
        let ix=0,iz=0;
        if(keys['KeyW']) iz-=1; if(keys['KeyS']) iz+=1;
        if(keys['KeyA']) ix-=1; if(keys['KeyD']) ix+=1;
        const moving=(ix!==0||iz!==0);
        if(moving){const len=Math.hypot(ix,iz);ix/=len;iz/=len;}

        const isSprinting=keys['ShiftLeft']&&moving&&!player.isExhausted;
        currentlySprinting=isSprinting;

        // Stamina
        if(isSprinting){player.stamina-=0.4;if(player.stamina<=0)player.isExhausted=true;}
        else{player.stamina=Math.min(MAX_STAMINA,player.stamina+0.9);if(player.stamina>=MAX_STAMINA*0.25)player.isExhausted=false;}
        const stPct=(player.stamina/MAX_STAMINA)*100;
        elStBar.style.width=stPct+'%';
        elStBar.style.background=player.isExhausted?'#8b0000':'linear-gradient(to bottom, #d4af37, #997a00)';
        elStCont.classList.toggle('exhausted',player.isExhausted);

        // Flashlight flickers when stamina < 28%
        flashLight.intensity=stPct<28?50*(0.7+0.3*Math.abs(Math.sin(now*0.025+Math.sin(now*0.007)*3))):50;

        // Velocity lerp (plain floats — no THREE.Vector2)
        const spd=isSprinting?player.runSpeed:(moving?player.walkSpeed:0);
        const tvX=(ix*Math.cos(yaw)+iz*Math.sin(yaw))*spd;
        const tvZ=(-ix*Math.sin(yaw)+iz*Math.cos(yaw))*spd;
        player.velX+=(tvX-player.velX)*0.15;
        player.velZ+=(tvZ-player.velZ)*0.15;

        // Collision with stamina wall-bump drain
        const nx=camera.position.x+player.velX, nz=camera.position.z+player.velZ;
        if(!isWall(nx,camera.position.z,player.radius)) camera.position.x=nx;
        else if(moving) player.stamina=Math.max(0,player.stamina-3);
        if(!isWall(camera.position.x,nz,player.radius)) camera.position.z=nz;
        else if(moving) player.stamina=Math.max(0,player.stamina-3);

        // Head bob + footsteps
        const spd2=Math.hypot(player.velX,player.velZ);
        if(spd2>0.02){
            const hz=isSprinting?3.5:1.5, amp=isSprinting?0.12:0.08;
            player.headBobTimer+=delta*hz*Math.PI*2;
            camera.position.y=player.height+Math.sin(player.headBobTimer)*amp;
            const cycle=Math.floor(player.headBobTimer/Math.PI);
            if(cycle>player.lastFootstepCycle){
                player.lastFootstepCycle=cycle;
                playFootstep(isSprinting);
                // Near-door footstep variant (slightly higher click near stone frame)
                if(camera.position.distanceTo(doorGroup.position)<20) playUI(isSprinting?420:280,0.07,0.06,'square');
                if(isSprinting){
                    sprintBreathStep++; if(sprintBreathStep%2===0) playSprintBreath();
                    echoPositions.push({wx:camera.position.x,wz:camera.position.z});
                    if(echoPositions.length>3) echoPositions.shift();
                }
            }
            // Sprint sound alert (throttled every 0.5s)
            if(isSprinting){sprintAlertCooldown-=delta;if(sprintAlertCooldown<=0){sprintAlertCooldown=0.5;alertRadius(camera.position.x,camera.position.z,SPRINT_ALERT_R);}}
        } else {
            camera.position.y+=(player.height-camera.position.y)*0.1;
            player.headBobTimer+=delta;
        }

        // Camera lean based on yaw change
        const yawD=yaw-prevYaw; prevYaw=yaw;
        leanAngle+=(yawD*-18-leanAngle)*0.12; leanAngle*=0.82;
    }

    // ==== ORB ANIMATION + COLLECTION ====
    let nearbyOrb=false;
    const remaining=orbs.filter(o=>o.position.y>0).length;
    for(const orb of orbs){
        if(orb.position.y<0) continue;
        const scarcity=1-(remaining/TOTAL_ORBS);
        orb.position.y=1.5+Math.sin(now*0.002+orb.position.x)*0.18;
        orb.rotation.y+=delta*1.2;
        orb.material.emissiveIntensity=0.9+scarcity*0.7;
        orb.userData.light.intensity=1.5+scarcity*2.5;
        if(orb.userData.ringMat) orb.userData.ringMat.opacity=0.25+scarcity*0.25;
        const distO=camera.position.distanceTo(orb.position);
        if(distO<6) nearbyOrb=true;
        if(!gameWon&&distO<3){
            orb.position.y=-1000; orbsCollected++; elOrbCount.innerText=orbsCollected;
            // Flash orb counter
            clearTimeout(orbFlashTimeout);
            elUI.classList.remove('orb-flash'); void elUI.offsetWidth;
            elUI.classList.add('orb-flash');
            orbFlashTimeout=setTimeout(()=>elUI.classList.remove('orb-flash'),400);
            // Scale enemy speeds with orb count
            const ns=0.12+orbsCollected*0.007;
            for(const e of enemies){e.userData.patrolSpeed=ns;e.userData.alertSpeed=Math.min(0.32,0.22+orbsCollected*0.005);}
            // Audio
            if(orb.userData.isGold){player.stamina=Math.min(MAX_STAMINA,player.stamina+MAX_STAMINA*0.6);player.isExhausted=false;playGoldChime();}
            else{
                playChime([440,660,880],0.09);
                if(orbsCollected===6) playChime([330,440,660],0.13);
                if(orbsCollected===11) playChime([330,440,660],0.13);
                if(orbsCollected===TOTAL_ORBS) playChime([220,330,440,660,880],0.13);
            }
            // Sound alert at orb position
            alertRadius(orb.position.x,orb.position.z,ORB_ALERT_R);
            // Trigger door when all collected
            if(orbsCollected===TOTAL_ORBS&&doorState==='closed'){
                doorState='valves_pressure'; initIndustrialAudio();
                sirens.forEach(s=>s.light.intensity=50);
                klaxonGain.gain.setTargetAtTime(0.015,audioCtx.currentTime,0.1);
                hissGain.gain.setTargetAtTime(0.1,audioCtx.currentTime,0.1);
                // Spawn 2 alerted enemies from maze edges
                const edgeCells=emptyCells.filter(c=>c.x===1||c.x===MAZE_SIZE-2||c.z===1||c.z===MAZE_SIZE-2);
                if(edgeCells.length>0){
                    for(let i=0;i<2;i++){
                        const ec=edgeCells[Math.floor(Math.random()*edgeCells.length)];
                        const ep=getPos(ec.x,ec.z); spawnEnemy(ep.x,ep.z,{x:ec.x,z:ec.z},'alerted');
                    }
                }
            }
        }
    }
    elCross.classList.toggle('nearby',nearbyOrb);

    // ==== PARTICLES ====
    for(let i=particles.length-1;i>=0;i--){
        const p=particles[i]; p.position.addScaledVector(p.userData.vel,delta); p.userData.life-=delta;
        if(p.userData.type==='steam'){p.userData.mat.opacity=(p.userData.life/1.0)*0.5;p.scale.setScalar(2.0-p.userData.life);}
        else if(p.userData.type==='spark'){p.userData.vel.y-=delta*15;if(p.position.y<0.1){p.position.y=0.1;p.userData.vel.y*=-0.5;}}
        else if(p.userData.type==='afterimage') p.userData.mat.opacity=(p.userData.life/0.55)*0.3;
        if(p.userData.life<=0){scene.remove(p);if(p.userData.type!=='spark')p.userData.mat.dispose();particles.splice(i,1);}
    }

    // Ceiling drip particles (steam falling from y=14)
    ceilingDripTimer-=delta;
    if(ceilingDripTimer<=0){
        ceilingDripTimer=2+Math.random()*4;
        const dc=emptyCells[Math.floor(Math.random()*emptyCells.length)];
        const dp=getPos(dc.x,dc.z);
        // Override velocity to go downward for ceiling drips
        const mat=steamMatBase.clone();
        const m=new THREE.Mesh(steamGeoBase,mat); m.position.set(dp.x,14,dp.z);
        m.userData={vel:new THREE.Vector3((Math.random()-0.5)*0.5,-Math.random()*2-0.5,(Math.random()-0.5)*0.5),life:1.2,type:'steam',mat};
        scene.add(m); particles.push(m);
    }

    // Drip sounds
    for(const dr of dripSources){
        dr.timer-=delta;
        if(dr.timer<=0){
            dr.timer=dr.interval;
            const d=Math.hypot(camera.position.x-dr.wx,camera.position.z-dr.wz);
            if(d<35) playDrip(Math.max(0.1,1-d/35));
        }
    }

    // Corridor light flicker
    for(const cl of corridorLights) cl.light.intensity=Math.max(0,cl.base+Math.sin(now*0.012+cl.seed)*0.3+Math.sin(now*0.031+cl.seed*2)*0.15);

    // Fog thickens when any enemy is alerted
    const anyAlerted=enemies.some(e=>e.userData.state==='alerted');
    scene.fog.far+=(((anyAlerted?52:120)-scene.fog.far)*0.015);

    // ==== RADAR ====
    rCtx.clearRect(0,0,radarCanvas.width,radarCanvas.height);
    // Draw explored cell dots
    rCtx.fillStyle='rgba(80,70,55,0.28)';
    for(const key of exploredCells){
        const[gx,gz]=key.split(',').map(Number);
        const wp=getPos(gx,gz);
        const dx=wp.x-camera.position.x, dz=wp.z-camera.position.z;
        if(Math.hypot(dx,dz)>radarMaxDist) continue;
        const lr=dx*Math.cos(yaw)-dz*Math.sin(yaw);
        const lf=-dx*Math.sin(yaw)-dz*Math.cos(yaw);
        rCtx.fillRect(rC+lr*rScale-1.2, rC-lf*rScale-1.2, 2.4, 2.4);
    }
    // Crosshair lines
    rCtx.strokeStyle='rgba(212,196,168,0.2)'; rCtx.lineWidth=1;
    rCtx.beginPath(); rCtx.moveTo(rC,0); rCtx.lineTo(rC,radarCanvas.height); rCtx.moveTo(0,rC); rCtx.lineTo(radarCanvas.width,rC); rCtx.stroke();
    // Player arrow
    rCtx.fillStyle='#d4c4a8'; rCtx.beginPath(); rCtx.moveTo(rC,rC-8); rCtx.lineTo(rC-5,rC+5); rCtx.lineTo(rC+5,rC+5); rCtx.fill();

    function drawBlip(wx,wz,color,size){
        const dx=wx-camera.position.x, dz=wz-camera.position.z;
        let lr=dx*Math.cos(yaw)-dz*Math.sin(yaw), lf=-dx*Math.sin(yaw)-dz*Math.cos(yaw);
        const dist=Math.hypot(lr,lf);
        if(dist>radarMaxDist){lr=(lr/dist)*radarMaxDist;lf=(lf/dist)*radarMaxDist;}
        const rx=rC+lr*rScale, ry=rC-lf*rScale;
        rCtx.fillStyle=color; rCtx.beginPath(); rCtx.arc(rx,ry,size,0,Math.PI*2); rCtx.fill();
        return {rx,ry};
    }

    // Door blip
    {
        const dx=doorGroup.position.x-camera.position.x, dz=doorGroup.position.z-camera.position.z;
        let lr=dx*Math.cos(yaw)-dz*Math.sin(yaw), lf=-dx*Math.sin(yaw)-dz*Math.cos(yaw);
        const dist=Math.hypot(lr,lf);
        if(dist>radarMaxDist){lr=(lr/dist)*radarMaxDist;lf=(lf/dist)*radarMaxDist;}
        const rx=rC+lr*rScale, ry=rC-lf*rScale;
        rCtx.fillStyle='#55aa55'; rCtx.fillRect(rx-5,ry-7,10,14);
        rCtx.fillStyle='#112211'; rCtx.fillRect(rx-3,ry-5,6,12);
        rCtx.fillStyle='#d4af37'; rCtx.beginPath(); rCtx.arc(rx+1,ry+1,1.5,0,Math.PI*2); rCtx.fill();
    }
    // Orb blips
    for(const o of orbs) if(o.position.y>0) drawBlip(o.position.x,o.position.z,o.userData.isGold?'#ffaa00':'#d4af37',2.5);
    // Last-known-player blip (blinks every 500ms, fades after 25s)
    if(lastKnownPos&&(now-lastKnownTime)<25000&&Math.floor(now/500)%2===0) drawBlip(lastKnownPos.wx,lastKnownPos.wz,'#ff3333',3.5);

    // ==== ENEMY STATE MACHINE ====
    let closestDist=100, alertedCount=0;
    for(let idx=0;idx<enemies.length;idx++){
        const enemy=enemies[idx]; const ud=enemy.userData;
        const distE=camera.position.distanceTo(enemy.position);
        if(distE<closestDist) closestDist=distE;

        // Facing angle for radar FOV cone
        const toTgt=new THREE.Vector3().subVectors(ud.targetPos,enemy.position);
        if(toTgt.length()>0.5) ud.facingAngle=Math.atan2(toTgt.x,toTgt.z);

        // Light detection: enemy in player flashlight cone + LOS?
        if(ud.state!=='alerted'&&distE<LIGHT_RANGE){
            const camFwd=new THREE.Vector3(0,0,-1).applyQuaternion(camera.quaternion);
            const camToE=new THREE.Vector3().subVectors(enemy.position,camera.position).normalize();
            if(camFwd.dot(camToE)>FLASH_CONE_COS&&hasLOS(camera.position.x,camera.position.z,enemy.position.x,enemy.position.z)) triggerAlert(enemy);
        }

        if(ud.state==='alerted'){
            alertedCount++;
            ud.alertTimer-=delta; ud.light.intensity=6+Math.sin(now*0.008)*2;
            if(ud.alertTimer<=0){ud.state='searching';ud.pathUpdateTimer=0;}
            else{
                // BFS toward player (throttled to every 1.5s)
                ud.pathUpdateTimer-=delta;
                if(ud.pathUpdateTimer<=0){
                    ud.pathUpdateTimer=1.5;
                    const pg2=worldToGrid(camera.position.x,camera.position.z);
                    const eg=worldToGrid(enemy.position.x,enemy.position.z);
                    const path=bfsPath(eg.x,eg.z,pg2.x,pg2.z);
                    if(path.length>0){ud.pathQueue=path;ud.lastKnownGrid=pg2;lastKnownPos={wx:camera.position.x,wz:camera.position.z};lastKnownTime=now;}
                }
            }
        } else if(ud.state==='searching'){
            alertedCount++;
            ud.light.intensity=3; enemy.rotation.y+=delta*0.7; // idle look-around
            if(ud.lastKnownGrid){
                const lkw=getPos(ud.lastKnownGrid.x,ud.lastKnownGrid.z);
                const lkPos=new THREE.Vector3(lkw.x,2.0,lkw.z);
                if(enemy.position.distanceTo(lkPos)<TILE_SIZE*0.5){
                    // Check footstep echoes first
                    if(echoPositions.length>0){const echo=echoPositions.pop();ud.lastKnownGrid=worldToGrid(echo.wx,echo.wz);ud.pathQueue=[];ud.pathUpdateTimer=0;}
                    else{ud.state='patrol';ud.lastKnownGrid=null;ud.pathQueue=[];ud.light.intensity=2;}
                } else {
                    ud.pathUpdateTimer-=delta;
                    if(ud.pathUpdateTimer<=0){
                        ud.pathUpdateTimer=2.0;
                        const eg=worldToGrid(enemy.position.x,enemy.position.z);
                        ud.pathQueue=bfsPath(eg.x,eg.z,ud.lastKnownGrid.x,ud.lastKnownGrid.z);
                    }
                }
            } else {ud.state='patrol';ud.light.intensity=2;}
        } else {
            // PATROL: random wander (no radar blip)
            ud.light.intensity=2;
            if(enemy.position.distanceTo(ud.targetPos)<0.5){
                const cx=Math.round(ud.targetPos.x/TILE_SIZE)+Math.floor(MAZE_SIZE/2);
                const cz=Math.round(ud.targetPos.z/TILE_SIZE)+Math.floor(MAZE_SIZE/2);
                const nb=[];
                for(const[dx,dz]of[[0,-1],[0,1],[-1,0],[1,0]]){
                    const nx2=cx+dx,nz2=cz+dz;
                    if(nx2>=0&&nx2<MAZE_SIZE&&nz2>=0&&nz2<MAZE_SIZE&&maze[nx2][nz2]===0&&!(nx2===ud.lastGrid.x&&nz2===ud.lastGrid.z)) nb.push({x:nx2,z:nz2});
                }
                if(!nb.length&&maze[ud.lastGrid.x]&&maze[ud.lastGrid.x][ud.lastGrid.z]===0) nb.push(ud.lastGrid);
                ud.lastGrid={x:cx,z:cz};
                const nc=nb.length?nb[Math.floor(Math.random()*nb.length)]:ud.lastGrid;
                ud.targetPos.set(getPos(nc.x,nc.z).x,2.0,getPos(nc.x,nc.z).z);
            }
        }

        // Follow active path queue (shared by alerted + searching states)
        if(ud.pathQueue.length>0){
            const nc=ud.pathQueue[0]; const nw=getPos(nc.x,nc.z);
            const np=new THREE.Vector3(nw.x,2.0,nw.z);
            if(enemy.position.distanceTo(np)<TILE_SIZE*0.4) ud.pathQueue.shift();
            else ud.targetPos.copy(np);
        }

        // Move toward target
        const moveSpd=ud.state==='alerted'?ud.alertSpeed:ud.state==='searching'?ud.searchSpeed:ud.patrolSpeed;
        const dir=new THREE.Vector3().subVectors(ud.targetPos,enemy.position); dir.y=0;
        if(dir.length()>0.01){dir.normalize();enemy.position.addScaledVector(dir,moveSpd);}
        enemy.position.y=2.0+Math.sin(now*0.003+idx)*0.4;

        // Aura pulse
        if(ud.auraMat){
            ud.auraMat.opacity=(ud.state==='alerted'?0.18:0.08)+Math.sin(now*0.0025+idx*1.7)*0.06;
            const auraChild=enemy.children.find(c=>c.isMesh&&c.geometry===auraGeo);
            if(auraChild) auraChild.scale.setScalar(1+Math.sin(now*0.002+idx)*0.12);
        }

        // Afterimage trail when active (alerted/searching only)
        if(ud.state!=='patrol'){ud.afterimageTimer-=delta;if(ud.afterimageTimer<=0){ud.afterimageTimer=0.35;emitAfterimage(enemy.position.x,enemy.position.y,enemy.position.z);}}

        // Radar: patrol enemies are invisible — only alerted/searching shown with FOV cone
        if(ud.state!=='patrol'){
            const blipColor=ud.state==='alerted'?'#ff4444':'#ff8844';
            const bl=drawBlip(enemy.position.x,enemy.position.z,blipColor,3);
            const fovLen=18*rScale; const facing=ud.facingAngle-yaw; const fovA=Math.PI/4;
            rCtx.strokeStyle='rgba(255,60,60,0.28)'; rCtx.lineWidth=1;
            rCtx.beginPath();
            rCtx.moveTo(bl.rx,bl.ry); rCtx.lineTo(bl.rx+Math.sin(facing-fovA)*fovLen,bl.ry-Math.cos(facing-fovA)*fovLen);
            rCtx.moveTo(bl.rx,bl.ry); rCtx.lineTo(bl.rx+Math.sin(facing+fovA)*fovLen,bl.ry-Math.cos(facing+fovA)*fovLen);
            rCtx.stroke();
            rCtx.beginPath(); rCtx.arc(bl.rx,bl.ry,fovLen,-(facing+fovA)-Math.PI/2,-(facing-fovA)-Math.PI/2);
            rCtx.strokeStyle='rgba(255,60,60,0.12)'; rCtx.stroke();
        }

        // Death check
        if(!gameWon&&distE<3.0&&gameActive){
            gameActive=false; document.exitPointerLock();
            const t=(accumulatedTime+(Date.now()-startTime)/1000).toFixed(1);
            document.getElementById('time-stat').innerText=formatTime(parseFloat(t));
            document.getElementById('orb-stat').innerText=`${orbsCollected} / ${TOTAL_ORBS}`;
            document.getElementById('death-cause').innerText=ud.name||'PHANTOM';
            document.getElementById('death-operative').innerText=nameInput.value||'UNKNOWN';
            document.getElementById('death-screen-ui').style.display='block';
            saveRecord(nameInput.value||'UNKNOWN',t,orbsCollected,'KILLED');
        }
    }

    // Units HUD
    elUnitsN.innerText=enemies.length;
    elUnitsA.innerText=alertedCount>0?` // ${alertedCount} ⚠`:'';
    elUnitsA.style.color=alertedCount>0?'#ff5555':'inherit';

    // Door proximity prompt
    {
        const show=camera.position.distanceTo(doorGroup.position)<20&&doorState==='closed'&&orbsCollected<TOTAL_ORBS;
        elDoorPrompt.style.display=show?'block':'none';
        if(show) elOrbsRem.innerText=TOTAL_ORBS-orbsCollected;
    }

    // Threat bar
    {
        const tl=closestDist<30?Math.max(0,(30-closestDist)/30):0;
        elThreat.style.width=(tl*100)+'%';
        const isClose=closestDist<12,isMed=closestDist<22;
        elThreat.style.background=isClose?'linear-gradient(to right,#cc0000,#ff0000)':isMed?'linear-gradient(to right,#cc4400,#ff6600)':'linear-gradient(to right,#886600,#ffaa00)';
        elThreat.style.boxShadow=tl>0.3?`0 0 ${Math.round(tl*14)}px rgba(255,${isClose?0:100},0,0.8)`:'none';
    }

    // Vignette (sprint = chromatic red tint, enemy = dark)
    {
        const sI=currentlySprinting?0.38:0;
        const eI=closestDist<18?((18-closestDist)/18)*0.52:0;
        elVignette.style.opacity=Math.min(0.92,sI+eI);
        // Chromatic: reddish background radial when sprinting
        elVignette.style.background=currentlySprinting
            ?'radial-gradient(ellipse at center, transparent 35%, rgba(35,0,8,0.97) 100%)'
            :'radial-gradient(ellipse at center, transparent 35%, rgba(0,0,0,0.97) 100%)';
    }

    // Proximity audio scaling
    if(breathGain){const bi=closestDist<20?Math.max(0,(20-closestDist)/20):0;breathGain.gain.setTargetAtTime(bi*0.07,audioCtx.currentTime,0.4);if(ambientGain)ambientGain.gain.setTargetAtTime(0.045+bi*0.03,audioCtx.currentTime,0.6);}
    if(growlGain){const gi=alertedCount>0&&closestDist<35?Math.max(0,(35-closestDist)/35)*0.12:0;growlGain.gain.setTargetAtTime(gi,audioCtx.currentTime,0.5);}

    // Proximity sting
    if(!gameWon&&closestDist<12){camera.position.x+=(Math.random()-0.5)*((12-closestDist)*0.02);if(!hasPlayedSting){playSting();hasPlayedSting=true;}}
    else hasPlayedSting=false;

    // Apply camera rotation (lean + door shake)
    camera.rotation.set(pitch,yaw,leanAngle+doorShakeZ);

    // ==== DOOR SEQUENCE ====
    if(doorState!=='closed'&&doorState!=='open'){
        const dtd=camera.position.distanceTo(doorGroup.position), vs=Math.max(0,1-dtd/50);
        sirens.forEach((s,i)=>s.group.rotation.y+=delta*(i%2===0?2:-2));
        if(klaxonGain) klaxonGain.gain.setTargetAtTime(vs*0.015,audioCtx.currentTime,0.1);
        doorShakeZ=dtd<45?(Math.random()-0.5)*(45-dtd)*0.0015:0;

        if(doorState==='valves_pressure'){
            if(valves[0].rotation.z<Math.PI*4){valves.forEach(v=>v.rotation.z+=delta*Math.PI);if(Math.random()>0.5)emitSteam(doorGroup.position.x,1,doorGroup.position.z);if(hissGain)hissGain.gain.setTargetAtTime(vs*0.1,audioCtx.currentTime,0.1);}
            else{doorState='vault_unlock';if(hissGain)hissGain.gain.setTargetAtTime(0,audioCtx.currentTime,0.1);if(vaultGain)vaultGain.gain.setTargetAtTime(vs*0.04,audioCtx.currentTime,0.1);}
        } else if(doorState==='vault_unlock'){
            if(vaultWG.rotation.z<Math.PI){vaultWG.rotation.z+=delta*(Math.PI/5);vaultWG.position.x-=delta*0.2;if(vaultGain)vaultGain.gain.setTargetAtTime(vs*0.04,audioCtx.currentTime,0.1);}
            else{doorState='unlatching';matIndicator.color.setHex(0x00ff00);if(vaultGain)vaultGain.gain.setTargetAtTime(0,audioCtx.currentTime,0.1);if(latchGain)latchGain.gain.setTargetAtTime(vs*0.06,audioCtx.currentTime,0.1);}
        } else if(doorState==='unlatching'){
            if(latchL.position.x>-6){const ls=delta*0.5;latchL.position.x-=ls;latchR.position.x+=ls;deadboltsL.forEach(b=>b.position.x-=ls*3);deadboltsR.forEach(b=>b.position.x+=ls*3);if(latchGain)latchGain.gain.setTargetAtTime(vs*0.06,audioCtx.currentTime,0.1);}
            else{doorState='retracting_pistons';if(latchGain)latchGain.gain.setTargetAtTime(0,audioCtx.currentTime,0.1);if(pistonGain)pistonGain.gain.setTargetAtTime(vs*0.15,audioCtx.currentTime,0.1);}
        } else if(doorState==='retracting_pistons'){
            if(pistonGroup.position.y<5){pistonGroup.position.y+=delta*1.0;if(pistonGain)pistonGain.gain.setTargetAtTime(vs*0.15,audioCtx.currentTime,0.1);}
            else{doorState='sliding';if(pistonGain)pistonGain.gain.setTargetAtTime(0,audioCtx.currentTime,0.1);if(gearGain)gearGain.gain.setTargetAtTime(vs*0.08,audioCtx.currentTime,0.1);}
        } else if(doorState==='sliding'){
            if(doorHL.position.x>-PW-2){
                const sl=delta*0.444;
                doorHL.position.x-=sl; doorHR.position.x+=sl;
                const gr=sl/GR; mainGL.rotation.z-=gr; mainGR2.rotation.z+=gr;
                const hr=GR/HGR; helpGL.rotation.z+=gr*hr; helpGR.rotation.z-=gr*hr;
                if(Math.random()>0.4)emitSpark(doorGroup.position.x-3,11+GR,doorGroup.position.z-0.8);
                if(Math.random()>0.4)emitSpark(doorGroup.position.x+3,11+GR,doorGroup.position.z-0.8);
                if(gearGain)gearGain.gain.setTargetAtTime(vs*0.08,audioCtx.currentTime,0.1);
            } else {
                doorState='open'; sirens.forEach(s=>s.light.intensity=0); matGlassRed.emissive.setHex(0x110000); doorShakeZ=0;
                const fot=audioCtx.currentTime+1.5;
                if(klaxonGain)klaxonGain.gain.linearRampToValueAtTime(0,fot);
                if(gearGain)gearGain.gain.linearRampToValueAtTime(0,fot);
            }
        }
    } else { doorShakeZ=0; }

    // ==== WIN CONDITION ====
    if(doorState==='open'&&camera.position.z>doorGroup.position.z+1.5&&!gameWon){
        gameWon=true; document.exitPointerLock();
        const ws=document.getElementById('win-screen');
        const fb=document.getElementById('fade-black');
        ws.style.display='flex'; fb.innerHTML='';
        setTimeout(()=>{fb.style.opacity='1';ws.style.opacity='1';},50);
        document.getElementById('finalTime').innerText=`FINAL TIME: ${formatTime(parseFloat(totalElapsed))}`;
        document.getElementById('finalOrbs').innerText=`ORBS RECOVERED: ${orbsCollected} / ${TOTAL_ORBS}`;
        saveRecord(nameInput.value||'UNKNOWN',totalElapsed,orbsCollected,'ESCAPED');
        try{if(klaxonOsc)klaxonOsc.stop();if(latchOsc)latchOsc.stop();if(pistonOsc)pistonOsc.stop();if(gearOsc)gearOsc.stop();if(vaultOsc)vaultOsc.stop();if(hissSrc)hissSrc.stop();}catch(e){}
    }
}

function animate(){ requestAnimationFrame(animate); update(); renderer.render(scene,camera); }
animate();

window.addEventListener('resize',()=>{camera.aspect=window.innerWidth/window.innerHeight;camera.updateProjectionMatrix();renderer.setSize(window.innerWidth,window.innerHeight);});

document.getElementById('reboot-btn').addEventListener('click',()=>{
    const d=document.getElementById('death-screen-ui');
    d.style.transition='opacity 0.5s'; d.style.opacity='0';
    setTimeout(()=>location.reload(),500);
});
