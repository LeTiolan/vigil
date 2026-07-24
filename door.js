import * as THREE from 'three';
import { scene } from './scene-setup.js';
import { getPos, exitGridX, exitGridZ } from './maze.js';
import { audioCtx, resume } from './audio.js';
import { registerSolid } from './collision.js';
import {
    matChrome, matDarkMetal, matSteel, matRusty, matGlassRed, matIndicator,
    matDoor, matHazard, matWarnYellow
} from './textures.js';

// ================================================================
//  DOOR GROUP — frame, gears, sirens, valves, wheel, gauges, pipes,
//  deadbolts, sliding panels, and the terminal control panel.
// ================================================================
export let doorState = 'closed';
export const doorWP = getPos(exitGridX, exitGridZ);
export const TERM_WX = doorWP.x, TERM_WZ = doorWP.z;
export const doorGroup = new THREE.Group();
doorGroup.position.set(doorWP.x, 0, doorWP.z);

// Door geometry: FH=frame height, FAR=distance in front toward player
// PW=panel half-width. NOTHING is registered solid below y=0.5.
const FH = 17, FAR = -2.0, PW = 5.0;

// ---- Door sound engine — all oscillator-based ----
export let doorAudio = {
    ctx: audioCtx, klaxonOsc: null, klaxonGain: null,
    grindOsc: null, grindGain: null, rumbleOsc: null, rumbleGain: null,
    steamSrc: null, steamGain: null, boltOsc: null, boltGain: null
};

export function initDoorAudio() {
    const a = doorAudio; a.ctx = audioCtx; resume();
    // Klaxon — warbling triangle wave
    a.klaxonOsc = a.ctx.createOscillator(); a.klaxonOsc.type = 'triangle'; a.klaxonOsc.frequency.value = 440;
    const klaxLFO = a.ctx.createOscillator(); klaxLFO.frequency.value = 3;
    const klaxMod = a.ctx.createGain(); klaxMod.gain.value = 120;
    klaxLFO.connect(klaxMod); klaxMod.connect(a.klaxonOsc.frequency); klaxLFO.start();
    a.klaxonGain = a.ctx.createGain(); a.klaxonGain.gain.value = 0;
    a.klaxonOsc.connect(a.klaxonGain); a.klaxonGain.connect(a.ctx.destination); a.klaxonOsc.start();
    // Gear grind — sawtooth with bandpass
    a.grindOsc = a.ctx.createOscillator(); a.grindOsc.type = 'sawtooth'; a.grindOsc.frequency.value = 38;
    const gbp = a.ctx.createBiquadFilter(); gbp.type = 'bandpass'; gbp.frequency.value = 180; gbp.Q.value = 2;
    a.grindGain = a.ctx.createGain(); a.grindGain.gain.value = 0;
    a.grindOsc.connect(gbp); gbp.connect(a.grindGain); a.grindGain.connect(a.ctx.destination); a.grindOsc.start();
    // Deep rumble — very low square wave
    a.rumbleOsc = a.ctx.createOscillator(); a.rumbleOsc.type = 'square'; a.rumbleOsc.frequency.value = 22;
    const rlp = a.ctx.createBiquadFilter(); rlp.type = 'lowpass'; rlp.frequency.value = 80;
    a.rumbleGain = a.ctx.createGain(); a.rumbleGain.value = 0;
    a.rumbleOsc.connect(rlp); rlp.connect(a.rumbleGain); a.rumbleGain.connect(a.ctx.destination); a.rumbleOsc.start();
    // Steam hiss — white noise highpass
    const nBuf = a.ctx.createBuffer(1, a.ctx.sampleRate * 2, a.ctx.sampleRate);
    const nd = nBuf.getChannelData(0); for (let i = 0; i < nd.length; i++) nd[i] = Math.random() * 2 - 1;
    a.steamSrc = a.ctx.createBufferSource(); a.steamSrc.buffer = nBuf; a.steamSrc.loop = true;
    const shp = a.ctx.createBiquadFilter(); shp.type = 'highpass'; shp.frequency.value = 1200;
    a.steamGain = a.ctx.createGain(); a.steamGain.gain.value = 0;
    a.steamSrc.connect(shp); shp.connect(a.steamGain); a.steamGain.connect(a.ctx.destination); a.steamSrc.start();
    // Bolt clang — sawtooth burst played on demand via function
    a.boltOsc = a.ctx.createOscillator(); a.boltOsc.type = 'sawtooth'; a.boltOsc.frequency.value = 95;
    a.boltGain = a.ctx.createGain(); a.boltGain.gain.value = 0;
    a.boltOsc.connect(a.boltGain); a.boltGain.connect(a.ctx.destination); a.boltOsc.start();
}

export function doorSnd(which, vol) {
    const a = doorAudio; if (!a.klaxonGain) return;
    const t = a.ctx.currentTime;
    const set = (g, v) => { if (g) g.gain.setTargetAtTime(v, t, 0.12); };
    if (which === 'klaxon') set(a.klaxonGain, vol);
    if (which === 'grind') set(a.grindGain, vol);
    if (which === 'rumble') { if (a.rumbleGain) a.rumbleGain.gain.setTargetAtTime(vol, t, 0.12); }
    if (which === 'steam') set(a.steamGain, vol);
    if (which === 'bolt') {
        if (a.boltGain) {
            a.boltGain.gain.setValueAtTime(vol, t);
            a.boltGain.gain.exponentialRampToValueAtTime(0.001, t + 0.18);
            a.boltOsc.frequency.setValueAtTime(95, t);
            a.boltOsc.frequency.exponentialRampToValueAtTime(35, t + 0.18);
        }
    }
}

export function stopAllDoorAudio() {
    const a = doorAudio;
    try {
        if (a.klaxonOsc) a.klaxonOsc.stop(); if (a.grindOsc) a.grindOsc.stop();
        if (a.rumbleOsc) a.rumbleOsc.stop(); if (a.steamSrc) a.steamSrc.stop();
        if (a.boltOsc) a.boltOsc.stop();
    } catch (_) { }
}
// GEAR FACTORY — used throughout the door
const mkGear = (r, depth, teeth, mat) => {
    const g = new THREE.Group();
    const cyl = new THREE.Mesh(new THREE.CylinderGeometry(r * 0.82, r * 0.82, depth, 18), mat || matChrome);
    cyl.rotation.x = Math.PI / 2;
    g.add(cyl);
    const hub = new THREE.Mesh(new THREE.CylinderGeometry(r * 0.24, r * 0.24, depth + 0.25, 10), matDarkMetal); hub.rotation.x = Math.PI / 2; g.add(hub);
    const tGeo = new THREE.BoxGeometry((Math.PI * r * 2) / (teeth * 2.1), r * 0.28, depth * 0.88);
    for (let i = 0; i < teeth; i++) {
        const a = (i / teeth) * Math.PI * 2;
        const t = new THREE.Mesh(tGeo, matSteel); t.position.set(Math.cos(a) * r * 0.92, Math.sin(a) * r * 0.92, 0); t.rotation.z = a + Math.PI / 2; g.add(t);
    }
    for (let i = 0; i < 6; i++) {
        const a = (i / 6) * Math.PI * 2;
        const sp = new THREE.Mesh(new THREE.BoxGeometry(r * 0.68, r * 0.11, depth * 0.66), matDarkMetal);
        sp.position.set(Math.cos(a) * r * 0.44, Math.sin(a) * r * 0.44, 0); sp.rotation.z = a + Math.PI / 2; g.add(sp);
    }
    return g;
};

// ── FRAME: Thick I-beam pillars, NO floor geometry ────────────────
const mkIPillar = (xs) => {
    const g = new THREE.Group(); g.position.set(xs * 6.6, FH / 2, FAR);
    const web = new THREE.Mesh(new THREE.BoxGeometry(0.55, FH, 2.2), matRusty); g.add(web);
    const tF = new THREE.Mesh(new THREE.BoxGeometry(3.6, 0.75, 2.6), matRusty); tF.position.y = FH / 2 - 0.38; g.add(tF);
    for (const py of [FH * 0.28, FH * 0.0, -FH * 0.22]) {
        const mF = new THREE.Mesh(new THREE.BoxGeometry(3.2, 0.42, 2.2), matRusty); mF.position.y = py; g.add(mF);
    }
    const gp = new THREE.Mesh(new THREE.BoxGeometry(0.65, 3.0, 2.2), matDarkMetal); gp.position.y = FH / 2 - 2.4; g.add(gp);
    // Bolt rows on flange face
    for (const by of [FH / 2 - 0.38, FH * 0.28, FH * 0.0, -FH * 0.22]) for (const bx of [-1.2, 0, 1.2]) {
        const bolt = new THREE.Mesh(new THREE.CylinderGeometry(0.13, 0.13, 0.16, 8), matChrome);
        bolt.rotation.x = Math.PI / 2; bolt.position.set(bx, by, 1.18); g.add(bolt);
    }
    doorGroup.add(g);
    // Collision hitbox — full height, but player walks between pillars
    const hb = new THREE.Mesh(new THREE.BoxGeometry(3.6, FH, 2.6), new THREE.MeshBasicMaterial({ visible: false }));
    hb.position.set(xs * 6.6, FH / 2, FAR); doorGroup.add(hb); registerSolid(hb);
};
mkIPillar(-1); mkIPillar(1);

// Heavy lintel spanning the top — above the walkway
const lintel = new THREE.Mesh(new THREE.BoxGeometry(17.0, 3.4, 2.6), matRusty);
lintel.position.set(0, FH + 1.4, FAR); lintel.castShadow = true;
doorGroup.add(lintel); registerSolid(lintel);

// Cross-braces from upper pillar to lintel centre (decorative, connected)
for (const xs of [-1, 1]) {
    const bLen = 6.2; const brace = new THREE.Mesh(new THREE.BoxGeometry(0.3, bLen, 0.5), matDarkMetal);
    brace.position.set(xs * 3.2, FH - 0.5, FAR + 0.3); brace.rotation.z = xs * 0.5; doorGroup.add(brace);
}

// ── WARNING SIRENS ────────────────────────────────────────────────
export const sirens = [];
const mkSiren = (x, z) => {
    const sg = new THREE.Group(); sg.position.set(x, FH - 1.2, z);
    sg.add(new THREE.Mesh(new THREE.CylinderGeometry(0.38, 0.55, 0.95, 14), new THREE.MeshLambertMaterial({ color: 0x0c0c0c })));
    const dome = new THREE.Mesh(new THREE.SphereGeometry(0.40, 12, 8, 0, Math.PI * 2, 0, Math.PI / 2), matGlassRed);
    dome.position.y = 0.08; sg.add(dome);
    const ref = new THREE.Mesh(new THREE.BoxGeometry(0.65, 0.11, 0.11), new THREE.MeshLambertMaterial({ color: 0xaaaa00 }));
    sg.add(ref);
    const sl = new THREE.SpotLight(0xff2200, 0, 60, Math.PI / 5, 0.4, 1);
    sl.position.set(0, 0.2, 0); sl.target.position.set(0, -8, 6); sl.castShadow = false;
    sg.add(sl); sg.add(sl.target); doorGroup.add(sg);
    sirens.push({ group: sg, light: sl, reflector: ref });
};
mkSiren(-6.2, FAR - 0.4); mkSiren(6.2, FAR - 0.4);
mkSiren(-6.2, FAR + 0.4); mkSiren(6.2, FAR + 0.4);


// Status indicator bars (glow green when unlocked)
export const matInd = matIndicator;
export const indL = new THREE.Mesh(new THREE.BoxGeometry(0.2, FH, 0.2), matInd); indL.position.set(-5.0, FH / 2, FAR); doorGroup.add(indL);
export const indR = new THREE.Mesh(new THREE.BoxGeometry(0.2, FH, 0.2), matInd); indR.position.set(5.0, FH / 2, FAR); doorGroup.add(indR);

// ── DOOR PANELS — two slabs that slide apart ───────────────────────
export const doorHL = new THREE.Group(); doorHL.position.set(-PW / 2, FH / 2, 0.5); doorGroup.add(doorHL);
export const doorHR = new THREE.Group(); doorHR.position.set(PW / 2, FH / 2, 0.5); doorGroup.add(doorHR);

const panGeo = new THREE.BoxGeometry(PW, FH, 1.3);
const pL2 = new THREE.Mesh(panGeo, matDoor); pL2.castShadow = true; doorHL.add(pL2); registerSolid(pL2, true);
const pR2 = new THREE.Mesh(panGeo, matDoor); pR2.castShadow = true; doorHR.add(pR2); registerSolid(pR2, true);

// Hazard edge strips
const hzG = new THREE.BoxGeometry(0.45, FH, 0.38);
const hzL = new THREE.Mesh(hzG, matHazard); hzL.position.set(PW / 2 - 0.22, 0, 0.74); doorHL.add(hzL);
const hzR = new THREE.Mesh(hzG, matHazard); hzR.position.set(-PW / 2 + 0.22, 0, 0.74); doorHR.add(hzR);

// Rivet rows on panel face
for (const px of [-PW / 2 + 0.5, PW / 2 - 0.5]) for (let py = -FH / 2 + 1.2; py < FH / 2; py += 2.1) {
    const rv = new THREE.Mesh(new THREE.CylinderGeometry(0.1, 0.1, 0.1, 8), matChrome);
    rv.rotation.x = Math.PI / 2; rv.position.set(px, py, 0.68); doorHL.add(rv);
    const rv2 = rv.clone(); rv2.position.set(-px, py, 0.68); doorHR.add(rv2);
}

// ── GEAR TRAIN — horizontal rack on panel tops, drive gears above lintel ──
const tGeo2 = new THREE.BoxGeometry(PW, 0.62, 0.52);
const rackL2 = new THREE.Mesh(tGeo2, matSteel); rackL2.position.set(0, FH / 2 + 0.31, 0); doorHL.add(rackL2);
const rackR2 = new THREE.Mesh(tGeo2, matSteel); rackR2.position.set(0, FH / 2 + 0.31, 0); doorHR.add(rackR2);
const toothG = new THREE.BoxGeometry(0.28, 0.38, 0.48);
for (let tx = -PW / 2 + 0.28; tx < PW / 2; tx += 0.58) {
    const tL2 = new THREE.Mesh(toothG, matSteel); tL2.position.set(tx, FH / 2 + 0.62, 0); doorHL.add(tL2);
    const tR2 = new THREE.Mesh(toothG, matSteel); tR2.position.set(tx, FH / 2 + 0.62, 0); doorHR.add(tR2);
}

// Main drive gears — one per side, meshing with rack
export const GR = 2.1, HGR = 1.0;
const gearY = FH + 1.8, gearZ = FAR + 0.65;
export const mgL = mkGear(GR, 0.75, 15); mgL.position.set(-PW - GR + 0.3, gearY, gearZ); doorGroup.add(mgL);
export const mgR = mkGear(GR, 0.75, 15); mgR.position.set(PW + GR - 0.3, gearY, gearZ); doorGroup.add(mgR);
// Idler gears connected to motors
export const hgL = mkGear(HGR, 0.55, 9); hgL.position.set(-PW - GR * 2.1 + 0.2, gearY + GR + HGR - 0.25, gearZ); doorGroup.add(hgL);
export const hgR = mkGear(HGR, 0.55, 9); hgR.position.set(PW + GR * 2.1 - 0.2, gearY + GR + HGR - 0.25, gearZ); doorGroup.add(hgR);
export const gearYPos = gearY, gearZPos = gearZ;
// Motor housings — bolted to lintel underside
const mhMat = new THREE.MeshLambertMaterial({ color: 0x0a0a0a });
const mhL = new THREE.Mesh(new THREE.BoxGeometry(3.1, 2.5, 1.9), mhMat); mhL.position.set(-PW - GR + 0.3, gearY + GR + 1.5, gearZ - 0.4); doorGroup.add(mhL);
const mhR = new THREE.Mesh(new THREE.BoxGeometry(3.1, 2.5, 1.9), mhMat); mhR.position.set(PW + GR - 0.3, gearY + GR + 1.5, gearZ - 0.4); doorGroup.add(mhR);
// Motor output shafts (connected visually from motor to gear)
const shaftMat = new THREE.MeshLambertMaterial({ color: 0x333333 });
const shL = new THREE.Mesh(new THREE.CylinderGeometry(0.22, 0.22, 1.0, 10), shaftMat); shL.rotation.x = Math.PI / 2; shL.position.set(-PW - GR + 0.3, gearY, gearZ - 0.38); doorGroup.add(shL);
const shR = new THREE.Mesh(new THREE.CylinderGeometry(0.22, 0.22, 1.0, 10), shaftMat); shR.rotation.x = Math.PI / 2; shR.position.set(PW + GR - 0.3, gearY, gearZ - 0.38); doorGroup.add(shR);
// Gear indicator lights on motor housings
const mIndL = new THREE.Mesh(new THREE.SphereGeometry(0.14, 8, 6), matInd); mIndL.position.set(-PW - GR + 0.3 - 1.0, gearY + GR + 2.2, gearZ + 0.6); doorGroup.add(mIndL);
const mIndR = new THREE.Mesh(new THREE.SphereGeometry(0.14, 8, 6), matInd); mIndR.position.set(PW + GR - 0.3 + 1.0, gearY + GR + 2.2, gearZ + 0.6); doorGroup.add(mIndR);

// ── LOCKING BOLTS — horizontal, above floor (never block walkway) ─
export const deadboltsL = [], deadboltsR = [];
for (const yOff of [FH * 0.52, FH * 0.22, -FH * 0.06]) {
    // Left bolt group
    const bL = new THREE.Group(); bL.position.set(-PW - 0.4, yOff, FAR - 0.6);
    const bBody = new THREE.Mesh(new THREE.BoxGeometry(2.6, 0.58, 0.58), matChrome); bBody.position.x = -1.1; bL.add(bBody);
    const bHead = new THREE.Mesh(new THREE.BoxGeometry(0.82, 0.88, 0.88), matSteel); bHead.position.x = -2.55; bL.add(bHead);
    const bSlot = new THREE.Mesh(new THREE.BoxGeometry(1.0, 0.82, 0.82), matDarkMetal); bSlot.position.x = -3.7; bL.add(bSlot);
    // Connecting rod from bolt to frame — shows it's anchored
    const bRod = new THREE.Mesh(new THREE.CylinderGeometry(0.12, 0.12, 1.2, 8), shaftMat); bRod.rotation.z = Math.PI / 2; bRod.position.x = -4.5; bL.add(bRod);
    doorGroup.add(bL); deadboltsL.push(bL);
    // Right bolt group (mirror)
    const bR = new THREE.Group(); bR.position.set(PW + 0.4, yOff, FAR - 0.6);
    const bRBody = new THREE.Mesh(new THREE.BoxGeometry(2.6, 0.58, 0.58), matChrome); bRBody.position.x = 1.1; bR.add(bRBody);
    const bRHead = new THREE.Mesh(new THREE.BoxGeometry(0.82, 0.88, 0.88), matSteel); bRHead.position.x = 2.55; bR.add(bRHead);
    const bRSlot = new THREE.Mesh(new THREE.BoxGeometry(1.0, 0.82, 0.82), matDarkMetal); bRSlot.position.x = 3.7; bR.add(bRSlot);
    const bRRod = new THREE.Mesh(new THREE.CylinderGeometry(0.12, 0.12, 1.2, 8), shaftMat); bRRod.rotation.z = Math.PI / 2; bRRod.position.x = 4.5; bR.add(bRRod);
    doorGroup.add(bR); deadboltsR.push(bR);
}

// ── PRESSURE VALVES ───────────────────────────────────────────────
export const valves = [];
for (const [xv, yv] of [[-3.6, FH * 0.44], [-3.6, FH * 0.12], [3.6, FH * 0.44], [3.6, FH * 0.12]]) {
    const vG = new THREE.Group();
    const vBody = new THREE.Mesh(new THREE.CylinderGeometry(0.36, 0.36, 0.72, 10), matSteel); vG.add(vBody);
    const vH1 = new THREE.Mesh(new THREE.BoxGeometry(1.5, 0.2, 0.2), matWarnYellow); vH1.position.y = 0.46; vG.add(vH1);
    const vH2 = new THREE.Mesh(new THREE.BoxGeometry(0.2, 0.2, 1.5), matWarnYellow); vH2.position.y = 0.46; vG.add(vH2);
    // Pipe stub connecting valve to door panel
    const vStub = new THREE.Mesh(new THREE.CylinderGeometry(0.14, 0.14, 0.8, 8), matDarkMetal); vStub.position.y = -0.75; vG.add(vStub);
    vG.position.set(xv, yv, FAR); vG.rotation.x = Math.PI / 2;
    doorGroup.add(vG); valves.push(vG);
}

// ── VAULT WHEEL (centre, connected via recessed shaft) ────────────
export const vaultWG = new THREE.Group(); vaultWG.position.set(0, FH * 0.40, FAR + 0.5); doorGroup.add(vaultWG);
const vRim = new THREE.Mesh(new THREE.TorusGeometry(1.9, 0.22, 10, 28), matRusty); vaultWG.add(vRim);
const vDisc = new THREE.Mesh(new THREE.CylinderGeometry(1.9, 1.9, 0.52, 26), matChrome); vDisc.rotation.x = Math.PI / 2; vaultWG.add(vDisc);
for (let i = 0; i < 8; i++) { const a = (i / 8) * Math.PI * 2; const sp = new THREE.Mesh(new THREE.BoxGeometry(3.4, 0.28, 0.28), matSteel); sp.rotation.z = a; vaultWG.add(sp); }
const vHub2 = new THREE.Mesh(new THREE.CylinderGeometry(0.48, 0.48, 0.72, 12), matDarkMetal); vHub2.rotation.x = Math.PI / 2; vaultWG.add(vHub2);
// Shaft from wheel back into door panel — shows it's connected
const wShaft = new THREE.Mesh(new THREE.CylinderGeometry(0.2, 0.2, 0.8, 10), shaftMat); wShaft.rotation.x = Math.PI / 2; wShaft.position.z = -0.65; vaultWG.add(wShaft);

// ── PRESSURE GAUGES ───────────────────────────────────────────────
const mkGauge2 = (xg, yg) => {
    const g = new THREE.Group(); g.position.set(xg, yg, FAR);
    const face = new THREE.Mesh(new THREE.CylinderGeometry(0.62, 0.62, 0.18, 16), new THREE.MeshLambertMaterial({ color: 0x080808 }));
    face.rotation.x = Math.PI / 2; g.add(face);
    g.add(new THREE.Mesh(new THREE.TorusGeometry(0.62, 0.09, 8, 20), matChrome));
    const needle = new THREE.Mesh(new THREE.BoxGeometry(0.06, 0.46, 0.07), new THREE.MeshBasicMaterial({ color: 0xff3300 }));
    needle.position.set(0.18, 0.15, 0.12); needle.rotation.z = -0.55; g.add(needle);
    doorGroup.add(g);
};
mkGauge2(-5.5, FH * 0.70); mkGauge2(5.5, FH * 0.70);
mkGauge2(-5.5, FH * 0.22); mkGauge2(5.5, FH * 0.22);

// ── PIPE NETWORK — all connected to real structures ───────────────
const pipMat = new THREE.MeshLambertMaterial({ color: 0x181818 });
const mkPipe2 = (x, y1, y2, z) => {
    const len = Math.abs(y2 - y1);
    const p = new THREE.Mesh(new THREE.CylinderGeometry(0.12, 0.12, len, 8), pipMat);
    p.position.set(x, (y1 + y2) / 2, z); doorGroup.add(p);
    for (const ey of [y1, y2]) { const c = new THREE.Mesh(new THREE.CylinderGeometry(0.19, 0.19, 0.2, 8), pipMat); c.position.set(x, ey, z); doorGroup.add(c); }
};
// Vertical pipe runs along pillar faces
mkPipe2(-7.2, 2.2, FH - 1.2, FAR - 0.35);
mkPipe2(7.2, 2.2, FH - 1.2, FAR - 0.35);
// Horizontal crossover pipes at mid height (connecting left to right)
const hPipe1 = new THREE.Mesh(new THREE.CylinderGeometry(0.12, 0.12, 8.0, 8), pipMat);
hPipe1.rotation.z = Math.PI / 2; hPipe1.position.set(0, FH * 0.35, FAR - 0.4); doorGroup.add(hPipe1);
const hPipe2 = new THREE.Mesh(new THREE.CylinderGeometry(0.12, 0.12, 8.0, 8), pipMat);
hPipe2.rotation.z = Math.PI / 2; hPipe2.position.set(0, FH * 0.60, FAR - 0.4); doorGroup.add(hPipe2);
// Diagonal pipe from lower valve to gauge
for (const xs of [-1, 1]) {
    const dp = new THREE.Mesh(new THREE.CylinderGeometry(0.1, 0.1, 2.5, 8), pipMat);
    dp.position.set(xs * 4.4, FH * 0.27, FAR - 0.3); dp.rotation.z = xs * 0.35; doorGroup.add(dp);
}

// ── TERMINAL CONTROL PANEL ──────────────────────────────────────────
// NOTE: this whole panel (termBtn, termScreenMat, termLight, ledMat,
// termBtnMat) was referenced throughout the original codebase's E-to-
// activate / orb-collection logic but never actually built anywhere —
// a latent bug from before the file split, not something that used to
// work. Reconstructed here so the "collect all orbs -> activate
// terminal -> door opens" sequence has something to click on.
const termGroup = new THREE.Group();
termGroup.position.set(-4.2, 3.4, FAR + 1.35);
doorGroup.add(termGroup);

export const termBtnMat = new THREE.MeshStandardMaterial({ color: 0x555555, roughness: 0.4, metalness: 0.5 });
const termHousing = new THREE.Mesh(new THREE.BoxGeometry(1.6, 2.0, 0.5), matDarkMetal);
termGroup.add(termHousing); registerSolid(termHousing);

export const termScreenMat = new THREE.MeshBasicMaterial({ color: 0x220000 });
const termScreen = new THREE.Mesh(new THREE.PlaneGeometry(1.1, 0.7), termScreenMat);
termScreen.position.set(0, 0.5, 0.26);
termGroup.add(termScreen);

export const termLight = new THREE.PointLight(0xff2200, 0.6, 4);
termLight.position.set(0, 0.5, 0.5);
termGroup.add(termLight);

export const ledMat = new THREE.MeshBasicMaterial({ color: 0x660000 });
const led = new THREE.Mesh(new THREE.CylinderGeometry(0.05, 0.05, 0.04, 8), ledMat);
led.rotation.x = Math.PI / 2;
led.position.set(0.5, 0.85, 0.26);
termGroup.add(led);

export const termBtn = new THREE.Mesh(new THREE.CylinderGeometry(0.18, 0.18, 0.12, 12), termBtnMat);
termBtn.rotation.x = Math.PI / 2;
termBtn.position.set(0, -0.5, 0.56);
termGroup.add(termBtn);

scene.add(doorGroup);

export function setDoorState(next) { doorState = next; }