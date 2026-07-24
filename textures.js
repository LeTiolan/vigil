import * as THREE from 'three';

// ================================================================
//  TEXTURES — 256x256 NearestFilter PSX style
// ================================================================
function makeTex(c, ru, rv) {
    const t = new THREE.CanvasTexture(c);
    t.magFilter = THREE.NearestFilter; t.minFilter = THREE.NearestFilter; t.generateMipmaps = false;
    t.wrapS = t.wrapT = THREE.RepeatWrapping; if (ru) t.repeat.set(ru, rv || ru); return t;
}

// Stone wall — mortar lines, varied blocks, cracks, moisture stains
function mkWallTex() {
    const c = document.createElement('canvas'); c.width = 256; c.height = 256; const ctx = c.getContext('2d');
    ctx.fillStyle = '#0d160d'; ctx.fillRect(0, 0, 256, 256);
    const bW = 64, bH = 48;
    for (let row = 0; row < 6; row++) for (let col = -1; col < 5; col++) {
        const ox = (row % 2 === 0) ? 0 : bW / 2, bx = col * bW + ox, by = row * bH;
        const sh = Math.floor(Math.random() * 22), g = 28 + sh, gv = 46 + sh;
        ctx.fillStyle = `rgb(${g},${gv},${g})`; ctx.fillRect(bx + 2, by + 2, bW - 4, bH - 4);
        // Surface noise — lots of it for PSX crunch
        for (let i = 0; i < 80; i++) { ctx.fillStyle = `rgba(0,0,0,${Math.random() * 0.22})`; ctx.fillRect(bx + 2 + Math.random() * (bW - 4), by + 2 + Math.random() * (bH - 4), Math.random() * 6 + 1, Math.random() * 5 + 1); }
        // Lighter highlight flecks
        for (let i = 0; i < 15; i++) { ctx.fillStyle = `rgba(255,255,200,${Math.random() * 0.04})`; ctx.fillRect(bx + 2 + Math.random() * (bW - 4), by + 2 + Math.random() * (bH - 4), Math.random() * 3 + 1, Math.random() * 2 + 1); }
        // Moisture streak
        if (Math.random() > 0.45) { const sx = bx + 6 + Math.random() * (bW - 12); const gr = ctx.createLinearGradient(sx, by, sx + 3, by + bH); gr.addColorStop(0, 'rgba(40,20,5,0)'); gr.addColorStop(0.3, 'rgba(55,28,4,0.55)'); gr.addColorStop(1, 'rgba(35,15,2,0)'); ctx.fillStyle = gr; ctx.fillRect(sx, by, 4, bH); }
        // Crack (random 30% chance)
        if (Math.random() > 0.7) { ctx.strokeStyle = `rgba(0,0,0,0.7)`; ctx.lineWidth = 1; ctx.beginPath(); const cx2 = bx + 8 + Math.random() * (bW - 16), cy2 = by + 4 + Math.random() * (bH - 8); ctx.moveTo(cx2, cy2); ctx.lineTo(cx2 + Math.random() * 12 - 6, cy2 + Math.random() * 14 + 4); ctx.stroke(); }
        // Top highlight
        ctx.fillStyle = 'rgba(255,255,255,0.035)'; ctx.fillRect(bx + 2, by + 2, bW - 4, 2);
    }
    // Mortar
    ctx.strokeStyle = '#060c06'; ctx.lineWidth = 2;
    for (let r = 0; r <= 6; r++) { ctx.beginPath(); ctx.moveTo(0, r * bH); ctx.lineTo(256, r * bH); ctx.stroke(); }
    for (let r = 0; r < 6; r++) { const ox = (r % 2 === 0) ? 0 : bW / 2; for (let c2 = -1; c2 <= 5; c2++) { const bx = c2 * bW + ox; ctx.beginPath(); ctx.moveTo(bx, r * bH); ctx.lineTo(bx, (r + 1) * bH); ctx.stroke(); } }
    // Corner cracks on some blocks — drawn over mortar
    for (let i = 0; i < 8; i++) {
        const cx3 = Math.random() * 240, cy3 = Math.random() * 240;
        ctx.strokeStyle = 'rgba(0,0,0,0.5)'; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(cx3, cy3);
        let cx4 = cx3, cy4 = cy3; for (let s = 0; s < 4; s++) { cx4 += Math.random() * 8 - 4; cy4 += Math.random() * 6 + 2; ctx.lineTo(cx4, cy4); } ctx.stroke();
    }
    return makeTex(c, 1.2, 1.4);
}

// Heavy metal floor — diamond plate grating with dirt/grease
function mkFloorTex() {
    const c = document.createElement('canvas'); c.width = 256; c.height = 256; const ctx = c.getContext('2d');
    ctx.fillStyle = '#111111'; ctx.fillRect(0, 0, 256, 256);
    // Diamond plate pattern — rows of offset diamonds
    const cell = 16; ctx.fillStyle = '#1c1c1c';
    for (let y = 0; y < 256; y += cell) { for (let x = (y / cell % 2 === 0) ? 0 : cell / 2; x < 256; x += cell) {
        ctx.beginPath(); ctx.moveTo(x + cell / 2, y); ctx.lineTo(x + cell, y + cell / 2); ctx.lineTo(x + cell / 2, y + cell); ctx.lineTo(x, y + cell / 2); ctx.closePath(); ctx.fill();
        ctx.strokeStyle = 'rgba(0,0,0,0.6)'; ctx.lineWidth = 1; ctx.stroke();
    } }
    // Bolts at seam crossings
    for (let y = 0; y < 256; y += 64) for (let x = 0; x < 256; x += 64) {
        ctx.fillStyle = '#0e0e0e'; ctx.beginPath(); ctx.arc(x, y, 5, 0, Math.PI * 2); ctx.fill();
        ctx.fillStyle = '#080808'; ctx.beginPath(); ctx.arc(x, y, 2.5, 0, Math.PI * 2); ctx.fill();
    }
    // Grease/dirt stains
    for (let i = 0; i < 30; i++) { ctx.fillStyle = `rgba(0,0,0,${Math.random() * 0.3 + 0.1})`; ctx.fillRect(Math.random() * 240, Math.random() * 240, Math.random() * 30 + 5, Math.random() * 3 + 1); }
    for (let i = 0; i < 12; i++) { ctx.fillStyle = `rgba(255,120,0,${Math.random() * 0.06})`; ctx.fillRect(Math.random() * 240, Math.random() * 240, Math.random() * 20 + 4, Math.random() * 20 + 4); }
    return makeTex(c, 4, 4);
}

// Concrete ceiling — cracked panels with water damage
function mkCeilTex() {
    const c = document.createElement('canvas'); c.width = 256; c.height = 256; const ctx = c.getContext('2d');
    ctx.fillStyle = '#0e0f10'; ctx.fillRect(0, 0, 256, 256);
    // Panels
    ctx.strokeStyle = '#090a0b'; ctx.lineWidth = 3;
    for (let x = 0; x <= 256; x += 64) { ctx.beginPath(); ctx.moveTo(x, 0); ctx.lineTo(x, 256); ctx.stroke(); }
    for (let y = 0; y <= 256; y += 64) { ctx.beginPath(); ctx.moveTo(0, y); ctx.lineTo(256, y); ctx.stroke(); }
    // Rust/water stains
    for (let i = 0; i < 20; i++) { const gx = Math.random() * 200 + 28, gy = Math.random() * 200 + 28; const gr = ctx.createRadialGradient(gx, gy, 0, gx, gy, 25 + Math.random() * 20); gr.addColorStop(0, 'rgba(60,30,10,0.25)'); gr.addColorStop(1, 'rgba(0,0,0,0)'); ctx.fillStyle = gr; ctx.fillRect(gx - 40, gy - 40, 80, 80); }
    // Noise
    for (let i = 0; i < 5000; i++) { ctx.fillStyle = `rgba(0,0,0,${Math.random() * 0.18})`; ctx.fillRect(Math.random() * 254, Math.random() * 254, Math.random() * 2 + 1, Math.random() * 2 + 1); }
    // Cracks
    for (let i = 0; i < 6; i++) { ctx.strokeStyle = 'rgba(0,0,0,0.6)'; ctx.lineWidth = 1; ctx.beginPath(); let cx5 = Math.random() * 200 + 28, cy5 = Math.random() * 200 + 28; ctx.moveTo(cx5, cy5); for (let s = 0; s < 6; s++) { cx5 += Math.random() * 12 - 6; cy5 += Math.random() * 12 - 6; ctx.lineTo(cx5, cy5); } ctx.stroke(); }
    return makeTex(c, 3, 3);
}

// Heavy industrial door steel — riveted plates
function mkDoorTex() {
    const c = document.createElement('canvas'); c.width = 128; c.height = 256; const ctx = c.getContext('2d');
    ctx.fillStyle = '#181818'; ctx.fillRect(0, 0, 128, 256);
    // Plate divisions
    for (let y = 0; y <= 256; y += 64) { ctx.strokeStyle = '#0a0a0a'; ctx.lineWidth = 3; ctx.beginPath(); ctx.moveTo(0, y); ctx.lineTo(128, y); ctx.stroke(); }
    // Rivet rows
    for (let y = 32; y < 256; y += 64) for (let x = 14; x < 128; x += 18) { ctx.fillStyle = '#111'; ctx.beginPath(); ctx.arc(x, y, 4, 0, Math.PI * 2); ctx.fill(); ctx.fillStyle = '#0a0a0a'; ctx.beginPath(); ctx.arc(x, y, 2, 0, Math.PI * 2); ctx.fill(); }
    // Grime
    for (let i = 0; i < 3000; i++) { ctx.fillStyle = `rgba(0,0,0,${Math.random() * 0.2})`; ctx.fillRect(Math.random() * 126, Math.random() * 254, Math.random() * 4 + 1, Math.random() * 3 + 1); }
    // Scratches
    for (let i = 0; i < 8; i++) { ctx.strokeStyle = `rgba(180,180,180,${Math.random() * 0.06})`; ctx.lineWidth = 1; ctx.beginPath(); const sy = Math.random() * 240; ctx.moveTo(Math.random() * 20, sy); ctx.lineTo(Math.random() * 20 + 80, sy + Math.random() * 20 - 10); ctx.stroke(); }
    return makeTex(c);
}

function mkGrimeTex() {
    const c = document.createElement('canvas'); c.width = 128; c.height = 128; const ctx = c.getContext('2d');
    ctx.fillStyle = '#1a1a1a'; ctx.fillRect(0, 0, 128, 128);
    for (let i = 0; i < 4000; i++) { ctx.fillStyle = Math.random() > 0.5 ? `rgba(0,0,0,${Math.random() * 0.18})` : `rgba(70,55,30,${Math.random() * 0.1})`; ctx.beginPath(); ctx.arc(Math.random() * 128, Math.random() * 128, Math.random() * 2.5, 0, Math.PI * 2); ctx.fill(); }
    return makeTex(c);
}

function mkHazardTex() {
    const c = document.createElement('canvas'); c.width = 128; c.height = 128; const ctx = c.getContext('2d');
    ctx.fillStyle = '#b89028'; ctx.fillRect(0, 0, 128, 128); ctx.fillStyle = '#0c0c0c';
    for (let i = -128; i < 256; i += 32) { ctx.beginPath(); ctx.moveTo(i, 0); ctx.lineTo(i + 16, 0); ctx.lineTo(i + 144, 128); ctx.lineTo(i + 128, 128); ctx.fill(); }
    return makeTex(c);
}

// Orb animated fluid canvas — updated each frame
const orbCanvas = document.createElement('canvas'); orbCanvas.width = 64; orbCanvas.height = 64;
const orbCtx = orbCanvas.getContext('2d');
export const orbTex = new THREE.CanvasTexture(orbCanvas);
orbTex.magFilter = THREE.LinearFilter; orbTex.minFilter = THREE.LinearFilter;

const orbImageData = orbCtx.createImageData(64, 64);

export function updateOrbTex(now) {
    const t = now * 0.0018; const w = 64, h = 64;
    const id = orbImageData;
    const data = id.data;

    for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
        const nx = (x / w) * 2 - 1, ny = (y / h) * 2 - 1, r = Math.sqrt(nx * nx + ny * ny);
        if (r > 1) { data[(y * w + x) * 4 + 3] = 0; continue; }
        // Multiple wave interference for water droplet look
        const wave = Math.sin(nx * 9 + t * 2.8) * 0.45 + Math.sin(ny * 7 + t * 2.2) * 0.45 + Math.sin((nx + ny) * 6 + t * 1.8) * 0.35 + Math.sin(r * 14 - t * 3.5) * 0.4 + Math.sin((nx - ny) * 5 + t * 2.5) * 0.3;
        const intensity = (wave + 2.5) / 5.0;
        const edge = 1 - r * r; const b = edge * intensity;
        data[(y * w + x) * 4 + 0] = Math.min(255, Math.floor(b * 30 + b * 40 * Math.sin(t + r * 3)));
        data[(y * w + x) * 4 + 1] = Math.min(255, Math.floor(b * 210 + b * 45 * Math.sin(t * 1.3 + nx * 4)));
        data[(y * w + x) * 4 + 2] = Math.min(255, Math.floor(b * 255));
        data[(y * w + x) * 4 + 3] = Math.min(255, Math.floor(edge * 240 * (0.6 + intensity * 0.4)));
    }
    orbCtx.putImageData(id, 0, 0); orbTex.needsUpdate = true;
}

// ================================================================
//  MATERIALS
// ================================================================
const wallTex = mkWallTex(), floorTex = mkFloorTex(), ceilTex = mkCeilTex(), doorTex = mkDoorTex();
export const matWall = new THREE.MeshStandardMaterial({ map: wallTex, roughness: 0.9 });
export const matFloor = new THREE.MeshStandardMaterial({ map: floorTex, roughness: 0.8 });
export const matCeil = new THREE.MeshStandardMaterial({ map: ceilTex, roughness: 0.9 });
export const matDoor = new THREE.MeshStandardMaterial({ map: doorTex, roughness: 0.6 });
export const matDarkMetal = new THREE.MeshStandardMaterial({ map: mkGrimeTex(), roughness: 0.8 });
export const matRusty = new THREE.MeshStandardMaterial({ color: 0x2a1f10, roughness: 0.9 });
export const matSteel = new THREE.MeshStandardMaterial({ color: 0x4a4a4a, roughness: 0.5 });
export const matChrome = new THREE.MeshStandardMaterial({ color: 0x666666, roughness: 0.2 });
export const matHazard = new THREE.MeshStandardMaterial({ map: mkHazardTex(), roughness: 0.8 });
export const matWarnYellow = new THREE.MeshStandardMaterial({ color: 0xaa8800, roughness: 0.8 });

// These stay Basic because they emit their own light/color
export const matGlassRed = new THREE.MeshBasicMaterial({ color: 0xdd0000, transparent: true, opacity: 0.85 });
export const matIndicator = new THREE.MeshBasicMaterial({ color: 0xff0000 });