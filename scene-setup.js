import * as THREE from 'three';

// ================================================================
//  SCENE — PSX style: low pixel ratio, nearest filter, no AA
// ================================================================
export const scene = new THREE.Scene();
scene.background = new THREE.Color(0x040508);
scene.fog = new THREE.FogExp2(0x040508, 0.022);

export const camera = new THREE.PerspectiveCamera(75, innerWidth / innerHeight, 0.1, 100);
camera.rotation.order = 'YXZ';

export const renderer = new THREE.WebGLRenderer({ antialias: false });
renderer.setPixelRatio(Math.min(devicePixelRatio, 1) * 0.3);
renderer.setSize(innerWidth, innerHeight);

// Enable Shadows
renderer.shadowMap.enabled = true;
renderer.shadowMap.type = THREE.PCFShadowMap;
document.body.appendChild(renderer.domElement);

// Bodycam flashlight — Bigger, detailed, and toggleable
export const flash1 = new THREE.SpotLight(0xfffdd8, 150, 80, Math.PI / 4, 0.1, 1.8);
flash1.castShadow = true; flash1.shadow.mapSize.setScalar(256); flash1.shadow.bias = -0.001;
export const flash2 = new THREE.SpotLight(0xffe8c0, 30, 45, Math.PI / 2.5, 0.8, 2.2);
flash2.castShadow = false;
flash1.position.set(0, 0, 0);
flash2.position.set(0, 0, 0);
camera.add(flash1); camera.add(flash1.target); flash1.target.position.set(0, 0, -1);
camera.add(flash2); camera.add(flash2.target); flash2.target.position.set(0, 0, -1);

// Add the camera (and its attached lights) to the scene
scene.add(camera);

export const hemi = new THREE.HemisphereLight(0x14181c, 0x08090a, 0.35);
scene.add(hemi);

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
    color: 0x99aaaf, // Dirty, pale grey/blue
    size: 0.25,
    transparent: true,
    opacity: 0.4,
    depthWrite: false // CRITICAL: Prevents dust from creating weird black outlines
});
export const dustParticles = new THREE.Points(dustGeo, dustMat);
scene.add(dustParticles);