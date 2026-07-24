import * as THREE from 'three';
import { scene } from './scene-setup.js';

// ================================================================
//  PARTICLES
// ================================================================
export const particles = [];
const sparkGeo = new THREE.BoxGeometry(0.08, 0.08, 0.08);
const sparkMat = new THREE.MeshBasicMaterial({ color: 0xff8800 });
const steamGeo = new THREE.PlaneGeometry(1.2, 1.2);
const steamMatBase = new THREE.MeshBasicMaterial({ color: 0xbbbbbb, transparent: true, opacity: 0.35, depthWrite: false });

export function emitSpark(x, y, z) {
    const s = new THREE.Mesh(sparkGeo, sparkMat); s.position.set(x, y, z);
    s.userData = { vel: new THREE.Vector3((Math.random() - 0.5) * 6, Math.random() * 6 + 2, (Math.random() - 0.5) * 6), life: 0.8, type: 'spark' };
    scene.add(s); particles.push(s);
}

export function emitSteam(x, y, z) {
    const mat = steamMatBase.clone(), s = new THREE.Mesh(steamGeo, mat); s.position.set(x, y, z);
    s.userData = { vel: new THREE.Vector3((Math.random() - 0.5) * 1.5, Math.random() * 2.5 + 0.5, (Math.random() - 0.5) * 1.5), life: 1.2, type: 'steam', mat };
    scene.add(s); particles.push(s);
}