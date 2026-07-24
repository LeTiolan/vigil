import * as THREE from 'three';
import { scene, camera } from './scene-setup.js';
import { getPos, worldToGrid, emptyCells, exitGridX, exitGridZ } from './maze.js';
import { TOTAL_ORBS, ENEMY_NAMES, PATROL_SPD, ALERT_DUR, HUNT_DUR } from './state.js';
import { orbTex } from './textures.js';

// ================================================================
//  COLLECTIBLE ORBS
// ================================================================
export const orbs = [];
{
    const spawnP = getPos(1, 1);
    const doorP = getPos(exitGridX, exitGridZ);
    const orbCandidates = emptyCells.filter(c => {
        const p = getPos(c.x, c.z);
        return Math.hypot(p.x - spawnP.x, p.z - spawnP.z) > 10 &&
               Math.hypot(p.x - doorP.x, p.z - doorP.z) > 10;
    });
    for (let i = orbCandidates.length - 1; i > 0; i--) {
        const j = Math.floor(Math.random() * (i + 1));
        [orbCandidates[i], orbCandidates[j]] = [orbCandidates[j], orbCandidates[i]];
    }

    const orbGeo = new THREE.SphereGeometry(0.55, 12, 10);
    const ringGeo = new THREE.SphereGeometry(0.85, 12, 10);

    for (let n = 0; n < TOTAL_ORBS && n < orbCandidates.length; n++) {
        const p = getPos(orbCandidates[n].x, orbCandidates[n].z);

        const orbMat = new THREE.MeshBasicMaterial({ map: orbTex, transparent: true, depthWrite: false });
        const orb = new THREE.Mesh(orbGeo, orbMat);
        orb.position.set(p.x, 2.0, p.z);

        const ringMat = new THREE.MeshBasicMaterial({ color: 0x00eaff, transparent: true, opacity: 0.3, side: THREE.DoubleSide, depthWrite: false });
        const ring = new THREE.Mesh(ringGeo, ringMat);
        orb.add(ring);

        const orbLight = new THREE.PointLight(0x00eaff, 1.2, 9);
        orb.add(orbLight);

        orb.userData = { ringMat };
        scene.add(orb);
        orbs.push(orb);
    }
}

// ================================================================
//  ENEMIES — Phantom AI bodies
// ================================================================
export const enemies = [];
{
    const spawnP = getPos(1, 1);
    const enemyCandidates = emptyCells.filter(c => {
        const p = getPos(c.x, c.z);
        return Math.hypot(p.x - spawnP.x, p.z - spawnP.z) > 30;
    });
    for (let i = enemyCandidates.length - 1; i > 0; i--) {
        const j = Math.floor(Math.random() * (i + 1));
        [enemyCandidates[i], enemyCandidates[j]] = [enemyCandidates[j], enemyCandidates[i]];
    }

    const midGeo = new THREE.SphereGeometry(1.0, 10, 8);
    const coreGeo = new THREE.SphereGeometry(0.5, 10, 8);

    for (let n = 0; n < ENEMY_NAMES.length && n < enemyCandidates.length; n++) {
        const cell = enemyCandidates[n];
        const p = getPos(cell.x, cell.z);

        const enemy = new THREE.Group();
        enemy.position.set(p.x, 2.2, p.z);

        const midMat = new THREE.MeshLambertMaterial({ color: 0x2a0050, transparent: true, opacity: 0.55 });
        const midMesh = new THREE.Mesh(midGeo, midMat);
        midMesh.scale.set(0.7, 1.5, 0.7);
        enemy.add(midMesh);

        const coreMat = new THREE.MeshLambertMaterial({ color: 0x110016, transparent: true, opacity: 0.85 });
        const coreMesh = new THREE.Mesh(coreGeo, coreMat);
        coreMesh.position.set(0, 0.8, 0);
        enemy.add(coreMesh);

        const eyeL = new THREE.PointLight(0xff2020, 0, 3);
        eyeL.position.set(-0.18, 0.85, 0.42);
        enemy.add(eyeL);
        const eyeR = new THREE.PointLight(0xff2020, 0, 3);
        eyeR.position.set(0.18, 0.85, 0.42);
        enemy.add(eyeR);

        const bodyLight = new THREE.PointLight(0x8800aa, 0.8, 10);
        bodyLight.position.set(0, 0.5, 0);
        enemy.add(bodyLight);

        enemy.userData = {
            name: ENEMY_NAMES[n],
            state: 'patrol',
            targetPos: new THREE.Vector3(p.x, 2.2, p.z),
            lastGrid: { x: cell.x, z: cell.z },
            currentSpeed: PATROL_SPD,
            wobbleSeed: Math.random() * Math.PI * 2,
            pathQueue: [],
            pathUpdateT: 0,
            huntTimer: 0,
            alertTimer: 0,
            searchTimer: 0,
            groupAlerted: false,
            groupTimer: 0,
            lastKnownGrid: null,
            lastKnownPos: null,
            playerMemory: [],
            predictedPos: null,
            coreMesh, midMesh, eyeL, eyeR, light: bodyLight,
        };

        scene.add(enemy);
        enemies.push(enemy);
    }
}

// ================================================================
//  ALERT SYSTEM
// ================================================================
export function triggerAlert(enemy, isGroupAlert) {
    const ud = enemy.userData;
    if (ud.state !== 'hunt') { ud.pathQueue = []; ud.pathUpdateT = 0; }
    ud.state = 'hunt';
    ud.huntTimer = HUNT_DUR;
    ud.alertTimer = ALERT_DUR;
    ud.lastKnownGrid = worldToGrid(camera.position.x, camera.position.z);
    ud.lastKnownPos = { x: camera.position.x, z: camera.position.z };
    if (isGroupAlert) { ud.groupAlerted = true; ud.groupTimer = 3.0; }
}

export function alertAllInRadius(wx, wz, radius) {
    enemies.forEach(enemy => {
        const d = Math.hypot(enemy.position.x - wx, enemy.position.z - wz);
        if (d < radius) triggerAlert(enemy, true);
    });
}