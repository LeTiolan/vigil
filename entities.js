import * as THREE from 'three';
import { scene, camera } from './scene-setup.js';
import { getPos, worldToGrid, emptyCells, exitGridX, exitGridZ } from './maze.js';
import { TOTAL_ORBS, ENEMY_NAMES, ALERT_DUR, HUNT_DUR } from './state.js';
import { orbTex, matGolem } from './textures.js';

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
//  ENEMIES — jointed golem rigs (torso/head/arms/legs), animated
//  procedurally each frame in main.js's update loop.
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

    // Rig proportions — bigger than the player (player height 2.1).
    const HIP_Y = 1.35, TORSO_LEN = 1.05, HEAD_R = 0.32;
    const THIGH_LEN = 0.66, SHIN_LEN = 0.62, UPARM_LEN = 0.5, LOARM_LEN = 0.48;

    const torsoGeo = new THREE.CapsuleGeometry(0.42, TORSO_LEN, 5, 10);
    const headGeo = new THREE.SphereGeometry(HEAD_R, 10, 8);
    const thighGeo = new THREE.CapsuleGeometry(0.17, THIGH_LEN, 4, 8);
    const shinGeo = new THREE.CapsuleGeometry(0.13, SHIN_LEN, 4, 8);
    const upArmGeo = new THREE.CapsuleGeometry(0.14, UPARM_LEN, 4, 8);
    const loArmGeo = new THREE.CapsuleGeometry(0.11, LOARM_LEN, 4, 8);
    const crackGeo = new THREE.BoxGeometry(0.07, 0.5, 0.045);

    function buildLimb(parent, xSide, geoUpper, lenUpper, geoLower, lenLower, yOff) {
        const pivotUpper = new THREE.Group();
        pivotUpper.position.set(xSide, yOff, 0);
        parent.add(pivotUpper);
        const upper = new THREE.Mesh(geoUpper, matGolem);
        upper.position.set(0, -lenUpper / 2, 0);
        upper.castShadow = true;
        pivotUpper.add(upper);
        const pivotLower = new THREE.Group();
        pivotLower.position.set(0, -lenUpper, 0);
        pivotUpper.add(pivotLower);
        const lower = new THREE.Mesh(geoLower, matGolem);
        lower.position.set(0, -lenLower / 2, 0);
        lower.castShadow = true;
        pivotLower.add(lower);
        return { upperPivot: pivotUpper, lowerPivot: pivotLower };
    }

    for (let n = 0; n < ENEMY_NAMES.length && n < enemyCandidates.length; n++) {
        const cell = enemyCandidates[n];
        const p = getPos(cell.x, cell.z);

        const enemy = new THREE.Group();
        enemy.position.set(p.x, 0, p.z); // ground-anchored root — legs reach the floor from here

        const pelvis = new THREE.Group();
        pelvis.position.set(0, HIP_Y, 0);
        enemy.add(pelvis);

        const torso = new THREE.Mesh(torsoGeo, matGolem);
        torso.position.set(0, TORSO_LEN / 2 + 0.08, 0);
        torso.castShadow = true;
        pelvis.add(torso);

        const head = new THREE.Mesh(headGeo, matGolem);
        head.position.set(0, TORSO_LEN + 0.36, 0);
        head.castShadow = true;
        pelvis.add(head);

        const legL = buildLimb(pelvis, 0.24, thighGeo, THIGH_LEN, shinGeo, SHIN_LEN, 0);
        const legR = buildLimb(pelvis, -0.24, thighGeo, THIGH_LEN, shinGeo, SHIN_LEN, 0);
        const armL = buildLimb(pelvis, 0.5, upArmGeo, UPARM_LEN, loArmGeo, LOARM_LEN, TORSO_LEN * 0.82);
        const armR = buildLimb(pelvis, -0.5, upArmGeo, UPARM_LEN, loArmGeo, LOARM_LEN, TORSO_LEN * 0.82);

        // Glowing veins — thin emissive strips scattered across the torso,
        // each enemy gets its OWN material instances so they can pulse
        // independently based on that enemy's state.
        const crackMats = [];
        for (let k = 0; k < 6; k++) {
            const mat = new THREE.MeshStandardMaterial({ color: 0x000000, emissive: 0xff5500, emissiveIntensity: 0.4 });
            const strip = new THREE.Mesh(crackGeo, mat);
            strip.position.set((Math.random() - 0.5) * 0.5, TORSO_LEN * (0.15 + Math.random() * 0.7), 0.4 * (Math.random() < 0.5 ? 1 : -1));
            strip.rotation.set(Math.random() * 0.6 - 0.3, Math.random() * Math.PI, Math.random() * 0.8 - 0.4);
            torso.add(strip);
            crackMats.push(mat);
        }

        const eyeL = new THREE.PointLight(0xff3300, 0, 3.5);
        eyeL.position.set(-0.13, TORSO_LEN + 0.38, 0.26);
        pelvis.add(eyeL);
        const eyeR = new THREE.PointLight(0xff3300, 0, 3.5);
        eyeR.position.set(0.13, TORSO_LEN + 0.38, 0.26);
        pelvis.add(eyeR);

        const bodyLight = new THREE.PointLight(0xcc5500, 0.5, 9);
        bodyLight.position.set(0, TORSO_LEN * 0.5, 0);
        pelvis.add(bodyLight);

        enemy.userData = {
            name: ENEMY_NAMES[n],
            state: 'patrol', // 'patrol' | 'search' | 'screaming' | 'hunt'
            lastGrid: { x: cell.x, z: cell.z },
            wanderTarget: null,
            pathQueue: [],
            pathUpdateT: 0,
            facing: Math.random() * Math.PI * 2,
            currentSpeed: 0,
            walkPhase: Math.random() * Math.PI * 2,
            huntTimer: 0,
            alertTimer: 0,
            searchTimer: 0,
            groupAlerted: false,
            groupTimer: 0,
            lastKnownGrid: null,
            lastKnownPos: null,
            playerMemory: [],
            predictedPos: null,
            screamPhase: null,
            screamT: 0,
            burstT: 0,
            stepPhaseLast: 0,
            joints: { hipL: legL.upperPivot, kneeL: legL.lowerPivot, hipR: legR.upperPivot, kneeR: legR.lowerPivot, shoulderL: armL.upperPivot, elbowL: armL.lowerPivot, shoulderR: armR.upperPivot, elbowR: armR.lowerPivot },
            crackMats, eyeL, eyeR, light: bodyLight,
        };

        scene.add(enemy);
        enemies.push(enemy);
    }
}

// ================================================================
//  ALERT SYSTEM
//
//  A fresh detection doesn't jump straight into a hunt — it triggers
//  the scream sub-state (handled per-frame in main.js), which freezes
//  movement, plays the brace/roar/slam animation, and only THEN hands
//  off into the hunt state with a temporary speed burst.
// ================================================================
export function triggerAlert(enemy, isGroupAlert) {
    const ud = enemy.userData;
    if (ud.state === 'patrol' || ud.state === 'search') {
        ud.state = 'screaming';
        ud.screamPhase = 'rising';
        ud.screamT = 0;
        ud.pathQueue = []; ud.pathUpdateT = 0;
    }
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
