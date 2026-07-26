import * as THREE from 'three';
import { scene, camera, renderer, flash1, flash2, dustParticles } from './scene-setup.js';
import { state, keys, player, exploredCells, MAX_STAMINA, TOTAL_ORBS, LIGHT_RANGE, CONE_COS, HUNT_SPD, SEARCH_SPD, PATROL_SPD, SEARCH_DUR, BURST_SPD, TURN_RATE, SCREAM_RISE_T, SCREAM_HOLD_T, SCREAM_SLAM_T, BURST_DUR } from './state.js';
import { MAZE_SIZE, TILE_SIZE, maze, getPos, worldToGrid, bfsPath, hasLOS } from './maze.js';
import { isWall } from './collision.js';
import { updateOrbTex } from './textures.js';
import { particles, emitSpark, emitSteam } from './particles.js';
import './level-geometry.js'; // builds floor/ceiling/walls/corridor lights as a side effect
import {
    doorGroup, doorState, setDoorState, TERM_WX, TERM_WZ, sirens, valves, vaultWG,
    deadboltsL, deadboltsR, matInd, mgL, mgR, hgL, hgR, GR, HGR, gearYPos, gearZPos,
    doorHL, doorHR, termBtn, termScreenMat, termLight, ledMat, termBtnMat,
    doorSnd, stopAllDoorAudio
} from './door.js';
import { orbs, enemies, alertAllInRadius, triggerAlert } from './entities.js';
import { playFootstep, playOrbChime, playSting, playFlashlightClick, playUISound, playRoar, playStomp } from './audio.js';
import { elOrbCount, elTimeVal, elStBar, elStCont, elCross, elPrompt, radarCanvas, rCtx, RC, R_MAX, R_SCL, elPromptText } from './dom.js';
import './menu.js'; // wires up menu/input listeners as a side effect

// Place the player at the maze entrance. This was missing entirely after
// the file split — the camera was defaulting to THREE's origin (0,0,0),
// which sits inside solid wall geometry near the maze's center instead
// of at the actual spawn corridor.
{
    const spawn = getPos(1, 1);
    camera.position.set(spawn.x, player.height, spawn.z);
}

// ================================================================
//  UPDATE LOOP
// ================================================================
// Scratch vectors, reused every frame/enemy instead of `new`-ing —
// avoids garbage-collector churn in the hot per-enemy AI loop.
const _inp = new THREE.Vector2();
const _fwd = new THREE.Vector3();
const _toE = new THREE.Vector3();

function update() {
    if (!state.gameActive) return;
    const now = performance.now();
    const delta = Math.min((now - state.prevTime) / 1000, 0.05); state.prevTime = now;
    const totalElapsed = (state.accumulatedTime + (Date.now() - state.startTime) / 1000).toFixed(1);
    if (!state.gameWon) elTimeVal.innerText = totalElapsed;

    // Update animated orb fluid texture once per frame
    updateOrbTex(now);

    // Track explored cells
    const pg = worldToGrid(camera.position.x, camera.position.z); exploredCells.add(`${pg.x},${pg.z}`);

    // ---- MOVEMENT ----
    if (!state.gameWon) {
        const inp = _inp.set(0, 0);
        if (keys['KeyW']) inp.y -= 1; if (keys['KeyS']) inp.y += 1; if (keys['KeyA']) inp.x -= 1; if (keys['KeyD']) inp.x += 1;
        if (inp.length() > 0) inp.normalize();
        const moving = inp.length() > 0, isSprinting = keys['ShiftLeft'] && moving && !player.isExhausted;
        state.currentlySprinting = isSprinting;

        // --- Bulletproof F key toggle (smooth intensity version) ---
        if (keys['KeyF'] && !window.fKeyWasPressed) {
            state.flashlightOn = !state.flashlightOn;
            flash1.intensity = state.flashlightOn ? 150 : 0;
            flash2.intensity = state.flashlightOn ? 30 : 0;
            if (typeof playFlashlightClick === 'function') playFlashlightClick();
            window.fKeyWasPressed = true;
            const fi = document.getElementById('flashlight-indicator');
            if (fi) { state.flashlightOn ? fi.classList.remove('off') : fi.classList.add('off'); }
        } else if (!keys['KeyF']) {
            window.fKeyWasPressed = false;
        }

        if (isSprinting) {
            player.stamina -= 0.4;
            if (player.stamina <= 0) player.isExhausted = true;
        } else {
            player.stamina = Math.min(MAX_STAMINA, player.stamina + 0.9);
            if (player.stamina >= MAX_STAMINA * 0.25) player.isExhausted = false;
        }
        const stPct = (player.stamina / MAX_STAMINA) * 100;
        elStBar.style.height = stPct + '%';
        elStBar.style.background = player.isExhausted ? '#8b0000' : 'linear-gradient(to top, #5a4200, #d4af37, #ffe060)';
        elStCont.classList.toggle('exhausted', player.isExhausted);

        // --- Flashlight flicker respects the toggle state ---
        if (state.flashlightOn) {
            if (stPct < 28) { const fl = 0.65 + 0.35 * Math.abs(Math.sin(now * 0.03 + Math.sin(now * 0.009) * 4)); flash1.intensity = 90 * fl; flash2.intensity = 18 * fl; }
            else { flash1.intensity = 90; flash2.intensity = 18; }
        }

        // FOV sprint tunnel
        const tFOV = isSprinting ? 86 : 75; camera.fov += (tFOV - camera.fov) * 0.09; camera.updateProjectionMatrix();

        const spd = isSprinting ? player.runSpeed : (moving ? player.walkSpeed : 0);
        const tv = inp.clone().multiplyScalar(spd); player.velocity.lerp(tv, 0.14);
        const mx = player.velocity.x * Math.cos(state.yaw) + player.velocity.y * Math.sin(state.yaw);
        const mz = -player.velocity.x * Math.sin(state.yaw) + player.velocity.y * Math.cos(state.yaw);
        let tx = camera.position.x, tz = camera.position.z;
        if (!isWall(tx + mx, tz, player.radius, doorGroup)) tx += mx;
        if (!isWall(tx, tz + mz, player.radius, doorGroup)) tz += mz;
        camera.position.x = tx; camera.position.z = tz;

        const spd2 = player.velocity.length();
        if (spd2 > 0.02) {
            const hz = isSprinting ? 3.5 : 1.5, amp = isSprinting ? 0.10 : 0.07;
            player.headBobTimer += delta * hz * Math.PI * 2;
            camera.position.y = player.height + Math.sin(player.headBobTimer) * amp;
            const cycle = Math.floor(player.headBobTimer / Math.PI);
            if (cycle > state.lastFootCycle) { state.lastFootCycle = cycle; playFootstep(isSprinting); }
            if (isSprinting) { state.sprintAlertCD -= delta; if (state.sprintAlertCD <= 0) { state.sprintAlertCD = 0.65; alertAllInRadius(camera.position.x, camera.position.z, 22); } }
        } else { camera.position.y += (player.height - camera.position.y) * 0.1; player.headBobTimer += delta; }
    }

    // ---- PARTICLES ----
    for (let i = particles.length - 1; i >= 0; i--) {
        const p = particles[i]; p.position.addScaledVector(p.userData.vel, delta); p.userData.life -= delta;
        if (p.userData.type === 'steam') { p.userData.mat.opacity = (p.userData.life / 1.2) * 0.35; p.scale.setScalar(2.2 - p.userData.life); }
        else if (p.userData.type === 'spark') { p.userData.vel.y -= delta * 18; if (p.position.y < 0.1) { p.position.y = 0.1; p.userData.vel.y *= -0.4; } }
        if (p.userData.life <= 0) { scene.remove(p); if (p.userData.type === 'steam') p.userData.mat.dispose(); particles.splice(i, 1); }
    }

    // ---- PERFORMANCE OPTIMIZED LIGHT UPDATE (Lag-Free) ----
    // Hard shadow budget: no matter how many corridor lights are nearby,
    // only the closest MAX_SHADOW_LIGHTS are ever allowed to cast a
    // shadow this frame. Everything else still lights the scene, just
    // without a shadow pass.
    const MAX_SHADOW_LIGHTS = 2;
    const shadowCandidates = [];

    state.corridorLights.forEach(cl => {
        let targetI = 1.0;

        if (cl.broken) {
            const t = now * 0.001 * cl.rate + cl.seed;
            const noise = Math.sin(t * 7.8) * Math.sin(t * 3.3) * Math.sin(t * 15.0);
            targetI = noise > 0.1 ? 1.0 : 0.05;
            if (Math.random() > 0.98) targetI = 0;
        } else {
            targetI = 0.9 + Math.sin(now * 0.005 + cl.seed) * 0.1;
        }

        if (cl.currentI === undefined) cl.currentI = 0;
        cl.currentI += (targetI - cl.currentI) * 0.25;

        if (cl.light) {
            cl.light.intensity = cl.base * cl.currentI;

            const dx = camera.position.x - cl.light.position.x;
            const dz = camera.position.z - cl.light.position.z;
            const distSq = dx * dx + dz * dz;

            const isClose = distSq < 3600;
            const isBrightEnough = cl.light.intensity > 0.1;

            cl.light.shadow.autoUpdate = false; // default off; re-enabled below for the closest few
            if (isClose && isBrightEnough) shadowCandidates.push({ cl, distSq });

            if (cl.light.shadow.camera.far !== 45) {
                cl.light.shadow.camera.far = 45;
                cl.light.shadow.camera.updateProjectionMatrix();
            }
        }

        if (cl.strip) cl.strip.emissiveIntensity = 2.5 * cl.currentI;
    });

    shadowCandidates.sort((a, b) => a.distSq - b.distSq);
    for (let i = 0; i < Math.min(MAX_SHADOW_LIGHTS, shadowCandidates.length); i++) {
        shadowCandidates[i].cl.light.shadow.autoUpdate = true;
    }

    // ---- TERMINAL BUTTON ANIMATION ----
    if (state.terminalBtnT > 0) { state.terminalBtnT -= delta; if (state.terminalBtnT <= 0) termBtn.position.z = 0.56; }
    if (doorState === 'ready_terminal' && !state.terminalActivated) termLight.intensity = 2.8 + 1.6 * Math.sin(now * 0.006);

    // ---- RADAR (200x200) ----
    rCtx.clearRect(0, 0, radarCanvas.width, radarCanvas.height);
    rCtx.strokeStyle = 'rgba(60,100,55,0.4)'; rCtx.lineWidth = 1.5; rCtx.beginPath(); rCtx.arc(RC, RC, RC - 4, 0, Math.PI * 2); rCtx.stroke();
    rCtx.strokeStyle = 'rgba(40,70,35,0.2)'; rCtx.lineWidth = 1;
    [RC * 0.35, RC * 0.65].forEach(r => { rCtx.beginPath(); rCtx.arc(RC, RC, r, 0, Math.PI * 2); rCtx.stroke(); });
    rCtx.strokeStyle = 'rgba(50,85,45,0.2)'; rCtx.beginPath(); rCtx.moveTo(RC, 8); rCtx.lineTo(RC, radarCanvas.height - 8); rCtx.moveTo(8, RC); rCtx.lineTo(radarCanvas.width - 8, RC); rCtx.stroke();

    rCtx.fillStyle = 'rgba(55,90,50,0.2)';
    exploredCells.forEach(k => {
        const [gx, gz] = k.split(',').map(Number); const wp = getPos(gx, gz);
        const dx = wp.x - camera.position.x, dz = wp.z - camera.position.z;
        if (Math.hypot(dx, dz) > R_MAX) return;
        const lr = dx * Math.cos(state.yaw) - dz * Math.sin(state.yaw), lf = -dx * Math.sin(state.yaw) - dz * Math.cos(state.yaw);
        rCtx.fillRect(RC + lr * R_SCL - 2, RC - lf * R_SCL - 2, 4, 4);
    });

    rCtx.fillStyle = 'rgba(220,200,150,0.85)';
    rCtx.beginPath(); rCtx.moveTo(RC, RC - 9); rCtx.lineTo(RC - 5, RC + 6); rCtx.lineTo(RC, RC + 3); rCtx.lineTo(RC + 5, RC + 6); rCtx.closePath(); rCtx.fill();

    function drawBlip(wx, wz, col, sz) {
        const dx = wx - camera.position.x, dz = wz - camera.position.z;
        let lr = dx * Math.cos(state.yaw) - dz * Math.sin(state.yaw), lf = -dx * Math.sin(state.yaw) - dz * Math.cos(state.yaw);
        const d = Math.hypot(lr, lf); if (d > R_MAX) { lr = (lr / d) * R_MAX; lf = (lf / d) * R_MAX; }
        const rx = RC + lr * R_SCL, ry = RC - lf * R_SCL;
        rCtx.fillStyle = col; rCtx.beginPath(); rCtx.arc(rx, ry, sz, 0, Math.PI * 2); rCtx.fill();
        return { rx, ry };
    }
    function drawDoor(wx, wz) {
        const dx = wx - camera.position.x, dz = wz - camera.position.z;
        let lr = dx * Math.cos(state.yaw) - dz * Math.sin(state.yaw), lf = -dx * Math.sin(state.yaw) - dz * Math.cos(state.yaw);
        const d = Math.hypot(lr, lf); if (d > R_MAX) { lr = (lr / d) * R_MAX; lf = (lf / d) * R_MAX; }
        const rx = RC + lr * R_SCL, ry = RC - lf * R_SCL;
        rCtx.strokeStyle = 'rgba(40,180,60,0.9)'; rCtx.lineWidth = 2;
        rCtx.strokeRect(rx - 6, ry - 8, 12, 14);
        rCtx.fillStyle = 'rgba(20,120,30,0.6)'; rCtx.fillRect(rx - 4, ry - 6, 8, 12);
    }
    drawDoor(doorGroup.position.x, doorGroup.position.z);
    if (doorState === 'ready_terminal') drawBlip(TERM_WX, TERM_WZ, 'rgba(0,220,255,0.9)', 4);
    orbs.forEach(o => { if (o.position.y > 0) { const { rx, ry } = drawBlip(o.position.x, o.position.z, 'rgba(0,220,255,0.5)', 3); const grd = rCtx.createRadialGradient(rx, ry, 0, rx, ry, 6); grd.addColorStop(0, 'rgba(0,238,255,0.4)'); grd.addColorStop(1, 'rgba(0,0,0,0)'); rCtx.fillStyle = grd; rCtx.beginPath(); rCtx.arc(rx, ry, 6, 0, Math.PI * 2); rCtx.fill(); } });

    // ---- CROSSHAIR nearby orb check ----
    let nearOrb = false; orbs.forEach(o => { if (o.position.y > 0 && camera.position.distanceTo(o.position) < 5.5) nearOrb = true; });
    elCross.classList.toggle('nearby', nearOrb);

    // ---- CREATURE AI: state machine, steering, and procedural animation ----
    let closestDist = 100; let anyScreaming = false;
    const camPos = camera.position;

    enemies.forEach((enemy, idx) => {
        const ud = enemy.userData;
        // Horizontal-only distance: the rig is ground-anchored now (real legs
        // reaching the floor), so 3D distance would always be inflated by the
        // camera's eye-height offset. Horizontal distance is what actually
        // matters for detection/threat here.
        const distE = Math.hypot(camPos.x - enemy.position.x, camPos.z - enemy.position.z);
        if (distE < closestDist) closestDist = distE;

        if (ud.groupAlerted) { ud.groupTimer -= delta; if (ud.groupTimer <= 0) ud.groupAlerted = false; }

        // --- Light cone detection (only when calm) ---
        if (ud.state === 'patrol' || ud.state === 'search') {
            if (distE < LIGHT_RANGE) {
                const fwd = _fwd.set(0, 0, -1).applyQuaternion(camera.quaternion);
                const toE = _toE.subVectors(enemy.position, camPos).normalize();
                if (fwd.dot(toE) > CONE_COS && hasLOS(camPos.x, camPos.z, enemy.position.x, enemy.position.z))
                    triggerAlert(enemy, false);
            }
        }

        let targetSpeed = 0;
        let steerTarget = null; // {x,z} world point to steer toward this frame

        // --- SCREAMING: frozen in place, arms brace up then slam down ---
        if (ud.state === 'screaming') {
            anyScreaming = true;
            ud.screamT += delta;
            const j = ud.joints;
            if (ud.screamPhase === 'rising') {
                const p = Math.min(1, ud.screamT / SCREAM_RISE_T);
                const raise = p * 2.5;
                j.shoulderL.rotation.x = -raise; j.shoulderR.rotation.x = -raise;
                j.shoulderL.rotation.z = raise * 0.35; j.shoulderR.rotation.z = -raise * 0.35;
                ud.eyeL.intensity = p * 3; ud.eyeR.intensity = p * 3;
                if (p >= 1) { ud.screamPhase = 'holding'; ud.screamT = 0; }
            } else if (ud.screamPhase === 'holding') {
                j.shoulderL.rotation.x = -2.5 + Math.sin(now * 0.03) * 0.06;
                j.shoulderR.rotation.x = -2.5 + Math.sin(now * 0.03 + 1) * 0.06;
                if (ud.screamT >= SCREAM_HOLD_T) {
                    playRoar();
                    ud.screamPhase = 'slamming'; ud.screamT = 0;
                }
            } else if (ud.screamPhase === 'slamming') {
                const p = Math.min(1, ud.screamT / SCREAM_SLAM_T);
                const raise = (1 - p) * 2.5;
                j.shoulderL.rotation.x = -raise + p * 0.9; j.shoulderR.rotation.x = -raise + p * 0.9;
                j.shoulderL.rotation.z = raise * 0.35 * (1 - p); j.shoulderR.rotation.z = -raise * 0.35 * (1 - p);
                if (p >= 1) {
                    ud.state = 'hunt'; ud.screamPhase = null; ud.burstT = BURST_DUR;
                }
            }
            ud.currentSpeed += (0 - ud.currentSpeed) * 0.12;
            ud.light.intensity = 2.2;

        // --- HUNT: burst speed right after the scream, settling to a normal run ---
        } else if (ud.state === 'hunt') {
            ud.alertTimer -= delta; ud.huntTimer -= delta;
            ud.eyeL.intensity = 2.5 + Math.sin(now * 0.012) * 0.8; ud.eyeR.intensity = ud.eyeL.intensity;
            ud.light.intensity = 2.5;

            if (hasLOS(camPos.x, camPos.z, enemy.position.x, enemy.position.z)) {
                ud.lastKnownGrid = worldToGrid(camPos.x, camPos.z);
                ud.lastKnownPos = { x: camPos.x, z: camPos.z };
                ud.playerMemory.push({ wx: camPos.x, wz: camPos.z, t: now });
                if (ud.playerMemory.length > 8) ud.playerMemory.shift();
            }

            if (ud.playerMemory.length >= 3) {
                const m = ud.playerMemory; const recent = m[m.length - 1], older = m[m.length - 3];
                const dt = (recent.t - older.t) / 1000;
                if (dt > 0.1) {
                    const vx = (recent.wx - older.wx) / dt, vz = (recent.wz - older.wz) / dt;
                    ud.predictedPos = { x: recent.wx + vx * 2.5, z: recent.wz + vz * 2.5 };
                }
            }

            ud.pathUpdateT -= delta;
            if (ud.pathUpdateT <= 0) {
                ud.pathUpdateT = 0.7; // recalculates faster than before — smarter, more responsive
                const target = ud.predictedPos || ud.lastKnownPos || { x: camPos.x, z: camPos.z };
                const eg = worldToGrid(enemy.position.x, enemy.position.z);
                const tg = worldToGrid(target.x, target.z);
                const path = bfsPath(eg.x, eg.z, tg.x, tg.z);
                if (path.length > 0) ud.pathQueue = path;
            }

            if (ud.huntTimer <= 0 || ud.alertTimer <= 0) { ud.state = 'search'; ud.searchTimer = SEARCH_DUR; ud.pathQueue = []; ud.pathUpdateT = 0; }

            if (ud.burstT > 0) { ud.burstT -= delta; targetSpeed = BURST_SPD; }
            else targetSpeed = HUNT_SPD;
            ud.currentSpeed += (targetSpeed - ud.currentSpeed) * 0.05;

            const pulse = 0.55 + 0.45 * Math.abs(Math.sin(now * 0.008 + idx));
            const { rx, ry } = drawBlip(enemy.position.x, enemy.position.z, `rgba(255,0,0,${0.7 + pulse * 0.3})`, 5 + pulse * 2);
            const g = rCtx.createRadialGradient(rx, ry, 0, rx, ry, 12); g.addColorStop(0, 'rgba(255,0,0,0.35)'); g.addColorStop(1, 'rgba(255,0,0,0)'); rCtx.fillStyle = g; rCtx.beginPath(); rCtx.arc(rx, ry, 12, 0, Math.PI * 2); rCtx.fill();

        // --- SEARCH ---
        } else if (ud.state === 'search') {
            ud.searchTimer -= delta;
            ud.eyeL.intensity = 1.2 + Math.sin(now * 0.005 + idx) * 0.4; ud.eyeR.intensity = ud.eyeL.intensity;
            ud.light.intensity = 1.8;

            if (ud.lastKnownGrid) {
                const lk = getPos(ud.lastKnownGrid.x, ud.lastKnownGrid.z);
                if (Math.hypot(enemy.position.x - lk.x, enemy.position.z - lk.z) < TILE_SIZE * 0.55 || ud.searchTimer <= 0) {
                    if (ud.playerMemory.length > 0) {
                        const mem = ud.playerMemory.pop();
                        ud.lastKnownGrid = worldToGrid(mem.wx, mem.wz); ud.pathQueue = []; ud.pathUpdateT = 0; ud.searchTimer = SEARCH_DUR * 0.6;
                    } else {
                        ud.state = 'patrol'; ud.pathQueue = []; ud.eyeL.intensity = 0; ud.eyeR.intensity = 0; ud.light.intensity = 0.5;
                        ud.predictedPos = null;
                    }
                } else {
                    ud.pathUpdateT -= delta;
                    if (ud.pathUpdateT <= 0) {
                        ud.pathUpdateT = 1.2; const eg = worldToGrid(enemy.position.x, enemy.position.z);
                        ud.pathQueue = bfsPath(eg.x, eg.z, ud.lastKnownGrid.x, ud.lastKnownGrid.z);
                    }
                }
            } else { ud.state = 'patrol'; ud.eyeL.intensity = 0; ud.eyeR.intensity = 0; }
            targetSpeed = SEARCH_SPD;
            ud.currentSpeed += (targetSpeed - ud.currentSpeed) * 0.035;

            const { rx: rx2, ry: ry2 } = drawBlip(enemy.position.x, enemy.position.z, 'rgba(220,110,0,0.75)', 3.5);
            const g2 = rCtx.createRadialGradient(rx2, ry2, 0, rx2, ry2, 9); g2.addColorStop(0, 'rgba(220,100,0,0.25)'); g2.addColorStop(1, 'rgba(0,0,0,0)'); rCtx.fillStyle = g2; rCtx.beginPath(); rCtx.arc(rx2, ry2, 9, 0, Math.PI * 2); rCtx.fill();

        // --- PATROL: slow, deliberate wander ---
        } else {
            ud.eyeL.intensity = 0; ud.eyeR.intensity = 0; ud.light.intensity = 0.5;
            if (!ud.wanderTarget) ud.wanderTarget = { x: enemy.position.x, z: enemy.position.z };
            if (Math.hypot(enemy.position.x - ud.wanderTarget.x, enemy.position.z - ud.wanderTarget.z) < 0.6) {
                const cx = Math.round(ud.wanderTarget.x / TILE_SIZE) + Math.floor(MAZE_SIZE / 2);
                const cz = Math.round(ud.wanderTarget.z / TILE_SIZE) + Math.floor(MAZE_SIZE / 2);
                const nb = []; [[0, -1], [0, 1], [-1, 0], [1, 0]].forEach(([dx2, dz2]) => { const nx = cx + dx2, nz = cz + dz2; if (nx >= 0 && nx < MAZE_SIZE && nz >= 0 && nz < MAZE_SIZE && maze[nx][nz] === 0 && !(nx === ud.lastGrid.x && nz === ud.lastGrid.z)) nb.push({ x: nx, z: nz }); });
                if (!nb.length && maze[ud.lastGrid.x] && maze[ud.lastGrid.x][ud.lastGrid.z] === 0) nb.push(ud.lastGrid);
                ud.lastGrid = { x: cx, z: cz }; const nc = nb.length ? nb[Math.floor(Math.random() * nb.length)] : ud.lastGrid;
                const np = getPos(nc.x, nc.z); ud.wanderTarget = { x: np.x, z: np.z };
            }
            steerTarget = ud.wanderTarget;
            targetSpeed = PATROL_SPD;
            ud.currentSpeed += (targetSpeed - ud.currentSpeed) * 0.015;
        }

        // --- Steering: freeform movement toward a blend of the next two
        //     path waypoints (not just the immediate one), so the creature
        //     cuts corners and moves diagonally instead of snapping through
        //     grid cells at right angles. ---
        if (ud.state !== 'screaming' && ud.pathQueue.length > 0) {
            const n0 = getPos(ud.pathQueue[0].x, ud.pathQueue[0].z);
            const d0 = Math.hypot(enemy.position.x - n0.x, enemy.position.z - n0.z);
            if (ud.pathQueue.length > 1) {
                const n1 = getPos(ud.pathQueue[1].x, ud.pathQueue[1].z);
                const blend = Math.max(0, Math.min(0.65, 1 - d0 / (TILE_SIZE * 0.75)));
                steerTarget = { x: n0.x * (1 - blend) + n1.x * blend, z: n0.z * (1 - blend) + n1.z * blend };
            } else steerTarget = n0;
            if (d0 < TILE_SIZE * 0.35) ud.pathQueue.shift();
        }

        if (ud.state !== 'screaming' && steerTarget) {
            const dx = steerTarget.x - enemy.position.x, dz = steerTarget.z - enemy.position.z;
            const dlen = Math.hypot(dx, dz);
            if (dlen > 0.01) {
                const nx = dx / dlen, nz = dz / dlen;
                enemy.position.x += nx * ud.currentSpeed;
                enemy.position.z += nz * ud.currentSpeed;

                // Turn-rate-limited facing: bigger than the player, but turns
                // tighter/faster — never snaps instantly to the new heading.
                const targetAngle = Math.atan2(nx, nz);
                let diff = targetAngle - ud.facing;
                while (diff > Math.PI) diff -= Math.PI * 2;
                while (diff < -Math.PI) diff += Math.PI * 2;
                const maxStep = TURN_RATE * delta;
                ud.facing += Math.max(-maxStep, Math.min(maxStep, diff));
                enemy.rotation.y = ud.facing;
            }
        }

        // --- Procedural walk-cycle: amplitude/frequency scale with actual
        //     speed, so slow patrol shuffling smoothly blends into a full
        //     run as currentSpeed ramps up — one continuous animation, not
        //     separate walk/run clips. ---
        if (ud.state !== 'screaming') {
            const speedRatio = Math.min(1.4, ud.currentSpeed / HUNT_SPD);
            ud.walkPhase += delta * (2.2 + speedRatio * 5.5);
            const amp = speedRatio * 0.75;
            const swing = Math.sin(ud.walkPhase), swingOpp = Math.sin(ud.walkPhase + Math.PI);
            const j = ud.joints;
            j.hipL.rotation.x = swing * amp; j.hipR.rotation.x = swingOpp * amp;
            j.kneeL.rotation.x = Math.max(0, -swing) * amp * 1.5; j.kneeR.rotation.x = Math.max(0, -swingOpp) * amp * 1.5;
            j.shoulderL.rotation.x = swingOpp * amp * 0.7; j.shoulderR.rotation.x = swing * amp * 0.7;
            j.shoulderL.rotation.z = 0; j.shoulderR.rotation.z = 0;

            // Heavy footfall thud in sync with each stride, when close enough to matter
            const stepPhase = Math.floor(ud.walkPhase / Math.PI);
            if (stepPhase !== ud.stepPhaseLast && ud.currentSpeed > 0.04 && distE < 32) {
                ud.stepPhaseLast = stepPhase;
                playStomp(Math.max(0, 1 - distE / 32));
            }
        }

        // Slight overall bob so the walk doesn't look perfectly rigid
        enemy.position.y = Math.abs(Math.sin(ud.walkPhase)) * 0.06;

        // --- Glowing veins: always faintly lit, ramping up as the player
        //     gets close enough to actually see them, brighter with threat. ---
        const baseByState = ud.state === 'hunt' ? 3.2 : ud.state === 'screaming' ? 2.6 : ud.state === 'search' ? 1.6 : 0.5;
        const visFactor = Math.max(0, Math.min(1, 1 - distE / 28));
        const crackPulse = 0.8 + 0.2 * Math.sin(now * 0.006 + idx);
        const crackI = baseByState * (0.15 + 0.85 * visFactor) * crackPulse;
        ud.crackMats.forEach(m => m.emissiveIntensity = crackI);

        // Death
        if (!state.gameWon && distE < 2.8 && state.gameActive) {
            state.gameActive = false; document.exitPointerLock();
            const t = (state.accumulatedTime + (Date.now() - state.startTime) / 1000).toFixed(1);
            document.getElementById('time-stat').innerText = t + 's'; document.getElementById('orb-stat').innerText = `${state.orbsCollected} / ${TOTAL_ORBS}`;
            document.getElementById('death-screen-ui').style.display = 'block';
        }
    });

    // Proximity screen shake/sting — stronger and wider-radius than before,
    // with an extra jolt while any creature is mid-scream nearby.
    if (!state.gameWon && closestDist < 16) {
        const t = (16 - closestDist) * (anyScreaming ? 0.032 : 0.016);
        camera.position.x += (Math.random() - 0.5) * t;
        camera.position.y += (Math.random() - 0.5) * t * 0.4;
        if (!state.hasPlayedSting) { playSting(); state.hasPlayedSting = true; }
    } else state.hasPlayedSting = false;

    // ---- ORB COLLECTION ----
    orbs.forEach(orb => {
        if (!state.gameWon && orb.position.y > 0 && camPos.distanceTo(orb.position) < 2.8) {
            orb.position.y = -1000; state.orbsCollected++; elOrbCount.innerText = state.orbsCollected;
            playOrbChime(); alertAllInRadius(orb.position.x, orb.position.z, 20);
            if (state.orbsCollected === TOTAL_ORBS && doorState === 'closed') {
                setDoorState('ready_terminal');
                termScreenMat.color.setHex(0x001400); termLight.color.setHex(0x00ff44); termLight.intensity = 3.5;
                ledMat.color.setHex(0x00cc22); termBtnMat.color.setHex(0x00bb00);
                playUISound(280, 0.7, 0.7, 'sine');
            }
        }
    });
    orbs.forEach(orb => { if (orb.position.y > 0 && orb.userData.ringMat) orb.userData.ringMat.opacity = 0.25 + 0.18 * Math.sin(now * 0.005 + orb.position.x); });

    // Siren spin
    sirens.forEach((s, i) => s.group.rotation.y += delta * (i % 2 === 0 ? 2.2 : -2.2));

    // Terminal proximity prompt
    if (state.gameActive && !state.gameWon && !state.terminalActivated) {
        const dt = Math.hypot(camPos.x - TERM_WX, camPos.z - TERM_WZ);
        const showTerm = doorState === 'ready_terminal' && dt < 9;
        elPrompt.style.display = showTerm ? 'block' : 'none';
        if (showTerm) elPromptText.innerText = 'ACTIVATE TERMINAL';
    }

    // ---- DOOR ANIMATION ─────────────────────────────────────────
    if (!state.gameWon) camera.rotation.z = 0;
    if (doorState !== 'closed' && doorState !== 'ready_terminal') {
        sirens.forEach((s, i) => { s.group.rotation.y += delta * (i % 2 === 0 ? 2.6 : -2.6); });
    }
    if (doorState !== 'closed' && doorState !== 'open' && doorState !== 'ready_terminal') {
        const dtd = camPos.distanceTo(doorGroup.position), vs = Math.max(0, 1 - dtd / 55);
        if (!state.gameWon && dtd < 50) { camera.rotation.z = (Math.random() - 0.5) * (50 - dtd) * 0.0012; }
        doorSnd('klaxon', vs * 0.018);

        if (doorState === 'valves_pressure') {
            valves.forEach(v => v.rotation.z += delta * Math.PI * 1.5);
            if (Math.random() > 0.5) emitSteam(doorGroup.position.x + (Math.random() - 0.5) * 4, 1.2, doorGroup.position.z - 1.5);
            doorSnd('steam', vs * 0.14);
            if (valves[0].rotation.z > Math.PI * 6) {
                setDoorState('vault_unlock');
                doorSnd('steam', 0); doorSnd('grind', vs * 0.05);
            }
        } else if (doorState === 'vault_unlock') {
            vaultWG.rotation.z += delta * (Math.PI / 4.2);
            doorSnd('grind', vs * 0.05);
            if (vaultWG.rotation.z > Math.PI * 2.0) {
                setDoorState('unlatching'); matInd.color.setHex(0x00ff00);
                doorSnd('grind', 0);
                [0, 0.18, 0.36].forEach(delay => setTimeout(() => doorSnd('bolt', 0.18), delay * 1000));
            }
        } else if (doorState === 'unlatching') {
            const bs = delta * 0.85;
            deadboltsL.forEach(b => { b.position.x -= bs * 4.2; });
            deadboltsR.forEach(b => { b.position.x += bs * 4.2; });
            if (deadboltsL[0].position.x < -9.0) {
                setDoorState('sliding');
                doorSnd('grind', vs * 0.10); doorSnd('rumble', vs * 0.12);
            }
        } else if (doorState === 'sliding') {
            const PW = 5.0;
            if (doorHL.position.x > -PW - 3.5) {
                const sl = delta * 0.58;
                doorHL.position.x -= sl; doorHR.position.x += sl;
                mgL.rotation.z -= sl / GR; mgR.rotation.z += sl / GR;
                hgL.rotation.z += (sl / GR) * (GR / HGR); hgR.rotation.z -= (sl / GR) * (GR / HGR);
                if (Math.random() > 0.35) {
                    emitSpark(doorGroup.position.x - 3.0, gearYPos, gearZPos - 0.3);
                    emitSpark(doorGroup.position.x + 3.0, gearYPos, gearZPos - 0.3);
                }
                doorSnd('grind', vs * 0.10); doorSnd('rumble', vs * 0.12);
            } else {
                setDoorState('open');
                sirens.forEach(s => s.light.intensity = 0);
                doorSnd('klaxon', 0); doorSnd('grind', 0); doorSnd('rumble', 0);
                setTimeout(stopAllDoorAudio, 2000);
            }
        }
    }

    // --- UPDATE DUST PARTICLES (OPTIMIZED) ---
    if (dustParticles) {
        dustParticles.rotation.y -= 0.0004;
        dustParticles.position.y = Math.sin(Date.now() * 0.0005) * 0.5;
    }

    // ---- WIN ----
    if (doorState === 'open' && camPos.z > doorGroup.position.z + 1.5 && !state.gameWon) {
        state.gameWon = true; document.exitPointerLock();
        const ws = document.getElementById('win-screen'), fb = document.getElementById('fade-black');
        ws.style.display = 'flex'; setTimeout(() => { fb.style.opacity = '1'; ws.style.opacity = '1'; }, 50);
        document.getElementById('finalTime').innerText = `FINAL TIME: ${totalElapsed}s`;
        elPrompt.style.display = 'none';
        try { stopAllDoorAudio(); } catch (_) { }
    }
}


function animate() { requestAnimationFrame(animate); update(); renderer.render(scene, camera); }
animate();

window.addEventListener('resize', () => { camera.aspect = innerWidth / innerHeight; camera.updateProjectionMatrix(); renderer.setSize(innerWidth, innerHeight); });

document.getElementById('reboot-btn').addEventListener('click', () => {
    const d = document.getElementById('death-screen-ui'); d.style.transition = 'opacity 0.5s'; d.style.opacity = '0'; setTimeout(() => location.reload(), 500);
});
