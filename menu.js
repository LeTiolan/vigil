import { state, SENSITIVITY } from './state.js';
import { camera } from './scene-setup.js';
import { playUISound, playTerminalClick, initIndustrialAudio } from './audio.js';
import { doorGroup, TERM_WX, TERM_WZ, termBtn, termScreenMat, termLight, ledMat, sirens, setDoorState, initDoorAudio } from './door.js';

// ================================================================
//  MENU + INPUT
// ================================================================
const uiContainer = document.getElementById('main-ui');
const engageBtn = document.getElementById('engage-btn');
const nameInput = document.getElementById('name-input');
const bgText = document.getElementById('input-bg-text');

const quotes = ["The corridors are wide, but the paths are many.", "Do not trust the geometry.", "They do not stop until you stop.", "The light draws them. So does sound.", "Some things cannot be outrun."];
document.getElementById('lore-text').innerText = `"${quotes[Math.floor(Math.random() * quotes.length)]}"`;

nameInput.addEventListener('focus', () => { if (!nameInput.value) { bgText.innerHTML = '<div class="dots"><span>.</span><span>.</span><span>.</span></div>'; bgText.style.opacity = '1'; } });
nameInput.addEventListener('blur', () => { if (!nameInput.value) { bgText.innerHTML = 'NAMETAG'; bgText.style.opacity = '1'; } });
nameInput.addEventListener('input', e => { playUISound(90, 1.2, 0.25, 'triangle'); e.target.value = e.target.value.replace(/[^A-Za-z]/g, '').toUpperCase(); if (nameInput.value.length > 0) bgText.style.opacity = '0'; else { bgText.style.opacity = '1'; bgText.innerHTML = '<div class="dots"><span>.</span><span>.</span><span>.</span></div>'; } });
nameInput.addEventListener('keydown', e => e.stopPropagation()); nameInput.addEventListener('keyup', e => e.stopPropagation());
document.querySelectorAll('#main-ui button,#main-ui input').forEach(el => { el.addEventListener('mouseenter', () => playUISound(500, 0.5, 0.08, 'triangle')); if (el !== engageBtn) el.addEventListener('mousedown', () => playUISound(180, 1.5, 0.2, 'sine')); else el.addEventListener('mousedown', () => playUISound(100, 2.0, 0.4, 'sine')); });
engageBtn.addEventListener('mousedown', () => { const g = document.querySelector('.grid-container'); g.classList.remove('shake-active'); void g.offsetWidth; g.classList.add('shake-active'); document.body.requestPointerLock(); initIndustrialAudio(); });

document.addEventListener('pointerlockchange', () => {
    if (document.pointerLockElement === document.body) {
        uiContainer.style.display = 'none'; state.gameActive = true; if (state.startTime === 0) state.startTime = Date.now(); state.prevTime = performance.now();
        if (!state.introShown) {
            state.introShown = true; const name = nameInput.value || 'OPERATIVE';
            const fb = document.getElementById('fade-black');
            fb.style.cssText = 'position:fixed;top:0;left:0;width:100%;height:100%;background:#000;z-index:200;opacity:1;display:flex;align-items:center;justify-content:center;pointer-events:none;transition:none;';
            fb.innerHTML = `<div style="text-align:center;font-family:'Courier New',monospace;color:#a88840;letter-spacing:4px;"><div style="font-size:1.4em;font-weight:bold;margin-bottom:10px;">OPERATIVE: ${name}</div><div style="font-size:0.7em;color:#4a3820;letter-spacing:6px;margin-top:8px;">SIGNAL LOCKED — DEPLOYING</div></div>`;
            setTimeout(() => { fb.style.transition = 'opacity 1.8s ease-in-out'; fb.style.opacity = '0'; setTimeout(() => { fb.style.cssText = 'position:fixed;top:0;left:0;width:100%;height:100%;background:#000;opacity:0;z-index:105;transition:opacity 3s ease-in-out;pointer-events:none;'; fb.innerHTML = ''; }, 1900); }, 1600);
        }
    } else if (!state.gameWon) {
        uiContainer.style.display = 'flex'; document.getElementById('main-title').innerText = 'SYSTEM PAUSED'; engageBtn.innerText = 'RESUME';
        state.gameActive = false; state.accumulatedTime += (Date.now() - state.startTime) / 1000; document.getElementById('menuOrbCount').innerText = state.orbsCollected;
        document.getElementById('interact-prompt').style.display = 'none';
    }
});

document.addEventListener('mousemove', e => {
    if (document.pointerLockElement === document.body) {
        state.yaw -= e.movementX * SENSITIVITY; state.pitch -= e.movementY * SENSITIVITY;
        state.pitch = Math.max(-Math.PI / 2, Math.min(Math.PI / 2, state.pitch));
        camera.rotation.set(state.pitch, state.yaw, 0);
    }
});

document.addEventListener('keydown', e => {
    // --- Exit terminal: E activates it when all objectives done ---
    if (e.code === 'KeyE' && state.gameActive && !state.gameWon && doorState === 'ready_terminal') {
        if (Math.hypot(camera.position.x - TERM_WX, camera.position.z - TERM_WZ) < 9) {
            state.terminalActivated = true; state.terminalBtnT = 0.18;
            termBtn.position.z = 0.44;
            termScreenMat.color.setHex(0xff4400); termLight.color.setHex(0xff6600); termLight.intensity = 4;
            ledMat.color.setHex(0xff4400); playTerminalClick();
            setTimeout(() => { setDoorState('valves_pressure'); initDoorAudio(); sirens.forEach(s => s.light.intensity = 50); }, 700);
        }
    }
});
