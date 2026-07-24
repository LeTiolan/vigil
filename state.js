import * as THREE from 'three';

// ================================================================
//  CONSTANTS & STATE
//
//  `state` is a single mutable object shared across every module.
//  Because ES module imports are live bindings but NOT reassignable
//  from outside their owning file, any value that gets reassigned
//  (not just mutated) from more than one file lives here as a
//  property instead of a bare `let` export. Always write
//  `state.xyz = ...`, never destructure it into a local `let`.
// ================================================================
export const TOTAL_ORBS = 12, MAX_STAMINA = 120;

// AI tuning
export const ALERT_DUR = 11.0, HUNT_DUR = 8.0, SEARCH_DUR = 14.0;
export const LIGHT_RANGE = 36, CONE_COS = Math.cos(58 * Math.PI / 180);
export const PATROL_SPD = 0.15, HUNT_SPD = 0.40, SEARCH_SPD = 0.12;
export const ENEMY_NAMES = ['REVENANT', 'UNIT-07', 'SPECTER-X', 'THE HOLLOW', 'SHADE-03', 'ECHO-NULL', 'WRAITH', 'ABSENCE'];
export const SENSITIVITY = 0.002;

export const state = {
    orbsCollected: 0,
    gameActive: false,
    gameWon: false,
    startTime: 0,
    accumulatedTime: 0,
    hasPlayedSting: false,
    prevTime: performance.now(),
    yaw: Math.PI,
    pitch: 0,
    introShown: false,
    sprintAlertCD: 0,
    lastFootCycle: 0,
    terminalActivated: false,
    terminalBtnT: 0,
    currentlySprinting: false,
    flashlightOn: true,
    corridorLights: [],
};

export const exploredCells = new Set();

// --- BULLETPROOF KEYBOARD TRACKER ---
export const keys = {};
window.addEventListener('keydown', (e) => { keys[e.code] = true; });
window.addEventListener('keyup', (e) => { keys[e.code] = false; });

export const player = {
    height: 2.1, radius: 0.8, walkSpeed: 0.22, runSpeed: 0.46,
    stamina: MAX_STAMINA, isExhausted: false,
    velocity: new THREE.Vector2(0, 0), headBobTimer: 0
};