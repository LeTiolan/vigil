import { TOTAL_ORBS } from './state.js';

// ================================================================
//  HUD DOM REFERENCES
// ================================================================
document.getElementById('totalOrbsUI').innerText = TOTAL_ORBS;

export const elOrbCount = document.getElementById('orbCount');
export const elTimeVal = document.getElementById('timeVal');
export const elStBar = document.getElementById('stamina-bar');
export const elStCont = document.getElementById('stamina-container');
export const elCross = document.getElementById('crosshair');
export const elPrompt = document.getElementById('interact-prompt');
export const radarCanvas = document.getElementById('radar');
export const rCtx = radarCanvas.getContext('2d');
export const RC = radarCanvas.width / 2, R_MAX = 105, R_SCL = (RC - 12) / R_MAX;
export const elPromptText = document.getElementById('prompt-text');