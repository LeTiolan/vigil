// ================================================================
//  AUDIO
// ================================================================
export const audioCtx = new (window.AudioContext || window.webkitAudioContext)();

let klaxonOsc, klaxonGain, vaultOsc, vaultGain, latchOsc, latchGain, pistonOsc, pistonGain, gearOsc, gearGain, hissSrc, hissGain;

export function resume() { if (audioCtx.state === 'suspended') audioCtx.resume(); }

export function initIndustrialAudio() {
    resume();
    klaxonOsc = audioCtx.createOscillator(); klaxonOsc.type = 'triangle'; klaxonOsc.frequency.value = 450;
    const kL = audioCtx.createOscillator(); kL.frequency.value = 2; const kM = audioCtx.createGain(); kM.gain.value = 150; kL.connect(kM); kM.connect(klaxonOsc.frequency); kL.start();
    klaxonGain = audioCtx.createGain(); klaxonGain.gain.value = 0; klaxonOsc.connect(klaxonGain); klaxonGain.connect(audioCtx.destination); klaxonOsc.start();

    vaultOsc = audioCtx.createOscillator(); vaultOsc.type = 'sawtooth'; vaultOsc.frequency.value = 160;
    vaultGain = audioCtx.createGain(); vaultGain.gain.value = 0; vaultOsc.connect(vaultGain); vaultGain.connect(audioCtx.destination); vaultOsc.start();

    latchOsc = audioCtx.createOscillator(); latchOsc.type = 'sawtooth'; latchOsc.frequency.value = 80;
    latchGain = audioCtx.createGain(); latchGain.gain.value = 0; latchOsc.connect(latchGain); latchGain.connect(audioCtx.destination); latchOsc.start();

    pistonOsc = audioCtx.createOscillator(); pistonOsc.type = 'square'; pistonOsc.frequency.value = 28;
    pistonGain = audioCtx.createGain(); pistonGain.gain.value = 0;
    const pf = audioCtx.createBiquadFilter(); pf.type = 'lowpass'; pf.frequency.value = 120;
    pistonOsc.connect(pf); pf.connect(pistonGain); pistonGain.connect(audioCtx.destination); pistonOsc.start();

    gearOsc = audioCtx.createOscillator(); gearOsc.type = 'square'; gearOsc.frequency.value = 15;
    gearGain = audioCtx.createGain(); gearGain.gain.value = 0; gearOsc.connect(gearGain); gearGain.connect(audioCtx.destination); gearOsc.start();

    const bsz = audioCtx.sampleRate * 2, nb = audioCtx.createBuffer(1, bsz, audioCtx.sampleRate);
    const nd = nb.getChannelData(0); for (let i = 0; i < bsz; i++) nd[i] = Math.random() * 2 - 1;
    hissSrc = audioCtx.createBufferSource(); hissSrc.buffer = nb; hissSrc.loop = true;
    const hf = audioCtx.createBiquadFilter(); hf.type = 'highpass'; hf.frequency.value = 800;
    hissGain = audioCtx.createGain(); hissGain.gain.value = 0;
    hissSrc.connect(hf); hf.connect(hissGain); hissGain.connect(audioCtx.destination); hissSrc.start();
}

export function playSting() {
    resume(); const o = audioCtx.createOscillator(), g = audioCtx.createGain(); o.type = 'sawtooth';
    o.frequency.setValueAtTime(110, audioCtx.currentTime); o.frequency.exponentialRampToValueAtTime(25, audioCtx.currentTime + 1.2);
    g.gain.setValueAtTime(0.18, audioCtx.currentTime); g.gain.exponentialRampToValueAtTime(0.001, audioCtx.currentTime + 1.2);
    o.connect(g); g.connect(audioCtx.destination); o.start(); o.stop(audioCtx.currentTime + 1.2);
}

// Realistic footstep: soft multi-band noise burst with a short reverb tail
function buildFootBuf(sprint) {
    const dur = sprint ? 0.06 : 0.09;
    const sz = Math.floor(audioCtx.sampleRate * dur);
    const b = audioCtx.createBuffer(1, sz, audioCtx.sampleRate);
    const d = b.getChannelData(0);
    for (let i = 0; i < sz; i++) d[i] = (Math.random() * 2 - 1) * Math.pow(1 - i / sz, sprint ? 3 : 4.5);
    return b;
}

export function playFootstep(sprint) {
    resume();
    const buf = buildFootBuf(sprint);
    // Low thud component (LOUDER)
    const s1 = audioCtx.createBufferSource(); s1.buffer = buf;
    const lp = audioCtx.createBiquadFilter(); lp.type = 'lowpass'; lp.frequency.value = sprint ? 100 : 70;
    const g1 = audioCtx.createGain(); g1.gain.value = sprint ? 0.35 : 0.20;
    s1.connect(lp); lp.connect(g1); g1.connect(audioCtx.destination); s1.start();
    // Mid body (LOUDER)
    const s2 = audioCtx.createBufferSource(); s2.buffer = buf;
    const bp = audioCtx.createBiquadFilter(); bp.type = 'bandpass'; bp.frequency.value = sprint ? 240 : 160; bp.Q.value = 1.8;
    const g2 = audioCtx.createGain(); g2.gain.value = sprint ? 0.15 : 0.08;
    s2.connect(bp); bp.connect(g2); g2.connect(audioCtx.destination); s2.start();
    // Short reverb tail
    const s3 = audioCtx.createBufferSource(); s3.buffer = buf;
    const lp2 = audioCtx.createBiquadFilter(); lp2.type = 'lowpass'; lp2.frequency.value = 50;
    const g3 = audioCtx.createGain(); g3.gain.value = sprint ? 0.04 : 0.025;
    s3.connect(lp2); lp2.connect(g3); g3.connect(audioCtx.destination);
    s3.start(audioCtx.currentTime + 0.07);
}

// Orb collect chime — warm ascending tones
export function playOrbChime() {
    resume();
    [330, 528, 792, 1056].forEach((f, i) => {
        const o = audioCtx.createOscillator(), g = audioCtx.createGain(); o.type = 'sine'; o.frequency.value = f;
        const t = audioCtx.currentTime + i * 0.085;
        g.gain.setValueAtTime(0, t); g.gain.linearRampToValueAtTime(0.2, t + 0.015); g.gain.exponentialRampToValueAtTime(0.001, t + 0.28);
        o.connect(g); g.connect(audioCtx.destination); o.start(t); o.stop(t + 0.3);
    });
}

export function playFlashlightClick() {
    if (!audioCtx) return;
    const t = audioCtx.currentTime;
    // Metallic 'snap'
    const snapOsc = audioCtx.createOscillator();
    const snapGain = audioCtx.createGain();
    snapOsc.type = 'square';
    snapOsc.frequency.setValueAtTime(1200, t);
    snapOsc.frequency.exponentialRampToValueAtTime(100, t + 0.03);
    snapGain.gain.setValueAtTime(0.3, t);
    snapGain.gain.exponentialRampToValueAtTime(0.01, t + 0.03);
    snapOsc.connect(snapGain);
    snapGain.connect(audioCtx.destination);
    snapOsc.start(t);
    snapOsc.stop(t + 0.04);
    // Hollow 'clack'
    const clackOsc = audioCtx.createOscillator();
    const clackGain = audioCtx.createGain();
    clackOsc.type = 'triangle';
    clackOsc.frequency.setValueAtTime(400, t);
    clackOsc.frequency.exponentialRampToValueAtTime(50, t + 0.06);
    clackGain.gain.setValueAtTime(0.5, t);
    clackGain.gain.exponentialRampToValueAtTime(0.01, t + 0.06);
    clackOsc.connect(clackGain);
    clackGain.connect(audioCtx.destination);
    clackOsc.start(t);
    clackOsc.stop(t + 0.07);
}

export function playTerminalClick() {
    resume();
    [200, 140, 90, 60].forEach((f, i) => {
        const o = audioCtx.createOscillator(), g = audioCtx.createGain(); o.type = 'square'; o.frequency.value = f;
        const t = audioCtx.currentTime + i * 0.07;
        g.gain.setValueAtTime(0.16, t); g.gain.exponentialRampToValueAtTime(0.001, t + 0.12);
        o.connect(g); g.connect(audioCtx.destination); o.start(t); o.stop(t + 0.13);
    });
}

export function playUISound(freq, vol, dur, type = 'triangle') {
    resume(); const o = audioCtx.createOscillator(), g = audioCtx.createGain(); o.type = type;
    o.frequency.setValueAtTime(freq, audioCtx.currentTime); o.frequency.exponentialRampToValueAtTime(freq / 2, audioCtx.currentTime + dur);
    g.gain.setValueAtTime(vol, audioCtx.currentTime); g.gain.exponentialRampToValueAtTime(0.001, audioCtx.currentTime + dur);
    o.connect(g); g.connect(audioCtx.destination); o.start(); o.stop(audioCtx.currentTime + dur);
}