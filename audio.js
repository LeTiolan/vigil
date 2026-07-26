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

// Deep guttural roar/scream — layered sub-bass growl, a wobbling mid
// growl voice, and a swept noise rasp, all through soft-clip distortion
// so it reads as guttural rather than a clean tone.
export function playRoar() {
    resume();
    const t = audioCtx.currentTime;
    const dur = 1.6;

    const master = audioCtx.createGain();
    master.gain.setValueAtTime(0.0001, t);
    master.gain.exponentialRampToValueAtTime(0.55, t + 0.08);
    master.gain.exponentialRampToValueAtTime(0.3, t + 0.5);
    master.gain.exponentialRampToValueAtTime(0.001, t + dur);

    const shaper = audioCtx.createWaveShaper();
    const curve = new Float32Array(256);
    for (let i = 0; i < 256; i++) { const x = (i / 255) * 2 - 1; curve[i] = Math.tanh(x * 3.2); }
    shaper.curve = curve; shaper.oversample = '2x';
    shaper.connect(master); master.connect(audioCtx.destination);

    // Sub-bass growl, pitch sagging the whole duration
    const sub = audioCtx.createOscillator(); sub.type = 'sawtooth';
    sub.frequency.setValueAtTime(90, t); sub.frequency.exponentialRampToValueAtTime(46, t + dur);
    const subGain = audioCtx.createGain(); subGain.gain.value = 0.9;
    sub.connect(subGain); subGain.connect(shaper); sub.start(t); sub.stop(t + dur);

    // Mid growl voice with a wobble LFO for texture
    const mid = audioCtx.createOscillator(); mid.type = 'sawtooth';
    mid.frequency.setValueAtTime(170, t); mid.frequency.exponentialRampToValueAtTime(88, t + dur);
    const wobble = audioCtx.createOscillator(); wobble.frequency.value = 14;
    const wobbleGain = audioCtx.createGain(); wobbleGain.gain.value = 25;
    wobble.connect(wobbleGain); wobbleGain.connect(mid.frequency); wobble.start(t); wobble.stop(t + dur);
    const midGain = audioCtx.createGain(); midGain.gain.value = 0.6;
    mid.connect(midGain); midGain.connect(shaper); mid.start(t); mid.stop(t + dur);

    // Swept noise rasp for scream breathiness
    const bufSize = Math.floor(audioCtx.sampleRate * dur);
    const buf = audioCtx.createBuffer(1, bufSize, audioCtx.sampleRate);
    const data = buf.getChannelData(0);
    for (let i = 0; i < bufSize; i++) data[i] = Math.random() * 2 - 1;
    const noise = audioCtx.createBufferSource(); noise.buffer = buf;
    const bp = audioCtx.createBiquadFilter(); bp.type = 'bandpass';
    bp.frequency.setValueAtTime(900, t); bp.frequency.exponentialRampToValueAtTime(300, t + dur); bp.Q.value = 1.4;
    const noiseGain = audioCtx.createGain();
    noiseGain.gain.setValueAtTime(0.0001, t);
    noiseGain.gain.exponentialRampToValueAtTime(0.35, t + 0.15);
    noiseGain.gain.exponentialRampToValueAtTime(0.001, t + dur);
    noise.connect(bp); bp.connect(noiseGain); noiseGain.connect(shaper); noise.start(t); noise.stop(t + dur);
}

// Heavy footfall thud for the creatures' walk/run cycle.
export function playStomp(vol = 1) {
    resume();
    const t = audioCtx.currentTime;
    const o = audioCtx.createOscillator(), g = audioCtx.createGain();
    o.type = 'sine';
    o.frequency.setValueAtTime(72, t); o.frequency.exponentialRampToValueAtTime(34, t + 0.18);
    g.gain.setValueAtTime(0.5 * vol, t); g.gain.exponentialRampToValueAtTime(0.001, t + 0.22);
    o.connect(g); g.connect(audioCtx.destination); o.start(t); o.stop(t + 0.22);

    const bufSize = Math.floor(audioCtx.sampleRate * 0.08);
    const buf = audioCtx.createBuffer(1, bufSize, audioCtx.sampleRate);
    const d = buf.getChannelData(0);
    for (let i = 0; i < bufSize; i++) d[i] = (Math.random() * 2 - 1) * Math.pow(1 - i / bufSize, 2);
    const n = audioCtx.createBufferSource(); n.buffer = buf;
    const lp = audioCtx.createBiquadFilter(); lp.type = 'lowpass'; lp.frequency.value = 400;
    const ng = audioCtx.createGain(); ng.gain.value = 0.3 * vol;
    n.connect(lp); lp.connect(ng); ng.connect(audioCtx.destination); n.start(t);
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
