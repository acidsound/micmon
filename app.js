"use strict";

/* ============ 상수 ============ */
const PITCH_MIN_MIDI = 36; // C2
const PITCH_MAX_MIDI = 84; // C6
const VOL_MIN_DB = -60;
const VOL_MAX_DB = 0;
const NOTE_NAMES = ["C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B"];
const BLACK_KEYS = new Set([1, 3, 6, 8, 10]);

/* ============ DOM ============ */
const recordBtn = document.getElementById("recordBtn");
const recordLabel = document.getElementById("recordLabel");
const demoBtn = document.getElementById("demoBtn");
const clearBtn = document.getElementById("clearBtn");
const statusDot = document.getElementById("statusDot");
const statusText = document.getElementById("statusText");
const noteValue = document.getElementById("noteValue");
const freqValue = document.getElementById("freqValue");
const volValue = document.getElementById("volValue");
const centsValue = document.getElementById("centsValue");
const tunerNeedle = document.getElementById("tunerNeedle");
const pitchCanvas = document.getElementById("pitchCanvas");
const volumeCanvas = document.getElementById("volumeCanvas");
const pitchEmpty = document.getElementById("pitchEmpty");
const volumeEmpty = document.getElementById("volumeEmpty");
const timeWindowInput = document.getElementById("timeWindow");
const timeWindowVal = document.getElementById("timeWindowVal");
const smoothingInput = document.getElementById("smoothing");
const smoothingVal = document.getElementById("smoothingVal");
const sensitivityInput = document.getElementById("sensitivity");
const sensitivityVal = document.getElementById("sensitivityVal");

/* ============ 상태 ============ */
let audioCtx = null;
let analyser = null;
let stream = null;
let sourceNode = null;
let timeData = null;
let mode = "idle"; // idle | mic | demo
let rafId = null;
let history = []; // {t, freq, midi, db, volNorm, pitchNorm}
let lastSmoothedMidi = null;
let lastSmoothedDb = null;
let demoStartTime = 0;
let lastFrameTime = 0;

function getTimeWindow() { return parseFloat(timeWindowInput.value); }
function getSmoothing() { return parseFloat(smoothingInput.value); }
function getSensitivity() { return parseFloat(sensitivityInput.value); }

function clamp(v, a, b) { return Math.min(b, Math.max(a, v)); }

function freqToMidi(freq) {
  if (!freq || freq <= 0) return null;
  return 69 + 12 * Math.log2(freq / 440);
}
function midiToFreq(midi) { return 440 * Math.pow(2, (midi - 69) / 12); }
function midiToNoteName(midi) {
  const m = Math.round(midi);
  const name = NOTE_NAMES[((m % 12) + 12) % 12];
  const octave = Math.floor(m / 12) - 1;
  return name + octave;
}
function colorFor(norm, alpha = 1) {
  const n = clamp(norm, 0, 1);
  const hue = 217 + (360 - 217) * n; // 파랑(217) → 빨강(360)
  return `hsla(${hue}, 90%, 62%, ${alpha})`;
}

/* ============ Pitch 검출 (Autocorrelation) ============ */
function detectPitch(buf, sampleRate) {
  const SIZE = buf.length;
  let rms = 0;
  for (let i = 0; i < SIZE; i++) rms += buf[i] * buf[i];
  rms = Math.sqrt(rms / SIZE);
  if (rms < 0.008) return { freq: -1, rms };

  const minLag = Math.floor(sampleRate / 1000);
  const maxLag = Math.ceil(sampleRate / 50);
  let bestLag = -1;
  let bestCorr = -1;

  // 자기상관
  for (let lag = minLag; lag <= maxLag; lag++) {
    let corr = 0;
    const limit = SIZE - lag;
    for (let i = 0; i < limit; i++) corr += buf[i] * buf[i + lag];
    corr /= limit;
    if (corr > bestCorr) { bestCorr = corr; bestLag = lag; }
  }
  if (bestLag <= minLag || bestLag >= maxLag) return { freq: -1, rms };
  // 신뢰도: bestCorr 가 rms^2 대비 너무 낮으면 무성음으로 판단
  if (bestCorr < rms * rms * 0.25) return { freq: -1, rms };

  // 포물선 보간으로 정밀도 향상
  const corrAt = (lag) => {
    let c = 0;
    const limit = SIZE - lag;
    for (let i = 0; i < limit; i++) c += buf[i] * buf[i + lag];
    return c / limit;
  };
  const c0 = corrAt(bestLag - 1);
  const c1 = bestCorr;
  const c2 = corrAt(bestLag + 1);
  const denom = c0 + c2 - 2 * c1;
  let shift = 0;
  if (denom !== 0) shift = 0.5 * (c0 - c2) / denom;
  const refinedLag = bestLag + shift;
  const freq = sampleRate / refinedLag;
  if (freq < 50 || freq > 1000) return { freq: -1, rms };
  return { freq, rms };
}

function rmsToDb(rms, sensitivity) {
  const g = rms * sensitivity;
  if (g <= 0.0001) return VOL_MIN_DB;
  const db = 20 * Math.log10(g);
  return clamp(db, VOL_MIN_DB, VOL_MAX_DB);
}

/* ============ 데모 신호 생성 ============ */
const DEMO_NOTES = [220.0, 261.63, 329.63, 196.0, 246.94, 293.66, 220.0, 174.61];
function demoSample(nowSec) {
  const t = nowSec;
  const noteIdx = Math.floor(t / 2) % DEMO_NOTES.length;
  const base = DEMO_NOTES[noteIdx];
  const phase = (t % 2) / 2;
  // 비브라토 + 글라이드
  const vibrato = 1 + 0.006 * Math.sin(t * 2 * Math.PI * 5.5);
  const glide = 1 + 0.04 * Math.exp(-phase * 6) * (noteIdx % 2 === 0 ? 1 : -1);
  const freq = base * vibrato * glide;
  // 볼륨 엔벨로프 (말하는 듯한 패턴)
  let db = -20 + 9 * Math.sin(t * 2.7) + 5 * Math.sin(t * 6.1) + 3 * Math.sin(t * 11.3);
  if (t % 4 > 3.4) db = -52 + Math.random() * 3; // 짧은 휴지
  db = clamp(db, VOL_MIN_DB, VOL_MAX_DB);
  return { freq, db };
}

/* ============ 샘플링 ============ */
function sampleMic() {
  if (!analyser || !timeData) return null;
  analyser.getFloatTimeDomainData(timeData);
  const { freq, rms } = detectPitch(timeData, audioCtx.sampleRate);
  const db = rmsToDb(rms, getSensitivity());
  return { freq, db };
}

function pushSample(freq, db) {
  const now = performance.now() / 1000;
  const smoothing = getSmoothing();

  let midi = freq > 0 ? freqToMidi(freq) : null;

  // 스무딩
  if (midi !== null) {
    if (lastSmoothedMidi !== null) {
      midi = lastSmoothedMidi * smoothing + midi * (1 - smoothing);
    }
    lastSmoothedMidi = midi;
  } else {
    lastSmoothedMidi = null;
  }
  let sDb = db;
  if (lastSmoothedDb !== null) {
    sDb = lastSmoothedDb * smoothing + db * (1 - smoothing);
  }
  lastSmoothedDb = sDb;

  const volNorm = clamp((sDb - VOL_MIN_DB) / (VOL_MAX_DB - VOL_MIN_DB), 0, 1);
  const pitchNorm = midi !== null
    ? clamp((midi - PITCH_MIN_MIDI) / (PITCH_MAX_MIDI - PITCH_MIN_MIDI), 0, 1)
    : null;

  history.push({
    t: now,
    freq: midi !== null ? midiToFreq(midi) : -1,
    midi,
    db: sDb,
    volNorm,
    pitchNorm,
  });

  // 윈도우 초과분 제거
  const cutoff = now - getTimeWindow() - 0.5;
  while (history.length && history[0].t < cutoff) history.shift();

  updateReadouts(history[history.length - 1]);
}

function updateReadouts(last) {
  if (!last) return;
  if (last.midi !== null) {
    const rounded = Math.round(last.midi);
    const cents = Math.round((last.midi - rounded) * 100);
    noteValue.textContent = midiToNoteName(last.midi);
    freqValue.textContent = last.freq.toFixed(1) + " Hz";
    centsValue.textContent = (cents > 0 ? "+" : "") + cents + " cents";
    const pct = clamp(50 + cents, 0, 100);
    tunerNeedle.style.left = pct + "%";
    tunerNeedle.style.background = Math.abs(cents) <= 5 ? "#22c55e" : Math.abs(cents) <= 15 ? "#eab308" : "#ef4444";
  } else {
    noteValue.textContent = "—";
    freqValue.textContent = "무성음";
    centsValue.textContent = "— cents";
    tunerNeedle.style.left = "50%";
    tunerNeedle.style.background = "#64748b";
  }
  volValue.textContent = last.db.toFixed(1) + " dB";
}

/* ============ 캔버스 렌더링 ============ */
function setupCanvas(canvas) {
  const dpr = window.devicePixelRatio || 1;
  const rect = canvas.getBoundingClientRect();
  const w = Math.max(1, Math.floor(rect.width * dpr));
  const h = Math.max(1, Math.floor(rect.height * dpr));
  if (canvas.width !== w || canvas.height !== h) {
    canvas.width = w;
    canvas.height = h;
  }
  const ctx = canvas.getContext("2d");
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  return { ctx, w: rect.width, h: rect.height };
}

const PAD = { left: 58, right: 12, top: 10, bottom: 30 };

function midiToY(midi, plotTop, plotH) {
  const n = clamp((midi - PITCH_MIN_MIDI) / (PITCH_MAX_MIDI - PITCH_MIN_MIDI), 0, 1);
  return plotTop + plotH - n * plotH;
}
function dbToY(db, plotTop, plotH) {
  const n = clamp((db - VOL_MIN_DB) / (VOL_MAX_DB - VOL_MIN_DB), 0, 1);
  return plotTop + plotH - n * plotH;
}
function timeToX(t, now, windowSec, plotLeft, plotW) {
  const start = now - windowSec;
  return plotLeft + ((t - start) / windowSec) * plotW;
}

function drawTimeGrid(ctx, plotLeft, plotTop, plotW, plotH, now, windowSec) {
  ctx.save();
  ctx.strokeStyle = "rgba(148,163,184,0.12)";
  ctx.fillStyle = "rgba(148,163,184,0.75)";
  ctx.font = "11px -apple-system, sans-serif";
  ctx.textAlign = "center";
  const start = now - windowSec;
  const firstSec = Math.ceil(start);
  for (let s = firstSec; s <= now; s++) {
    const x = timeToX(s, now, windowSec, plotLeft, plotW);
    ctx.beginPath();
    ctx.moveTo(x, plotTop);
    ctx.lineTo(x, plotTop + plotH);
    ctx.stroke();
    const ago = Math.round(now - s);
    ctx.fillText(ago === 0 ? "지금" : ago + "초 전", x, plotTop + plotH + 18);
  }
  ctx.restore();
}

function drawPitchGrid(ctx, plotLeft, plotTop, plotW, plotH) {
  ctx.save();
  const total = PITCH_MAX_MIDI - PITCH_MIN_MIDI;
  const bandH = plotH / total;

  // 건반 배경: 검은 건반 밴드
  for (let m = PITCH_MIN_MIDI; m < PITCH_MAX_MIDI; m++) {
    const isBlack = BLACK_KEYS.has(((m % 12) + 12) % 12);
    const y = midiToY(m + 1, plotTop, plotH);
    if (isBlack) {
      ctx.fillStyle = "rgba(255,255,255,0.055)";
      ctx.fillRect(plotLeft, y, plotW, bandH);
    }
  }

  // 반음 그리드 라인
  ctx.font = "11px -apple-system, sans-serif";
  ctx.textAlign = "right";
  for (let m = PITCH_MIN_MIDI; m <= PITCH_MAX_MIDI; m++) {
    const y = midiToY(m, plotTop, plotH);
    const isC = ((m % 12) + 12) % 12 === 0;
    const isBlack = BLACK_KEYS.has(((m % 12) + 12) % 12);
    ctx.strokeStyle = isC ? "rgba(226,232,240,0.35)" : isBlack ? "rgba(148,163,184,0.10)" : "rgba(148,163,184,0.16)";
    ctx.lineWidth = isC ? 1.2 : 1;
    ctx.beginPath();
    ctx.moveTo(plotLeft, y);
    ctx.lineTo(plotLeft + plotW, y);
    ctx.stroke();

    if (isC) {
      ctx.fillStyle = "rgba(226,232,240,0.9)";
      ctx.font = "bold 11px -apple-system, sans-serif";
      ctx.fillText(midiToNoteName(m), plotLeft - 8, y + 4);
    } else if (m % 12 === 9) { // A 라벨 보조
      ctx.fillStyle = "rgba(148,163,184,0.55)";
      ctx.font = "10px -apple-system, sans-serif";
      ctx.fillText(midiToNoteName(m), plotLeft - 8, y + 4);
    }
  }
  ctx.restore();
}

function drawVolumeGrid(ctx, plotLeft, plotTop, plotW, plotH) {
  ctx.save();
  ctx.font = "11px -apple-system, sans-serif";
  ctx.textAlign = "right";
  for (let db = VOL_MIN_DB; db <= VOL_MAX_DB; db += 10) {
    const y = dbToY(db, plotTop, plotH);
    const isZero = db === 0;
    ctx.strokeStyle = isZero ? "rgba(239,68,68,0.35)" : "rgba(148,163,184,0.16)";
    ctx.lineWidth = isZero ? 1.2 : 1;
    ctx.beginPath();
    ctx.moveTo(plotLeft, y);
    ctx.lineTo(plotLeft + plotW, y);
    ctx.stroke();
    ctx.fillStyle = isZero ? "rgba(248,113,113,0.9)" : "rgba(148,163,184,0.75)";
    ctx.fillText(db + "dB", plotLeft - 8, y + 4);
  }
  ctx.restore();
}

function drawTrace(ctx, plotLeft, plotTop, plotW, plotH, now, windowSec, getY, getColorNorm, isPitch) {
  if (history.length < 2) return;
  ctx.save();
  ctx.lineWidth = 2.5;
  ctx.lineJoin = "round";
  ctx.lineCap = "round";

  let prev = null;
  for (let i = 0; i < history.length; i++) {
    const p = history[i];
    if (p.t < now - windowSec) { prev = null; continue; }
    const yVal = getY(p);
    if (yVal === null) { prev = null; continue; }
    const x = timeToX(p.t, now, windowSec, plotLeft, plotW);
    const y = yVal;
    if (prev) {
      const norm = getColorNorm(p);
      ctx.strokeStyle = norm === null ? "rgba(100,116,139,0.7)" : colorFor(norm);
      ctx.beginPath();
      ctx.moveTo(prev.x, prev.y);
      ctx.lineTo(x, y);
      ctx.stroke();
    }
    prev = { x, y };
  }

  // 현재 값 도트
  const last = history[history.length - 1];
  if (last) {
    const yVal = getY(last);
    if (yVal !== null) {
      const x = timeToX(last.t, now, windowSec, plotLeft, plotW);
      const norm = getColorNorm(last);
      ctx.beginPath();
      ctx.arc(x, yVal, 5, 0, Math.PI * 2);
      ctx.fillStyle = norm === null ? "#64748b" : colorFor(norm);
      ctx.fill();
      ctx.lineWidth = 2;
      ctx.strokeStyle = "white";
      ctx.stroke();
    }
  }
  ctx.restore();
}

function render() {
  const now = performance.now() / 1000;
  const windowSec = getTimeWindow();

  // Pitch
  {
    const { ctx, w, h } = setupCanvas(pitchCanvas);
    const plotLeft = PAD.left, plotTop = PAD.top;
    const plotW = w - PAD.left - PAD.right;
    const plotH = h - PAD.top - PAD.bottom;
    ctx.clearRect(0, 0, w, h);
    ctx.fillStyle = "#0a0f1e";
    ctx.fillRect(0, 0, w, h);
    drawPitchGrid(ctx, plotLeft, plotTop, plotW, plotH);
    drawTimeGrid(ctx, plotLeft, plotTop, plotW, plotH, now, windowSec);
    // 음정 그래프: 색상 = 볼륨
    drawTrace(ctx, plotLeft, plotTop, plotW, plotH, now, windowSec,
      (p) => (p.midi === null ? null : midiToY(p.midi, plotTop, plotH)),
      (p) => p.volNorm,
      true);
    // 축 테두리
    ctx.strokeStyle = "rgba(148,163,184,0.25)";
    ctx.strokeRect(plotLeft, plotTop, plotW, plotH);
  }

  // Volume
  {
    const { ctx, w, h } = setupCanvas(volumeCanvas);
    const plotLeft = PAD.left, plotTop = PAD.top;
    const plotW = w - PAD.left - PAD.right;
    const plotH = h - PAD.top - PAD.bottom;
    ctx.clearRect(0, 0, w, h);
    ctx.fillStyle = "#0a0f1e";
    ctx.fillRect(0, 0, w, h);
    drawVolumeGrid(ctx, plotLeft, plotTop, plotW, plotH);
    drawTimeGrid(ctx, plotLeft, plotTop, plotW, plotH, now, windowSec);
    // 볼륨 그래프: 색상 = 음정
    drawTrace(ctx, plotLeft, plotTop, plotW, plotH, now, windowSec,
      (p) => dbToY(p.db, plotTop, plotH),
      (p) => p.pitchNorm,
      false);
    ctx.strokeStyle = "rgba(148,163,184,0.25)";
    ctx.strokeRect(plotLeft, plotTop, plotW, plotH);
  }

  // empty state 토글
  const hasData = history.length > 5;
  pitchEmpty.classList.toggle("hidden", hasData);
  volumeEmpty.classList.toggle("hidden", hasData);
}

/* ============ 메인 루프 ============ */
function loop() {
  rafId = requestAnimationFrame(loop);
  const nowMs = performance.now();
  // 샘플링은 ~30fps 로 제한 (렌더링은 60fps)
  if (mode !== "idle" && nowMs - lastFrameTime >= 33) {
    lastFrameTime = nowMs;
    if (mode === "mic") {
      const s = sampleMic();
      if (s) pushSample(s.freq, s.db);
    } else if (mode === "demo") {
      const s = demoSample((nowMs - demoStartTime) / 1000);
      pushSample(s.freq, s.db);
    }
  }
  render();
}

/* ============ 시작/정지 ============ */
function setStatus(text, cls) {
  statusText.textContent = text;
  statusDot.className = "status-dot " + cls;
}

async function startMic() {
  try {
    setStatus("마이크 연결 중…", "demo");
    stream = await navigator.mediaDevices.getUserMedia({
      audio: { echoCancellation: false, noiseSuppression: false, autoGainControl: false },
    });
    audioCtx = new (window.AudioContext || window.webkitAudioContext)();
    await audioCtx.resume();
    sourceNode = audioCtx.createMediaStreamSource(stream);
    analyser = audioCtx.createAnalyser();
    analyser.fftSize = 2048;
    analyser.smoothingTimeConstant = 0;
    sourceNode.connect(analyser);
    timeData = new Float32Array(analyser.fftSize);
    mode = "mic";
    setStatus("녹음 중", "recording");
    recordBtn.classList.add("stop");
    recordLabel.textContent = "Stop";
    demoBtn.classList.remove("active");
  } catch (err) {
    console.error(err);
    setStatus("마이크 권한 없음 — 데모 모드를 사용하세요", "error");
    alert("마이크 권한을 허용해 주세요.\n브라우저 주소창의 마이크 아이콘을 클릭해 허용할 수 있습니다.\n\n마이크가 없을 경우 '데모 모드'로 그래프 동작을 확인할 수 있습니다.");
  }
}

function startDemo() {
  stopAll(true);
  mode = "demo";
  demoStartTime = performance.now();
  setStatus("데모 재생 중", "demo");
  recordBtn.classList.add("stop");
  recordLabel.textContent = "Stop";
  demoBtn.classList.add("active");
}

function stopAll(keepHistory) {
  if (stream) { stream.getTracks().forEach((t) => t.stop()); stream = null; }
  if (sourceNode) { try { sourceNode.disconnect(); } catch (_) {} sourceNode = null; }
  if (audioCtx) { audioCtx.close().catch(() => {}); audioCtx = null; }
  analyser = null;
  timeData = null;
  mode = "idle";
  if (!keepHistory) {
    history = [];
    lastSmoothedMidi = null;
    lastSmoothedDb = null;
    noteValue.textContent = "—";
    freqValue.textContent = "— Hz";
    volValue.textContent = "— dB";
    centsValue.textContent = "— cents";
    tunerNeedle.style.left = "50%";
  }
  setStatus("대기 중", "idle");
  recordBtn.classList.remove("stop");
  recordLabel.textContent = "Record 시작";
  demoBtn.classList.remove("active");
}

/* ============ 이벤트 ============ */
recordBtn.addEventListener("click", () => {
  if (mode === "idle") startMic();
  else stopAll(false);
});
demoBtn.addEventListener("click", () => {
  if (mode === "demo") stopAll(false);
  else startDemo();
});
clearBtn.addEventListener("click", () => {
  history = [];
  lastSmoothedMidi = null;
  lastSmoothedDb = null;
});

timeWindowInput.addEventListener("input", () => {
  timeWindowVal.textContent = timeWindowInput.value + "초";
});
smoothingInput.addEventListener("input", () => {
  smoothingVal.textContent = smoothingInput.value;
});
sensitivityInput.addEventListener("input", () => {
  sensitivityVal.textContent = sensitivityInput.value + "x";
});

window.addEventListener("resize", render);

/* ============ 초기화 ============ */
loop();
