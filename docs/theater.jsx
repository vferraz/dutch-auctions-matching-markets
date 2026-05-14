// Session Theater — animated Monte Carlo visualization for v2.
// Plots rider values as dots arriving over time; each mechanism's
// acceptance line cuts the plane and dots get colored accept/reject.
// PP-batch dots stay "pending" until t=T then settle simultaneously.

const { useState, useEffect, useMemo, useRef, useCallback } = React;

// Deterministic seeded PRNG (mulberry32)
function mulberry32(seed) {
  let s = seed >>> 0;
  return function () {
    s = (s + 0x6D2B79F5) >>> 0;
    let t = s;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

// Generate Poisson contact events shared across mechanisms.
function generateEvents(p, seed) {
  const rand = mulberry32(seed);
  // event rate: μD(θ) per "lane unit"; tune density for visual richness
  const rate = window.Model.muD(p.theta, p.A, p.beta) * 2.5;
  const events = [];
  let t = 0;
  while (events.length < 300) {
    const u = Math.max(1e-9, rand());
    t += -Math.log(u) / rate;
    if (t >= p.T) break;
    events.push({ t, v: rand() });
  }
  return events;
}

const C = window.PALETTE;
const fmt = window.fmt;

// Determine acceptance for one event under one mechanism at time tNow.
// Returns: {state: "future"|"rejected"|"pending"|"accepted", matchTime}
function resolveEvent(mech, ev, p, tNow) {
  if (ev.t > tNow) return { state: "future" };
  let priceAtT;
  if (mech === "DA") priceAtT = p.rho * Math.exp(-p.delta * ev.t);
  else priceAtT = p.pbar;
  const accepted = ev.v >= priceAtT;
  if (!accepted) return { state: "rejected", price: priceAtT };
  if (mech === "FPb" && tNow < p.T) {
    return { state: "pending", matchTime: p.T, price: priceAtT };
  }
  return { state: "accepted", matchTime: ev.t, price: priceAtT };
}

function Lane({ mech, label, color, p, events, tNow, height }) {
  const W = 1280, H = height;
  const padL = 100, padR = 100, padT = 18, padB = 22;
  const x = v => padL + (v / p.T) * (W - padL - padR);
  const y = v => H - padB - v * (H - padT - padB);

  // Price function drawn behind
  let priceLineD = "";
  if (mech === "DA") {
    const N = 100;
    for (let i = 0; i <= N; i++) {
      const t = (i / N) * p.T;
      const v = p.rho * Math.exp(-p.delta * t);
      priceLineD += (i === 0 ? "M" : "L") + x(t).toFixed(1) + " " + y(v).toFixed(1);
    }
  } else {
    priceLineD = `M${x(0)} ${y(p.pbar)} L${x(p.T)} ${y(p.pbar)}`;
  }

  // Resolve all events at current time
  const resolved = events.map(ev => ({ ev, r: resolveEvent(mech, ev, p, tNow) }));
  const matched = resolved.filter(({ r }) => r.state === "accepted");
  const pending = resolved.filter(({ r }) => r.state === "pending");
  const rejected = resolved.filter(({ r }) => r.state === "rejected");

  // accept-region fill polygon (above price line, within [0,tNow])
  let acceptFill = "";
  if (mech === "DA") {
    const N = 80;
    const cutT = Math.min(tNow, p.T);
    acceptFill += `M${x(0)} ${y(1)}`;
    acceptFill += ` L${x(cutT)} ${y(1)}`;
    for (let i = N; i >= 0; i--) {
      const t = (i / N) * cutT;
      const v = p.rho * Math.exp(-p.delta * t);
      acceptFill += ` L${x(t).toFixed(1)} ${y(v).toFixed(1)}`;
    }
    acceptFill += " Z";
  } else {
    const cutT = Math.min(tNow, p.T);
    acceptFill = `M${x(0)} ${y(1)} L${x(cutT)} ${y(1)} L${x(cutT)} ${y(p.pbar)} L${x(0)} ${y(p.pbar)} Z`;
  }

  // Conditional avg price among accepted (or pending+accepted)
  const settledOrPending = mech === "FPb"
    ? matched.concat(pending)
    : matched;
  const avgPrice = settledOrPending.length
    ? settledOrPending.reduce((s, { r }) => s + r.price, 0) / settledOrPending.length
    : 0;
  const matchCount = mech === "FPb"
    ? (tNow >= p.T ? matched.length : pending.length)
    : matched.length;

  // Just-fired pulse: events within last 0.6 sim-min
  const pulseWindow = 0.6;
  const justFired = resolved.filter(({ ev }) => ev.t > tNow - pulseWindow && ev.t <= tNow);
  // Settle flash: when t crosses T, brief flash on lane
  const settled = mech === "FPb" && tNow >= p.T;

  return (
    <g>
      {/* lane background */}
      <rect x={padL} y={padT} width={W - padL - padR} height={H - padT - padB}
            fill="#FAFAFB" stroke="#E2E4E8" strokeWidth="0.6" rx="4" />
      {/* grid */}
      {[0.25, 0.5, 0.75].map(v => (
        <line key={v} x1={padL} x2={W - padR} y1={y(v)} y2={y(v)}
              stroke="#ECEDF0" strokeWidth="0.5" />
      ))}
      {/* accept region shading */}
      <path d={acceptFill} fill={color} opacity={settled ? 0.22 : 0.10} />
      {/* price line */}
      <path d={priceLineD} fill="none" stroke={color}
            strokeWidth="1.8" strokeDasharray={mech === "FPb" ? "5 3" : "none"}
            opacity="0.95" />

      {/* rejected dots — gray, small */}
      {rejected.map(({ ev }, i) => (
        <circle key={`r${i}`} cx={x(ev.t)} cy={y(ev.v)} r="1.6"
                fill="#A8ADB5" opacity="0.7" />
      ))}
      {/* pending dots (PP-batch only) — pulsing amber */}
      {pending.map(({ ev }, i) => (
        <g key={`p${i}`}>
          <circle cx={x(ev.t)} cy={y(ev.v)} r="3.5"
                  fill="none" stroke="#E6A23C" strokeWidth="1.2" opacity="0.8" />
          <circle cx={x(ev.t)} cy={y(ev.v)} r="2.2"
                  fill="#E6A23C" opacity="0.85" />
        </g>
      ))}
      {/* accepted dots */}
      {matched.map(({ ev }, i) => (
        <circle key={`m${i}`} cx={x(ev.t)} cy={y(ev.v)} r="3.2"
                fill={color} stroke="#FFFFFF" strokeWidth="0.9" opacity="0.98" />
      ))}
      {/* settle flash */}
      {settled && (
        <rect x={padL} y={padT} width={W - padL - padR} height={H - padT - padB}
              fill={color} opacity="0.05" pointerEvents="none" />
      )}
      {/* pulse for just-fired events */}
      {justFired.map(({ ev, r }, i) => {
        const age = (tNow - ev.t) / pulseWindow;
        const radius = 4 + age * 14;
        const opacity = (1 - age) * 0.7;
        const col = r.state === "accepted" ? color
                  : r.state === "pending" ? "#E6A23C"
                  : "#666";
        return (
          <circle key={`pulse${i}`} cx={x(ev.t)} cy={y(ev.v)}
                  r={radius} fill="none" stroke={col}
                  strokeWidth="1.2" opacity={opacity} pointerEvents="none" />
        );
      })}

      {/* now cursor */}
      <line x1={x(tNow)} x2={x(tNow)} y1={padT} y2={H - padB}
            stroke="#3A3733" strokeWidth="0.6" opacity="0.45" />

      {/* label band on left */}
      <g>
        <text x="10" y={padT + 14} fontSize="10.5"
              fontFamily="Inter, sans-serif" fontWeight="700"
              fill={color} letterSpacing="0.1em">{label.toUpperCase()}</text>
        <text x="10" y={padT + 27} fontSize="8.5"
              fontFamily="Inter, sans-serif" fill="#8A857B"
              letterSpacing="0.05em">
          {mech === "DA" ? "descending clock"
          : mech === "FPi" ? "immediate execution"
          : "batch at T"}
        </text>
        {/* live stats */}
        <text x="10" y={H - padB - 16} fontSize="8.5"
              fontFamily="Inter, sans-serif" fill="#8A857B"
              letterSpacing="0.08em">MATCHED</text>
        <text x="10" y={H - padB - 2} fontSize="18"
              fontFamily="EB Garamond, serif"
              fontWeight="600" fill="#131210">
          {matchCount}
        </text>
      </g>

      {/* right side stats */}
      <g>
        <text x={W - padR + 12} y={padT + 14} fontSize="8.5"
              fontFamily="Inter, sans-serif" fill="#8A857B"
              letterSpacing="0.08em">AVG PRICE</text>
        <text x={W - padR + 12} y={padT + 30} fontSize="14"
              fontFamily="JetBrains Mono, monospace"
              fontWeight="500" fill="#131210">
          {avgPrice > 0 ? avgPrice.toFixed(3) : "—"}
        </text>
        <text x={W - padR + 12} y={H - padB - 16} fontSize="8.5"
              fontFamily="Inter, sans-serif" fill="#8A857B"
              letterSpacing="0.08em">P @ NOW</text>
        <text x={W - padR + 12} y={H - padB - 2} fontSize="12"
              fontFamily="JetBrains Mono, monospace"
              fill={color}>
          {mech === "DA"
            ? (p.rho * Math.exp(-p.delta * tNow)).toFixed(3)
            : p.pbar.toFixed(3)}
        </text>
      </g>
    </g>
  );
}

function Theater({ p, M }) {
  const [tNow, setTNow] = useState(0);
  const [playing, setPlaying] = useState(false);
  const [speed, setSpeed] = useState(1.0);
  const [seed, setSeed] = useState(7);

  const events = useMemo(
    () => generateEvents(p, seed),
    [p.theta, p.A, p.beta, p.T, p.rho, p.delta, p.pbar, seed]
  );

  // Reset to t=0 when params change
  useEffect(() => { setTNow(0); }, [p.T, p.theta, p.delta, p.rho, p.pbar, p.A, p.beta, seed]);

  // Animation loop
  const rafRef = useRef();
  useEffect(() => {
    if (!playing) return;
    let last = performance.now();
    const tick = (now) => {
      const dt = (now - last) / 1000;
      last = now;
      setTNow(prev => {
        // Want full T to take ~12 seconds at speed=1
        const next = prev + (p.T / 12) * dt * speed;
        if (next >= p.T + 0.6) {
          setPlaying(false);
          return p.T;
        }
        return next;
      });
      rafRef.current = requestAnimationFrame(tick);
    };
    rafRef.current = requestAnimationFrame(tick);
    return () => cancelAnimationFrame(rafRef.current);
  }, [playing, speed, p.T]);

  const W = 1280;
  const laneH = 96;
  const totalH = laneH * 3 + 44;

  // Time axis ticks
  const tAxisY = totalH - 12;
  const tickT = (i) => (i / 6) * p.T;

  return (
    <div className="theater">
      <div className="theater-chrome">
        <div className="theater-title">
          <span className="dot blink" />
          <span>Session theater</span>
          <span className="theater-time">
            t = <strong>{tNow.toFixed(1)}</strong> / {p.T.toFixed(0)} min
          </span>
        </div>
        <div className="theater-controls">
          <button className="ctrl primary" onClick={() => {
            if (tNow >= p.T) setTNow(0);
            setPlaying(p => !p);
          }}>
            {playing ? "❚❚ Pause" : (tNow >= p.T ? "↻ Replay" : "▶ Play")}
          </button>
          <button className="ctrl" onClick={() => { setTNow(0); setPlaying(false); }}>
            Reset
          </button>
          <button className="ctrl" onClick={() => { setSeed(s => s + 1); setPlaying(true); }}>
            New realization
          </button>
          <div className="speed">
            <label>Speed</label>
            <input type="range" min="0.25" max="4" step="0.25"
                   value={speed} onChange={e => setSpeed(parseFloat(e.target.value))} />
            <span className="speed-val">{speed.toFixed(2)}×</span>
          </div>
        </div>
      </div>

      <div className="theater-stage">
        <svg viewBox={`0 0 ${W} ${totalH}`} width="100%" height="auto"
             preserveAspectRatio="xMidYMid meet">
          <g><Lane mech="DA"  label="Dutch auction"   color={C.DA}  p={p} events={events} tNow={tNow} height={laneH} /></g>
          <g transform={`translate(0,${laneH})`}><Lane mech="FPi" label="PP-immediate"   color={C.FPi} p={p} events={events} tNow={tNow} height={laneH} /></g>
          <g transform={`translate(0,${laneH * 2})`}><Lane mech="FPb" label="PP-batch"       color={C.FPb} p={p} events={events} tNow={tNow} height={laneH} /></g>

          {/* Time axis under all lanes */}
          <g>
            {Array.from({ length: 7 }, (_, i) => (
              <g key={i}>
                <text x={100 + (i / 6) * (W - 200)}
                      y={tAxisY}
                      fontSize="9.5"
                      fontFamily="Inter, sans-serif"
                      fill="#8A857B"
                      textAnchor="middle">
                  {tickT(i).toFixed(0)}m
                </text>
              </g>
            ))}
            <text x={W / 2} y={totalH - 1} fontSize="9"
                  fontFamily="Inter, sans-serif" fill="#A8A498"
                  textAnchor="middle" letterSpacing="0.08em">
              SESSION TIME · drag below to scrub
            </text>
          </g>
        </svg>
        {/* Scrubber overlay */}
        <input type="range" className="scrubber"
               min="0" max={p.T} step={p.T / 600}
               value={tNow}
               onChange={e => { setTNow(parseFloat(e.target.value)); setPlaying(false); }} />
      </div>

      <div className="theater-legend">
        <span><i className="swatch swatch-da" /> DA matched</span>
        <span><i className="swatch swatch-pp" /> PP-imm matched</span>
        <span><i className="swatch swatch-pending" /> PP-batch pending</span>
        <span><i className="swatch swatch-bat" /> PP-batch settled</span>
        <span><i className="swatch swatch-rej" /> rejected</span>
        <span className="legend-explainer">
          Each dot is a contact event at <em>(t, v)</em>. Above the price line → accept.
        </span>
      </div>
    </div>
  );
}

window.Theater = Theater;
