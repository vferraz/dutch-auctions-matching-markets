// panels-v3.jsx — redesigned visualization components for v3.
// Adds the 4-quadrant case classifier + plain-English explainer,
// rebuilds the 6 analytic panels without internal legends, and
// supplies a grouped-bar equilibrium comparison, scenario cards,
// and a tidy parameters cluster.

const C = {
  DA:    "#2B6CB0",
  FPi:   "#C05621",
  FPb:   "#9B2C2C",
  ink:   "#1A1A1A",
  ink2:  "#36322C",
  muted: "#6B6660",
  rule:  "#D8D2C2",
  grid:  "#EBE6D8",
  faint: "#C9C2B4",
  cream: "#FAF8F0",
  blueSoft: "#E6EEF7",
  orangeSoft: "#FBEEDC",
};

// ── helpers ──────────────────────────────────────────────────────────
function makeScale(d0, d1, r0, r1) {
  const m = (r1 - r0) / (d1 - d0 || 1);
  const f = v => r0 + (v - d0) * m;
  f.inv = u => d0 + (u - r0) / m;
  f.domain = [d0, d1];
  f.range = [r0, r1];
  return f;
}
function niceTicks(d0, d1, n = 4) {
  const span = d1 - d0;
  if (span <= 0) return [d0];
  const step0 = Math.pow(10, Math.floor(Math.log10(span / n)));
  const err = (n * step0) / span;
  let step = step0;
  if (err <= 0.15) step *= 10;
  else if (err <= 0.35) step *= 5;
  else if (err <= 0.75) step *= 2;
  const t0 = Math.ceil(d0 / step) * step;
  const out = [];
  for (let v = t0; v <= d1 + 1e-9; v += step) {
    out.push(Math.abs(v) < 1e-12 ? 0 : v);
  }
  return out;
}
function fmt(v, d = 2) {
  if (!isFinite(v)) return "∞";
  if (Math.abs(v) >= 1000) return v.toFixed(0);
  if (Math.abs(v) < 0.01 && v !== 0) return v.toExponential(1);
  return v.toFixed(d);
}
function linePath(xs, ys, x, y) {
  let d = "";
  for (let i = 0; i < xs.length; i++) {
    const xi = x(xs[i]), yi = y(ys[i]);
    if (!isFinite(xi) || !isFinite(yi)) continue;
    d += (d ? "L" : "M") + xi.toFixed(2) + " " + yi.toFixed(2);
  }
  return d;
}

// Minimal axes — no inline legend
function Axes({ x, y, W, H, padL, padR, padT, padB, xLabel, yLabel, xTicks, yTicks }) {
  const xt = xTicks || niceTicks(x.domain[0], x.domain[1], 4);
  const yt = yTicks || niceTicks(y.domain[0], y.domain[1], 4);
  return (
    <g>
      {yt.map((v, i) => (
        <line key={`gy${i}`} x1={padL} x2={W - padR} y1={y(v)} y2={y(v)}
              stroke={C.grid} strokeWidth="0.5" />
      ))}
      <line x1={padL} x2={W - padR} y1={H - padB} y2={H - padB}
            stroke={C.rule} strokeWidth="0.7" />
      <line x1={padL} x2={padL} y1={padT} y2={H - padB}
            stroke={C.rule} strokeWidth="0.7" />
      {xt.map((v, i) => (
        <g key={`tx${i}`}>
          <line x1={x(v)} x2={x(v)} y1={H - padB} y2={H - padB + 4}
                stroke={C.rule} strokeWidth="0.6" />
          <text x={x(v)} y={H - padB + 14} fontSize="10" fill={C.muted}
                textAnchor="middle" fontFamily="Inter, sans-serif">
            {fmt(v, 2)}
          </text>
        </g>
      ))}
      {yt.map((v, i) => (
        <g key={`ty${i}`}>
          <line x1={padL - 4} x2={padL} y1={y(v)} y2={y(v)}
                stroke={C.rule} strokeWidth="0.6" />
          <text x={padL - 6} y={y(v) + 3} fontSize="10" fill={C.muted}
                textAnchor="end" fontFamily="Inter, sans-serif">
            {fmt(v, 2)}
          </text>
        </g>
      ))}
      {xLabel && (
        <text x={(padL + W - padR) / 2} y={H - 6} fontSize="10.5" fill={C.ink2}
              textAnchor="middle"
              fontFamily="Inter, sans-serif">{xLabel}</text>
      )}
      {yLabel && (
        <text x={14} y={(padT + H - padB) / 2} fontSize="10.5" fill={C.ink2}
              textAnchor="middle"
              transform={`rotate(-90, 14, ${(padT + H - padB) / 2})`}
              fontFamily="Inter, sans-serif">{yLabel}</text>
      )}
    </g>
  );
}

function PanelFrame({ title, subtitle, w = 500, h = 280, children }) {
  return (
    <figure className="panel-v3">
      <header>
        <h4>{title}</h4>
        {subtitle && <p className="sub">{subtitle}</p>}
      </header>
      <svg viewBox={`0 0 ${w} ${h}`} width="100%" height="auto"
           preserveAspectRatio="xMidYMid meet">
        {children}
      </svg>
    </figure>
  );
}

// ── CASE CLASSIFIER (4-quadrant diagram) ─────────────────────────────
//
//  Plots the (earnings gap, timing gap) point in the plane.
//  The four cases are the four quadrants. λ controls the slope of the
//  decision line; DA wins above the line (in dpi-positive / dtau-positive
//  rotational sense).
//
//  Margin = -dpi + λ·dtau ≥ 0 → DA wins.
function CaseClassifier({ p, M }) {
  const d = M.dominanceCase(p.theta, p.delta, p.rho, p.pbar, p.T, p.alpha, p.A, p.beta);

  // Adaptive plot ranges — always include the current point with some margin.
  const xR = Math.max(0.16, Math.abs(d.dpi) * 1.45, 0.25);
  const yR = Math.max(p.T * 0.4, Math.abs(d.dtau) * 1.45, 5);

  const W = 460, H = 340;
  const padL = 60, padR = 16, padT = 30, padB = 36;
  const x = v => padL + ((v + xR) / (2 * xR)) * (W - padL - padR);
  const y = v => H - padB - ((v + yR) / (2 * yR)) * (H - padT - padB);

  // Plot bounds in data coords
  const x0 = -xR, x1 = +xR, y0 = -yR, y1 = +yR;

  // Decision line: dtau = dpi / λ   (DA wins iff dtau >= dpi/λ)
  // Slope is 1/λ in (dpi, dtau) space.
  const slope = p.lam > 1e-9 ? 1 / p.lam : 1e12;
  // Clip endpoints to plot
  function clipLineToRect(slope) {
    // line: y = slope * x, passes through origin
    const pts = [];
    // Intersections with x = x0, x = x1, y = y0, y = y1
    const tryAdd = (px, py) => {
      if (px >= x0 - 1e-9 && px <= x1 + 1e-9 && py >= y0 - 1e-9 && py <= y1 + 1e-9) {
        pts.push([px, py]);
      }
    };
    tryAdd(x0, slope * x0);
    tryAdd(x1, slope * x1);
    if (slope !== 0) {
      tryAdd(y0 / slope, y0);
      tryAdd(y1 / slope, y1);
    }
    return pts.slice(0, 2);
  }
  const linePts = clipLineToRect(slope);

  // DA-winning region polygon: { (dpi, dtau) : dtau >= dpi/λ } intersected with rect
  // Build polygon by walking rect corners and adding line-crossing points.
  function daRegionPolygon(slope) {
    // Check the four corners of the rectangle
    const corners = [
      [x0, y0], [x1, y0], [x1, y1], [x0, y1],
    ];
    // function: f(p) = dtau - dpi/slope ... wait, define inWin(p) = (p.y >= slope*p.x)
    const inWin = (px, py) => py >= slope * px - 1e-9;
    const out = [];
    for (let i = 0; i < 4; i++) {
      const a = corners[i], b = corners[(i + 1) % 4];
      const inA = inWin(a[0], a[1]), inB = inWin(b[0], b[1]);
      if (inA) out.push(a);
      if (inA !== inB) {
        // find crossing along edge from a to b
        // parametrize p = a + t*(b-a), solve py - slope*px = 0
        const px = b[0] - a[0], py = b[1] - a[1];
        const denom = py - slope * px;
        if (Math.abs(denom) > 1e-12) {
          const t = (slope * a[0] - a[1]) / denom;
          if (t >= -1e-9 && t <= 1 + 1e-9) {
            out.push([a[0] + t * px, a[1] + t * py]);
          }
        }
      }
    }
    return out;
  }
  const daPoly = daRegionPolygon(slope);
  const polyD = daPoly.length
    ? "M" + daPoly.map(p => `${x(p[0]).toFixed(2)} ${y(p[1]).toFixed(2)}`).join(" L") + " Z"
    : "";

  // Quadrant labels — positioned in mid-quadrant
  const quadLabels = [
    { x: -xR * 0.5, y:  yR * 0.6, case: 1, title: "Case 1", sub: "DA dominates" },
    { x:  xR * 0.5, y:  yR * 0.6, case: 2, title: "Case 2", sub: "Genuine tradeoff" },
    { x: -xR * 0.5, y: -yR * 0.6, case: 4, title: "Case 4", sub: "Reversed tradeoff" },
    { x:  xR * 0.5, y: -yR * 0.6, case: 3, title: "Case 3", sub: "PP dominates" },
  ];

  // current point clamped to view
  const ptX = Math.max(x0 * 0.99, Math.min(x1 * 0.99, d.dpi));
  const ptY = Math.max(y0 * 0.99, Math.min(y1 * 0.99, d.dtau));

  return (
    <svg viewBox={`0 0 ${W} ${H}`} width="100%" height="auto"
         preserveAspectRatio="xMidYMid meet">
      {/* DA-winning region fill */}
      {polyD && <path d={polyD} fill={C.DA} opacity="0.07" />}
      {/* main axes through origin */}
      <line x1={padL} x2={W - padR} y1={y(0)} y2={y(0)}
            stroke={C.rule} strokeWidth="0.7" />
      <line x1={x(0)} x2={x(0)} y1={padT} y2={H - padB}
            stroke={C.rule} strokeWidth="0.7" />
      {/* decision line */}
      {linePts.length === 2 && (
        <line x1={x(linePts[0][0])} y1={y(linePts[0][1])}
              x2={x(linePts[1][0])} y2={y(linePts[1][1])}
              stroke={C.ink} strokeWidth="1.4" strokeDasharray="5 4" />
      )}
      {/* axis labels */}
      <text x={W - padR - 2} y={y(0) - 6} fontSize="10" fill={C.muted}
            textAnchor="end" fontFamily="Inter, sans-serif" fontStyle="italic">
        earnings gap → q<tspan baselineShift="sub">PP</tspan>π − q<tspan baselineShift="sub">DA</tspan>π
      </text>
      <text x={x(0) + 6} y={padT - 4} fontSize="10" fill={C.muted}
            textAnchor="start" fontFamily="Inter, sans-serif" fontStyle="italic">
        timing gap ↑ τ<tspan baselineShift="sub">PP</tspan> − τ<tspan baselineShift="sub">DA</tspan>
      </text>
      {/* tick labels */}
      <text x={x(xR) - 4} y={y(0) + 14} fontSize="9" fill={C.muted}
            textAnchor="end" fontFamily="Inter, sans-serif">PP earns more →</text>
      <text x={x(-xR) + 4} y={y(0) + 14} fontSize="9" fill={C.muted}
            textAnchor="start" fontFamily="Inter, sans-serif">← DA earns more</text>
      <text x={x(0) + 6} y={y(yR) + 14} fontSize="9" fill={C.muted}
            textAnchor="start" fontFamily="Inter, sans-serif">DA faster</text>
      <text x={x(0) + 6} y={y(-yR) - 6} fontSize="9" fill={C.muted}
            textAnchor="start" fontFamily="Inter, sans-serif">DA slower</text>

      {/* quadrant labels */}
      {quadLabels.map((q, i) => (
        <g key={i} opacity={d.kase === q.case ? 1 : 0.45}>
          <text x={x(q.x)} y={y(q.y) - 6} fontSize="11" fill={C.ink2}
                textAnchor="middle" fontFamily="Inter, sans-serif"
                fontWeight="700">
            {q.title}
          </text>
          <text x={x(q.x)} y={y(q.y) + 8} fontSize="10" fill={C.muted}
                textAnchor="middle" fontFamily="Inter, sans-serif"
                fontStyle="italic">
            {q.sub}
          </text>
        </g>
      ))}

      {/* current point */}
      <line x1={x(ptX)} x2={x(0)} y1={y(ptY)} y2={y(ptY)}
            stroke={C.ink} strokeWidth="0.5" strokeDasharray="1 2" opacity="0.4" />
      <line x1={x(ptX)} x2={x(ptX)} y1={y(ptY)} y2={y(0)}
            stroke={C.ink} strokeWidth="0.5" strokeDasharray="1 2" opacity="0.4" />
      <circle cx={x(ptX)} cy={y(ptY)} r="6" fill={C.ink} stroke="#fff" strokeWidth="2" />

      {/* decision line annotation */}
      <text x={W - padR - 4} y={padT + 14} fontSize="10" fill={C.muted}
            textAnchor="end" fontFamily="Inter, sans-serif" fontStyle="italic">
        decision line · slope 1/λ
      </text>
    </svg>
  );
}

// Plain-English per-case story
function CaseExplainer({ p, M }) {
  const d = M.dominanceCase(p.theta, p.delta, p.rho, p.pbar, p.T, p.alpha, p.A, p.beta);
  const localDAwins =
    d.kase === 1 ? true :
    d.kase === 2 ? p.lam >= d.thr :
    d.kase === 3 ? false :
    p.lam <= d.thr;

  // story content per case
  const stories = {
    1: {
      title: "DA dominates",
      tag: "DA earns more AND contracts faster",
      story: <>The clock genuinely beats the post: Dutch trades occur at higher prices <em>and</em> happen sooner. No level of waiting cost flips this verdict — every driver, patient or impatient, prefers DA. Entry follows.</>,
      rule: <>DA wins locally for <strong>every</strong> λ ≥ 0.</>,
    },
    2: {
      title: "Genuine tradeoff",
      tag: "PP earns more, DA contracts faster",
      story: <>Posted price clears at a higher per-trade revenue, but DA gets matches through quicker. Drivers face a real choice: take the price premium and wait, or take the speed and skip the premium. Only drivers with a high enough waiting cost (λ ≥ λ★) trade time for money and pick DA.</>,
      rule: <>DA wins locally iff <strong className="mono">λ ≥ λ★ = {fmt(d.thr, 3)}</strong>. Current λ = {fmt(p.lam, 3)} → <strong>{p.lam >= d.thr ? "DA wins" : "PP wins"}</strong>.</>,
    },
    3: {
      title: "PP dominates",
      tag: "PP earns more AND contracts faster",
      story: <>The posted price beats Dutch on both axes — higher take per match and lower waiting time. The clock has nothing to offer marginal drivers in this regime; raising waiting costs doesn't help.</>,
      rule: <>Posted price wins locally for <strong>every</strong> λ &gt; 0.</>,
    },
    4: {
      title: "Reversed tradeoff",
      tag: "DA earns more, PP contracts faster",
      story: <>The descending clock starts above the posted price, so early DA accepts hit at a premium and the average DA payment exceeds p̄. But the high opening clock suppresses early acceptance, so DA is actually slower. Only patient drivers (λ ≤ λ★★) value the price premium enough to absorb the wait.</>,
      rule: <>DA wins locally iff <strong className="mono">λ ≤ λ★★ = {fmt(d.thr, 3)}</strong>. Current λ = {fmt(p.lam, 3)} → <strong>{p.lam <= d.thr ? "DA wins" : "PP wins"}</strong>.</>,
    },
  };
  const s = stories[d.kase];

  return (
    <div className="case-explainer">
      <div className="case-meta">
        <span className="case-num">Case {d.kase}</span>
        <span className={"case-pill " + (localDAwins ? "win-da" : "win-pp")}>
          {localDAwins ? "▲ DA wins" : "▼ PP wins"} <span className="muted">at current λ</span>
        </span>
      </div>
      <h3 className="case-title">{s.title}</h3>
      <p className="case-tag">{s.tag}</p>
      <p className="case-story">{s.story}</p>
      <p className="case-rule">{s.rule}</p>
    </div>
  );
}

// ── PANEL 1 — Price paths ────────────────────────────────────────────
function PricePathPanel({ p, M }) {
  const W = 500, H = 260, padL = 50, padR = 20, padT = 18, padB = 36;
  const T = p.T;
  const x = makeScale(0, T, padL, W - padR);
  const y = makeScale(0, 1, H - padB, padT);
  const N = 200;
  const ts = Array.from({ length: N + 1 }, (_, i) => (i / N) * T);
  const pDA = ts.map(t => p.rho * Math.exp(-p.delta * t));

  return (
    <PanelFrame
      title="Price paths"
      subtitle="What each mechanism charges the rider as time advances"
      w={W} h={H}
    >
      <Axes x={x} y={y} W={W} H={H} padL={padL} padR={padR} padT={padT} padB={padB}
            xLabel="time t (min)" yLabel="price / v̄" />
      {/* shaded acceptance region under DA curve (above pbar line) */}
      <line x1={padL} x2={W - padR} y1={y(p.pbar)} y2={y(p.pbar)}
            stroke={C.FPi} strokeWidth="1.8" strokeDasharray="5 3" />
      <path d={linePath(ts, pDA, x, y)} fill="none" stroke={C.DA} strokeWidth="2" />
      {/* end-of-clock marker for batch */}
      <circle cx={x(T)} cy={y(p.rho * Math.exp(-p.delta * T))} r="3" fill={C.DA} />
      {/* p0 marker on DA */}
      <circle cx={x(0)} cy={y(p.rho)} r="3" fill={C.DA} />
    </PanelFrame>
  );
}

// ── PANEL 2 — Cumulative match probability ───────────────────────────
function CumMatchPanel({ p, M }) {
  const W = 500, H = 260, padL = 50, padR = 20, padT = 18, padB = 36;
  const T = p.T;
  const theta = p.theta;
  const x = makeScale(0, T, padL, W - padR);
  const y = makeScale(0, 1, H - padB, padT);
  const N = 200;
  const ts = Array.from({ length: N + 1 }, (_, i) => (i / N) * T);
  const cumDA = ts.map(t => 1 - M.S_DA(t, theta, p.delta, p.rho, p.A, p.beta));
  const eta = M.etaFP(theta, p.pbar, p.A, p.beta);
  const cumPP = ts.map(t => 1 - Math.exp(-eta * t));
  const qFP = cumPP[cumPP.length - 1];

  return (
    <PanelFrame
      title="Cumulative match probability"
      subtitle="Fraction of drivers matched by time t — PP-batch realizes only at T"
      w={W} h={H}
    >
      <Axes x={x} y={y} W={W} H={H} padL={padL} padR={padR} padT={padT} padB={padB}
            xLabel="time t (min)" yLabel="Pr(matched by t)" />
      <path d={linePath(ts, cumDA, x, y)} fill="none" stroke={C.DA} strokeWidth="2" />
      <path d={linePath(ts, cumPP, x, y)} fill="none" stroke={C.FPi}
            strokeWidth="1.8" strokeDasharray="5 3" />
      {/* PP-batch: dotted along 0 then jumps to qFP at T */}
      <line x1={padL} x2={x(T)} y1={y(0)} y2={y(0)} stroke={C.FPb}
            strokeWidth="1.5" strokeDasharray="2 3" />
      <line x1={x(T)} x2={x(T)} y1={y(0)} y2={y(qFP)} stroke={C.FPb}
            strokeWidth="1.6" />
      <circle cx={x(T)} cy={y(qFP)} r="4" fill={C.FPb} stroke="#fff" strokeWidth="1.2" />
    </PanelFrame>
  );
}

// ── PANEL 3 — Margin (decomposition) vs λ ────────────────────────────
// FIXED SIGN: total = -dpi + λ·dtau
function MarginPanel({ p, M }) {
  const W = 500, H = 260, padL = 55, padR = 20, padT = 18, padB = 36;
  const theta = p.theta;
  const d = M.dominanceCase(theta, p.delta, p.rho, p.pbar, p.T, p.alpha, p.A, p.beta);
  const earn = -d.dpi;     // DA earnings advantage (positive = DA better)
  const tslope = d.dtau;   // slope vs λ for DA-favoring margin
  const lamMax = 0.16;
  const lams = Array.from({ length: 161 }, (_, i) => (i / 160) * lamMax);
  const earnArr = lams.map(_ => earn);
  const timeArr = lams.map(l => l * tslope);
  const total = lams.map(l => earn + l * tslope);

  let ymin = Math.min(0, ...total, ...earnArr, ...timeArr);
  let ymax = Math.max(0, ...total, ...earnArr, ...timeArr);
  const padY = (ymax - ymin) * 0.15 || 0.02;
  ymin -= padY; ymax += padY;
  const x = makeScale(0, lamMax, padL, W - padR);
  const y = makeScale(ymin, ymax, H - padB, padT);

  // Shaded DA-winning region in λ
  let shadeLo = null, shadeHi = null;
  if (d.kase === 1) { shadeLo = 0; shadeHi = lamMax; }
  else if (d.kase === 2 && d.thr < lamMax) { shadeLo = d.thr; shadeHi = lamMax; }
  else if (d.kase === 4 && d.thr < lamMax) { shadeLo = 0; shadeHi = d.thr; }

  return (
    <PanelFrame
      title={<>DA margin vs waiting cost <em>λ</em></>}
      subtitle={<>Earnings + λ·timing as a function of <em>λ</em>. Shaded = DA wins.</>}
      w={W} h={H}
    >
      <Axes x={x} y={y} W={W} H={H} padL={padL} padR={padR} padT={padT} padB={padB}
            xLabel="driver waiting cost λ" yLabel="c̄ DA − c̄ PP" />
      {shadeLo != null && (
        <rect x={x(shadeLo)} y={padT}
              width={x(shadeHi) - x(shadeLo)} height={H - padB - padT}
              fill={C.DA} opacity="0.07" />
      )}
      <line x1={padL} x2={W - padR} y1={y(0)} y2={y(0)} stroke={C.muted}
            strokeWidth="0.6" />
      {/* earnings component (flat) */}
      <path d={linePath(lams, earnArr, x, y)} fill="none" stroke={C.DA}
            strokeWidth="1.3" strokeDasharray="2 3" opacity="0.7" />
      {/* timing component (slope) */}
      <path d={linePath(lams, timeArr, x, y)} fill="none" stroke={C.FPi}
            strokeWidth="1.3" strokeDasharray="4 3" opacity="0.7" />
      {/* total */}
      <path d={linePath(lams, total, x, y)} fill="none" stroke={C.ink}
            strokeWidth="2.2" />
      {/* threshold line */}
      {(d.kase === 2 || d.kase === 4) && isFinite(d.thr) && d.thr < lamMax && (
        <line x1={x(d.thr)} x2={x(d.thr)} y1={padT} y2={H - padB}
              stroke={C.muted} strokeWidth="0.7" strokeDasharray="3 3" />
      )}
      {/* current λ */}
      <line x1={x(p.lam)} x2={x(p.lam)} y1={padT} y2={H - padB}
            stroke={C.ink} strokeWidth="0.6" strokeDasharray="1 2" opacity="0.6" />
      <circle cx={x(p.lam)} cy={y(earn + p.lam * tslope)} r="4"
              fill={C.ink} stroke="#fff" strokeWidth="1.5" />
    </PanelFrame>
  );
}

// ── PANEL 4 — Driver entry fixed point ───────────────────────────────
function EntryFixedPanel({ p, M }) {
  const W = 500, H = 260, padL = 50, padR = 20, padT = 18, padB = 36;
  const x = makeScale(0, p.Dbar, padL, W - padR);
  const y = makeScale(0, p.Dbar, H - padB, padT);
  const N = 80;
  const Ds = Array.from({ length: N + 1 }, (_, i) => (i / N) * p.Dbar);
  const phiDA  = Ds.map(D => M.phiM(D, "DA",  p.R, p.lam, p.Dbar, p.cmax, p));
  const phiFPi = Ds.map(D => M.phiM(D, "FPi", p.R, p.lam, p.Dbar, p.cmax, p));
  const phiFPb = Ds.map(D => M.phiM(D, "FPb", p.R, p.lam, p.Dbar, p.cmax, p));
  const Dda  = M.solveEntry("DA",  p.R, p.lam, p.Dbar, p.cmax, p);
  const Dfpi = M.solveEntry("FPi", p.R, p.lam, p.Dbar, p.cmax, p);
  const Dfpb = M.solveEntry("FPb", p.R, p.lam, p.Dbar, p.cmax, p);

  return (
    <PanelFrame
      title="Driver entry fixed point"
      subtitle="Equilibrium driver mass is where Φₘ(D) crosses the 45° line"
      w={W} h={H}
    >
      <Axes x={x} y={y} W={W} H={H} padL={padL} padR={padR} padT={padT} padB={padB}
            xLabel="driver mass D" yLabel="Φₘ(D)" />
      <line x1={x(0)} y1={y(0)} x2={x(p.Dbar)} y2={y(p.Dbar)}
            stroke={C.muted} strokeWidth="0.6" strokeDasharray="2 3" />
      <path d={linePath(Ds, phiFPb, x, y)} fill="none" stroke={C.FPb}
            strokeWidth="1.5" strokeDasharray="2 2" />
      <path d={linePath(Ds, phiFPi, x, y)} fill="none" stroke={C.FPi}
            strokeWidth="1.7" strokeDasharray="5 3" />
      <path d={linePath(Ds, phiDA, x, y)} fill="none" stroke={C.DA}
            strokeWidth="2" />
      {Dda > 0 && (
        <g>
          <line x1={x(Dda)} x2={x(Dda)} y1={y(0)} y2={y(Dda)}
                stroke={C.DA} strokeWidth="0.6" strokeDasharray="1 2" opacity="0.7" />
          <circle cx={x(Dda)} cy={y(Dda)} r="4.5" fill={C.DA} stroke="#fff" strokeWidth="1.5" />
        </g>
      )}
      {Dfpi > 0 && (
        <circle cx={x(Dfpi)} cy={y(Dfpi)} r="4.5" fill={C.FPi}
                stroke="#fff" strokeWidth="1.5" />
      )}
      {Dfpb > 0 && (
        <circle cx={x(Dfpb)} cy={y(Dfpb)} r="4.5" fill={C.FPb}
                stroke="#fff" strokeWidth="1.5" />
      )}
    </PanelFrame>
  );
}

// ── PANEL 5 — Two-sided closure ──────────────────────────────────────
function TwoSidedPanel({ p, M }) {
  const W = 500, H = 260, padL = 50, padR = 20, padT = 18, padB = 36;
  const x = makeScale(0, p.Dbar, padL, W - padR);
  const y = makeScale(0, p.R,    H - padB, padT);
  const N = 32;
  const Rgrid = Array.from({ length: N + 1 }, (_, i) => Math.max(1, (i / N) * p.R));
  const Dgrid = Array.from({ length: N + 1 }, (_, i) => Math.max(1, (i / N) * p.Dbar));
  const D_resp_DA  = Rgrid.map(Rv => M.solveEntry("DA",  Rv, p.lam, p.Dbar, p.cmax, p));
  const D_resp_FPi = Rgrid.map(Rv => M.solveEntry("FPi", Rv, p.lam, p.Dbar, p.cmax, p));
  const R_resp_DA  = Dgrid.map(Dv => M.solveRiderResponse(Dv, "DA",  p.R, p));
  const R_resp_FPi = Dgrid.map(Dv => M.solveRiderResponse(Dv, "FPi", p.R, p));
  const eqDA  = M.solveTwoSided("DA",  p, [44, 45]);
  const eqFPi = M.solveTwoSided("FPi", p, [46, 62]);

  function curve(xs, ys) {
    let d = "";
    for (let i = 0; i < xs.length; i++) {
      const xi = x(xs[i]), yi = y(ys[i]);
      if (!isFinite(xi) || !isFinite(yi)) continue;
      d += (d ? "L" : "M") + xi.toFixed(2) + " " + yi.toFixed(2);
    }
    return d;
  }
  return (
    <PanelFrame
      title="Two-sided closure"
      subtitle="Driver and rider best-responses; intersection = joint equilibrium"
      w={W} h={H}
    >
      <Axes x={x} y={y} W={W} H={H} padL={padL} padR={padR} padT={padT} padB={padB}
            xLabel="driver mass D" yLabel="rider mass R" />
      <path d={curve(D_resp_DA, Rgrid)}  fill="none" stroke={C.DA}  strokeWidth="2" />
      <path d={curve(Dgrid, R_resp_DA)}  fill="none" stroke={C.DA}  strokeWidth="1.4" strokeDasharray="3 3" />
      <path d={curve(D_resp_FPi, Rgrid)} fill="none" stroke={C.FPi} strokeWidth="2" />
      <path d={curve(Dgrid, R_resp_FPi)} fill="none" stroke={C.FPi} strokeWidth="1.4" strokeDasharray="3 3" />
      <circle cx={x(eqDA[0])}  cy={y(eqDA[1])}  r="5" fill={C.DA}  stroke="#fff" strokeWidth="1.5" />
      <circle cx={x(eqFPi[0])} cy={y(eqFPi[1])} r="5" fill={C.FPi} stroke="#fff" strokeWidth="1.5" />
    </PanelFrame>
  );
}

// ── PANEL 6 — Revenue ratio vs ρ ─────────────────────────────────────
function OutcomesRhoPanel({ p, M }) {
  const W = 500, H = 260, padL = 55, padR = 20, padT = 18, padB = 36;
  const rhos = Array.from({ length: 36 }, (_, i) => 0.35 + (i / 35) * 0.60);
  const ratio = rhos.map(rho => {
    const pp = Object.assign({}, p, { rho });
    const eq = M.computeEquilibrium(pp);
    return eq.FPi.Rev > 1e-9 ? eq.DA.Rev / eq.FPi.Rev : 1;
  });
  const ymin = Math.min(0.85, ...ratio);
  const ymax = Math.max(1.15, ...ratio);
  const x = makeScale(0.35, 0.95, padL, W - padR);
  const y = makeScale(ymin, ymax, H - padB, padT);

  // shaded DA-winning area (ratio >= 1)
  let shadeD = "M";
  for (let i = 0; i < rhos.length; i++) {
    const top = Math.max(1, ratio[i]);
    shadeD += (i === 0 ? "" : "L") + x(rhos[i]).toFixed(2) + " " + y(top).toFixed(2) + " ";
  }
  for (let i = rhos.length - 1; i >= 0; i--) {
    shadeD += "L" + x(rhos[i]).toFixed(2) + " " + y(1).toFixed(2) + " ";
  }
  shadeD += "Z";

  const ppCur = M.computeEquilibrium(p);
  const curRatio = ppCur.FPi.Rev > 1e-9 ? ppCur.DA.Rev / ppCur.FPi.Rev : 1;

  return (
    <PanelFrame
      title="Revenue ratio vs starting price"
      subtitle={<>Sensitivity of Rev<sub>DA</sub>/Rev<sub>PP</sub> as ρ = p₀ / v̄ varies</>}
      w={W} h={H}
    >
      <Axes x={x} y={y} W={W} H={H} padL={padL} padR={padR} padT={padT} padB={padB}
            xLabel="ρ = p₀ / v̄" yLabel="Rev DA / Rev PP" />
      <path d={shadeD} fill={C.DA} opacity="0.07" />
      <line x1={padL} x2={W - padR} y1={y(1)} y2={y(1)} stroke={C.muted}
            strokeWidth="0.7" strokeDasharray="3 3" />
      <path d={linePath(rhos, ratio, x, y)} fill="none" stroke={C.ink}
            strokeWidth="2.2" />
      <line x1={x(p.rho)} x2={x(p.rho)} y1={padT} y2={H - padB}
            stroke={C.ink} strokeWidth="0.6" strokeDasharray="1 2" opacity="0.5" />
      <circle cx={x(p.rho)} cy={y(curRatio)} r="5" fill={C.ink}
              stroke="#fff" strokeWidth="1.5" />
    </PanelFrame>
  );
}

// ── Shared legend card ───────────────────────────────────────────────
function ChartLegend() {
  const items = [
    { color: C.DA, label: "DA — Dutch clock (descending price)" },
    { color: C.FPi, label: "PP-imm — posted price, executes immediately", dash: true },
    { color: C.FPb, label: "PP-batch — posted price, executes at T", dot: true },
  ];
  return (
    <div className="chart-legend">
      <div className="legend-rows">
        {items.map((it, i) => (
          <div key={i} className="legend-row">
            <svg width="36" height="10" viewBox="0 0 36 10">
              <line x1="0" x2="36" y1="5" y2="5" stroke={it.color}
                    strokeWidth="2"
                    strokeDasharray={it.dash ? "5 3" : (it.dot ? "2 3" : "none")} />
            </svg>
            <span>{it.label}</span>
          </div>
        ))}
      </div>
      <p className="legend-note">
        Solid line = DA. Dashed = PP-immediate. Dotted = PP-batch (often coincides with PP-imm
        on volume/price; differs on <em>timing</em>).
      </p>
    </div>
  );
}

// ── Equilibrium as grouped horizontal bars ───────────────────────────
function EquilibriumBars({ p, M }) {
  const eq = M.computeEquilibrium(p);
  const metrics = [
    { key: "Dstar", label: "Driver entry D★",      d: 1, hint: "Equilibrium driver mass at the entry fixed point." },
    { key: "m",     label: "Match volume m",       d: 1, hint: "D★ · q = total trades per session." },
    { key: "Rev",   label: "Platform revenue",     d: 2, hint: "α · m · p̄ — commission times volume times trade price." },
    { key: "W",     label: "Welfare W",            d: 1, hint: "m·s − λ·D·τ − κ·R·τR. Surplus net of waiting costs." },
    { key: "tau",   label: "Driver wait τ (min)",  d: 2, invert: true, hint: "Expected time-to-contract per driver. Shorter is better." },
    { key: "tauR",  label: "Rider wait τR (min)",  d: 2, invert: true, hint: "Expected time-to-contract per rider." },
  ];
  const mechs = [
    { key: "DA",  label: "DA",       color: C.DA },
    { key: "FPi", label: "PP-imm",   color: C.FPi },
    { key: "FPb", label: "PP-batch", color: C.FPb },
  ];
  return (
    <div className="eq-bars">
      {metrics.map(m => {
        const vals = mechs.map(mk => eq[mk.key][m.key]);
        const absMax = Math.max(...vals.map(Math.abs), 0.001);
        const bestVal = m.invert ? Math.min(...vals) : Math.max(...vals);
        return (
          <div key={m.key} className="eq-row">
            <div className="eq-row-head">
              <span className="eq-row-label">{m.label}</span>
              <span className="eq-row-hint">{m.hint}</span>
            </div>
            <div className="eq-row-bars">
              {mechs.map((mk, i) => {
                const v = vals[i];
                const isBest = v === bestVal && Math.abs(v) > 1e-9;
                const pct = Math.max(0, (Math.abs(v) / absMax) * 100);
                return (
                  <div key={mk.key} className={"eq-bar" + (isBest ? " best" : "")}>
                    <div className="eq-bar-mech" style={{ color: mk.color }}>{mk.label}</div>
                    <div className="eq-bar-track">
                      <div className="eq-bar-fill"
                           style={{ width: pct + "%", background: mk.color }} />
                    </div>
                    <div className="eq-bar-val">{fmt(v, m.d)}{isBest && <span className="best-star">★</span>}</div>
                  </div>
                );
              })}
            </div>
          </div>
        );
      })}
    </div>
  );
}

// ── Scenario cards (prominent, with always-visible descriptions) ─────
function ScenarioCards({ presets, descriptions, active, onSelect }) {
  return (
    <div className="scenario-cards">
      {Object.keys(presets).map(name => (
        <button key={name}
                className={"scenario-card" + (active === name ? " active" : "")}
                onClick={() => onSelect(name)}>
          <div className="scenario-head">
            <span className="scenario-name">{name}</span>
            {active === name && <span className="scenario-active">●</span>}
          </div>
          <p className="scenario-desc">{descriptions[name]}</p>
        </button>
      ))}
    </div>
  );
}

// ── Compact parameter cluster (demoted) ──────────────────────────────
function ParamCluster({ title, hint, sliders, onChange }) {
  return (
    <div className="param-cluster">
      <header>
        <h4>{title}</h4>
        <p>{hint}</p>
      </header>
      <div className="param-sliders">
        {sliders.map(s => (
          <div key={s.key} className="param-slider" title={s.tip}>
            <div className="param-slider-head">
              <span className="ps-math">{s.math}</span>
              <span className="ps-label">{s.label}</span>
              <span className="ps-val">{s.fmt(s.value)}</span>
            </div>
            <input type="range" min={s.min} max={s.max} step={s.step}
                   value={s.value}
                   onChange={e => onChange(s.key, parseFloat(e.target.value))} />
            <div className="ps-tip">{s.tip}</div>
          </div>
        ))}
      </div>
    </div>
  );
}

Object.assign(window, {
  PALETTE: C, fmt,
  CaseClassifier, CaseExplainer,
  PricePathPanelV3: PricePathPanel,
  CumMatchPanelV3: CumMatchPanel,
  MarginPanelV3: MarginPanel,
  EntryFixedPanelV3: EntryFixedPanel,
  TwoSidedPanelV3: TwoSidedPanel,
  OutcomesRhoPanelV3: OutcomesRhoPanel,
  ChartLegend, EquilibriumBars,
  ScenarioCards, ParamCluster,
});
