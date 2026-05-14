// app-v3.jsx — refined layout for v3.

const { useState, useMemo } = React;

const PRESETS = {
  Baseline: {
    A: 0.5, beta: 0.5, T: 30, rho: 0.7, delta: 0.02,
    pbar: 0.5, alpha: 0.20, theta: 2.0,
    Dbar: 100, cmax: 0.5, R: 200,
    lam: 0.05, kappa: 0.03, s: 1.0,
  },
  "Slow clock": {
    A: 0.5, beta: 0.5, T: 30, rho: 0.7, delta: 0.005,
    pbar: 0.5, alpha: 0.20, theta: 2.0,
    Dbar: 100, cmax: 0.5, R: 200,
    lam: 0.05, kappa: 0.03, s: 1.0,
  },
  "Fast clock": {
    A: 0.5, beta: 0.5, T: 30, rho: 0.7, delta: 0.08,
    pbar: 0.5, alpha: 0.20, theta: 2.0,
    Dbar: 100, cmax: 0.5, R: 200,
    lam: 0.05, kappa: 0.03, s: 1.0,
  },
  "Tradeoff": {
    A: 0.5, beta: 0.5, T: 30, rho: 0.5, delta: 0.05,
    pbar: 0.6, alpha: 0.20, theta: 1.0,
    Dbar: 100, cmax: 0.5, R: 100,
    lam: 0.05, kappa: 0.03, s: 1.0,
  },
  "Rider-rich": {
    A: 0.5, beta: 0.5, T: 30, rho: 0.7, delta: 0.02,
    pbar: 0.5, alpha: 0.20, theta: 4.0,
    Dbar: 100, cmax: 0.5, R: 400,
    lam: 0.05, kappa: 0.03, s: 1.0,
  },
  "Driver-rich": {
    A: 0.5, beta: 0.5, T: 30, rho: 0.7, delta: 0.02,
    pbar: 0.5, alpha: 0.20, theta: 0.5,
    Dbar: 100, cmax: 0.5, R: 50,
    lam: 0.05, kappa: 0.03, s: 1.0,
  },
};

const SCENARIO_DESCS = {
  Baseline: "Table OA.1 calibration: ρ = 0.7, δ = 0.02, p̄ = 0.5. Lands in Case 4 — DA earns a premium but contracts slower.",
  "Slow clock": "δ → 0: the clock barely descends. DA prices stay high; the earnings advantage swells but so does the wait.",
  "Fast clock": "δ large: prices crash quickly. Volume climbs but the trade-weighted DA price falls below p̄.",
  Tradeoff: "Posted price p̄ above the clock start. Creates the textbook tradeoff — DA only wins above a floor λ★.",
  "Rider-rich": "θ = 4: four riders per driver. Fast meetings on the driver side; DA's earnings premium amplified.",
  "Driver-rich": "θ = 0.5: drivers chase scarce riders. Match probabilities sag; the timing channel grows.",
};

const CLUSTERS = [
  {
    title: "Trading-format design",
    hint: "The platform's levers — what the clock and the post look like.",
    sliders: [
      { key: "rho",   math: "ρ",  label: "start price",  min: 0.2, max: 0.95, step: 0.01, fmt: v => v.toFixed(2),
        tip: "p₀ / v̄ — top of the descending clock relative to max rider value." },
      { key: "delta", math: "δ",  label: "clock speed",  min: 0.001, max: 0.15, step: 0.001, fmt: v => v.toFixed(3),
        tip: "Proportional price decline rate. p(t) = p₀ · exp(−δt)." },
      { key: "pbar",  math: "p̄", label: "posted price", min: 0.1, max: 0.9, step: 0.01, fmt: v => v.toFixed(2),
        tip: "The flat price under PP-imm and PP-batch." },
      { key: "T",     math: "T",  label: "session min",  min: 5, max: 90, step: 1, fmt: v => v.toFixed(0),
        tip: "Length of the trading session in minutes." },
      { key: "alpha", math: "α",  label: "commission",   min: 0, max: 0.5, step: 0.01, fmt: v => (v*100).toFixed(0)+"%",
        tip: "Platform commission. Drivers receive (1−α)·p per trade." },
    ],
  },
  {
    title: "Matching technology",
    hint: "Bilateral CRS Poisson meetings. Tightness θ = R / D.",
    sliders: [
      { key: "theta", math: "θ",  label: "tightness R/D", min: 0.2, max: 5, step: 0.05, fmt: v => v.toFixed(2),
        tip: "Rider-to-driver ratio at fixed thickness." },
      { key: "A",     math: "A",  label: "meeting eff.",  min: 0.1, max: 1.5, step: 0.05, fmt: v => v.toFixed(2),
        tip: "Aggregate meeting efficiency M(D,R) = A · D^(1-β) · R^β." },
      { key: "beta",  math: "β",  label: "match elast.",  min: 0.1, max: 0.9, step: 0.05, fmt: v => v.toFixed(2),
        tip: "Elasticity of meetings w.r.t. rider mass. Empirically ~0.5 in ride-hailing." },
    ],
  },
  {
    title: "Entry primitives",
    hint: "Waiting costs and pool sizes that close the entry equilibria.",
    sliders: [
      { key: "lam",   math: "λ",  label: "driver wait",   min: 0, max: 0.15, step: 0.001, fmt: v => v.toFixed(3),
        tip: "Driver per-minute waiting cost. The main lever in the 4-case classifier." },
      { key: "kappa", math: "κ",  label: "rider wait",    min: 0, max: 0.15, step: 0.001, fmt: v => v.toFixed(3),
        tip: "Rider per-minute waiting cost." },
      { key: "Dbar",  math: "D̄",  label: "driver cap",    min: 10, max: 200, step: 5, fmt: v => v.toFixed(0),
        tip: "Upper bound on driver pool — entry sits below this." },
      { key: "cmax",  math: "c̄",  label: "entry cost cap", min: 0.05, max: 2, step: 0.05, fmt: v => v.toFixed(2),
        tip: "Maximum entry cost in the driver pool's uniform distribution." },
      { key: "R",     math: "R̄",  label: "rider cap",      min: 20, max: 400, step: 5, fmt: v => v.toFixed(0),
        tip: "Upper bound on rider pool size." },
    ],
  },
];

function AppV3() {
  const M = window.Model;
  const [p, setP] = useState(() => Object.assign({}, PRESETS.Baseline));
  const [preset, setPreset] = useState("Baseline");
  const [showParams, setShowParams] = useState(true);

  function set(k, v) {
    setP(prev => Object.assign({}, prev, { [k]: v }));
    setPreset(null);
  }
  function applyPreset(name) {
    setP(Object.assign({}, PRESETS[name]));
    setPreset(name);
  }

  return (
    <div className="appv3">
      {/* ── MASTHEAD (slim) ─────────────────────────────────── */}
      <header className="masthead-v3">
        <div className="m3-left">
          <div className="m3-eyebrow">
            Pitz &amp; Ferraz · 2026 · Interactive companion
          </div>
          <h1 className="m3-title">
            Timing, Entry, and Revenue
          </h1>
          <p className="m3-sub">
            in clock-based platform markets
          </p>
        </div>
        <div className="m3-right">
          <p className="m3-blurb">
            On platforms where time-to-contract matters — flower auctions, ride-hailing,
            on-demand labor — the trading format determines who enters, market thickness,
            and revenue. This page lets you live-explore the paper's four-case classifier
            and watch a Monte Carlo session play out side-by-side across the three
            mechanisms.
          </p>
          <div className="m3-meta">
            <span>v3 · <a href="https://github.com/vferraz/dutch-auctions-matching-markets"
                          target="_blank" rel="noreferrer">replication code</a></span>
          </div>
        </div>
      </header>

      {/* ── SCENARIOS ────────────────────────────────────────── */}
      <section className="scenarios-section">
        <div className="section-pretitle">
          <h2>Scenarios</h2>
          <p>Pick a calibration to see how the classifier and the live session respond. Each
            scenario lands in a different region of the four-case diagram.</p>
        </div>
        <ScenarioCards presets={PRESETS} descriptions={SCENARIO_DESCS}
                       active={preset} onSelect={applyPreset} />
      </section>

      {/* ── SESSION THEATER ─────────────────────────────────── */}
      <section className="theater-section">
        <Theater p={p} M={M} />
      </section>

      {/* ── CASE CLASSIFIER + EXPLAINER ─────────────────────── */}
      <section className="classifier-section">
        <div className="section-pretitle">
          <h2>The four-case classifier</h2>
          <p>Two signed gaps decide everything: how much more PP earns per trade, and how
            much faster (or slower) PP contracts. The four quadrants are the paper's four cases.</p>
        </div>
        <div className="classifier-grid">
          <div className="classifier-plot">
            <CaseClassifier p={p} M={M} />
          </div>
          <div className="classifier-text">
            <CaseExplainer p={p} M={M} />
          </div>
        </div>
      </section>

      {/* ── ANALYTIC PANELS (2 × 3) ─────────────────────────── */}
      <section className="panels-section-v3">
        <div className="section-pretitle">
          <h2>Analytic objects</h2>
          <p>Reduced-form quantities from <code>lib.py</code>. Every panel uses the same
            colour code; the legend below applies throughout.</p>
        </div>
        <div className="panels-grid-v3">
          <PricePathPanelV3 p={p} M={M} />
          <CumMatchPanelV3  p={p} M={M} />
          <MarginPanelV3    p={p} M={M} />
          <EntryFixedPanelV3 p={p} M={M} />
          <TwoSidedPanelV3  p={p} M={M} />
          <OutcomesRhoPanelV3 p={p} M={M} />
        </div>
        <ChartLegend />
      </section>

      {/* ── EQUILIBRIUM OUTCOMES (bars) ─────────────────────── */}
      <section className="eq-section-v3">
        <div className="section-pretitle">
          <h2>Equilibrium outcomes</h2>
          <p>At the entry fixed point (rider mass held at the pool cap). Bars are normalised
            per row; ★ marks the per-metric winner.</p>
        </div>
        <EquilibriumBars p={p} M={M} />
      </section>

      {/* ── PARAMETERS (demoted, collapsible) ─────────────── */}
      <section className="params-section">
        <header className="params-header">
          <div>
            <h2>Parameters</h2>
            <p>Move any of the model's primitives. Hover a slider for its definition.</p>
          </div>
          <button className="params-toggle"
                  onClick={() => setShowParams(s => !s)}>
            {showParams ? "Hide" : "Show"}
          </button>
        </header>
        {showParams && (
          <div className="params-grid">
            {CLUSTERS.map(cluster => (
              <ParamCluster key={cluster.title}
                            title={cluster.title}
                            hint={cluster.hint}
                            sliders={cluster.sliders.map(s =>
                              Object.assign({}, s, { value: p[s.key] }))}
                            onChange={set} />
            ))}
          </div>
        )}
      </section>

      <footer className="foot-v3">
        <span>Uniform <em>v</em> ∼ U[0,1] · CRS Poisson meetings · large-market approximation · φ = 0</span>
        <span><a href="https://github.com/vferraz/dutch-auctions-matching-markets"
                 target="_blank" rel="noreferrer">vferraz/dutch-auctions-matching-markets</a></span>
      </footer>
    </div>
  );
}

ReactDOM.createRoot(document.getElementById("root")).render(<AppV3 />);
