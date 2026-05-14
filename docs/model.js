// Port of code/lib.py from
//   "Timing, Entry, and Revenue in Clock-Based Platform Markets"
//   Pitz & Ferraz (2026)
// All formulas match lib.py one-to-one. Uniform values v ~ U[0,1] so
// barF_V(x) = max(0, 1-x). Numerical integrals use composite Simpson.

(function (root) {
  "use strict";

  // ── Numerical helpers ───────────────────────────────────────────────
  function simpson(f, a, b, n) {
    // n must be even
    if (n % 2) n += 1;
    const h = (b - a) / n;
    let s = f(a) + f(b);
    for (let i = 1; i < n; i++) {
      const x = a + i * h;
      s += (i % 2 ? 4 : 2) * f(x);
    }
    return (s * h) / 3;
  }

  function brent(f, lo, hi, tol = 1e-7, maxIter = 100) {
    // Simple bisection — robust enough for monotone entry maps.
    let flo = f(lo), fhi = f(hi);
    if (flo === 0) return lo;
    if (fhi === 0) return hi;
    if (flo * fhi > 0) return null; // no sign change
    for (let i = 0; i < maxIter; i++) {
      const mid = 0.5 * (lo + hi);
      const fm = f(mid);
      if (Math.abs(fm) < tol || (hi - lo) < tol) return mid;
      if (flo * fm < 0) { hi = mid; fhi = fm; }
      else              { lo = mid; flo = fm; }
    }
    return 0.5 * (lo + hi);
  }

  // ── Primitives ──────────────────────────────────────────────────────
  function muD(theta, A, beta) { return A * Math.pow(theta, beta); }
  function muR(theta, A, beta) { return A * Math.pow(theta, beta - 1); }

  // ── Fixed-price benchmarks (PP^imm / PP^batch) ──────────────────────
  function etaFP(theta, pbar, A, beta) {
    return muD(theta, A, beta) * Math.max(0, 1 - pbar);
  }
  function qFP(theta, pbar, T, A, beta) {
    return 1 - Math.exp(-etaFP(theta, pbar, A, beta) * T);
  }
  function tauFPi(theta, pbar, T, A, beta) {
    const e = etaFP(theta, pbar, A, beta);
    if (e < 1e-12) return T;
    return (1 - Math.exp(-e * T)) / e;
  }
  function tauFPb(T) { return T; }
  function piFP(alpha, pbar) { return (1 - alpha) * pbar; }

  // ── Dutch / clock auction ───────────────────────────────────────────
  function H_DA(t, theta, delta, rho, A, beta) {
    const mu = muD(theta, A, beta);
    if (delta < 1e-12) return mu * t * (1 - rho);
    return mu * (t - (rho / delta) * (1 - Math.exp(-delta * t)));
  }
  function S_DA(t, theta, delta, rho, A, beta) {
    return Math.exp(-H_DA(t, theta, delta, rho, A, beta));
  }
  function h_DA(t, theta, delta, rho, A, beta) {
    return muD(theta, A, beta) * (1 - rho * Math.exp(-delta * t));
  }
  function qDA(theta, delta, rho, T, A, beta) {
    return 1 - Math.exp(-H_DA(T, theta, delta, rho, A, beta));
  }
  function tauDA(theta, delta, rho, T, A, beta) {
    return simpson(t => S_DA(t, theta, delta, rho, A, beta), 0, T, 120);
  }
  function pbarDA(theta, delta, rho, T, A, beta) {
    const q = qDA(theta, delta, rho, T, A, beta);
    if (q < 1e-30) return rho;
    const num = simpson(
      t => rho * Math.exp(-delta * t)
         * h_DA(t, theta, delta, rho, A, beta)
         * S_DA(t, theta, delta, rho, A, beta),
      0, T, 120);
    return num / q;
  }
  function piDA(theta, delta, rho, T, A, beta, alpha) {
    return (1 - alpha) * pbarDA(theta, delta, rho, T, A, beta);
  }

  // ── Driver-cutoff ───────────────────────────────────────────────────
  function cBar(q, pi, tau, lam) { return q * pi - lam * tau; }

  // ── Bidirectional four-case dominance (DA vs PP^imm) ────────────────
  function dominanceCase(theta, delta, rho, pbar, T, alpha, A, beta) {
    const qf = qFP(theta, pbar, T, A, beta);
    const pif = piFP(alpha, pbar);
    const qd = qDA(theta, delta, rho, T, A, beta);
    const pid = piDA(theta, delta, rho, T, A, beta, alpha);
    const tf = tauFPi(theta, pbar, T, A, beta);
    const td = tauDA(theta, delta, rho, T, A, beta);
    const dpi = qf * pif - qd * pid;     // earnings gap (PP - DA)
    const dtau = tf - td;                 // timing gap   (PP - DA)
    let kase, thr;
    if (dpi <= 0 && dtau >= 0)      { kase = 1; thr = 0; }
    else if (dpi > 0 && dtau > 0)   { kase = 2; thr = dpi / dtau; }
    else if (dpi >= 0 && dtau <= 0) { kase = 3; thr = Infinity; }
    else                             { kase = 4; thr = Math.abs(dpi) / Math.abs(dtau); }
    return { kase, thr, dpi, dtau, qf, pif, qd, pid, tf, td };
  }

  // ── Rider-side objects ──────────────────────────────────────────────
  function qR(D, R, qd) { return (D * qd) / Math.max(R, 1e-12); }

  function H_R_DA(t, theta, delta, rho, A, beta) {
    const mu = muR(theta, A, beta);
    if (delta < 1e-12) return mu * t * (1 - rho);
    return mu * (t - (rho / delta) * (1 - Math.exp(-delta * t)));
  }
  function tauR_DA(theta, delta, rho, T, A, beta) {
    return simpson(t => Math.exp(-H_R_DA(t, theta, delta, rho, A, beta)), 0, T, 120);
  }
  function tauR_FPi(theta, pbar, T, A, beta) {
    const er = muR(theta, A, beta) * Math.max(0, 1 - pbar);
    if (er < 1e-12) return T;
    return (1 - Math.exp(-er * T)) / er;
  }
  function tauR_FPb(T) { return T; }

  // ── Reduced-form bundle ────────────────────────────────────────────
  function reducedForm(mech, theta, p) {
    if (mech === "DA") {
      return {
        q:  qDA(theta, p.delta, p.rho, p.T, p.A, p.beta),
        pi: piDA(theta, p.delta, p.rho, p.T, p.A, p.beta, p.alpha),
        tau: tauDA(theta, p.delta, p.rho, p.T, p.A, p.beta),
        pbm: pbarDA(theta, p.delta, p.rho, p.T, p.A, p.beta),
      };
    } else if (mech === "FPi") {
      return {
        q:  qFP(theta, p.pbar, p.T, p.A, p.beta),
        pi: piFP(p.alpha, p.pbar),
        tau: tauFPi(theta, p.pbar, p.T, p.A, p.beta),
        pbm: p.pbar,
      };
    } else {
      return {
        q:  qFP(theta, p.pbar, p.T, p.A, p.beta),
        pi: piFP(p.alpha, p.pbar),
        tau: tauFPb(p.T),
        pbm: p.pbar,
      };
    }
  }

  // ── Entry map (driver side, R fixed) ───────────────────────────────
  function phiM(D, mech, R, lam, Dbar, cmax, p) {
    if (D < 1e-10) D = 1e-10;
    const theta = R / D;
    const rf = reducedForm(mech, theta, p);
    const cb = cBar(rf.q, rf.pi, rf.tau, lam);
    return Math.min(Math.max(0, cb) * (Dbar / cmax), Dbar);
  }
  function solveEntry(mech, R, lam, Dbar, cmax, p) {
    const eps = 0.01;
    const g = D => D - phiM(D, mech, R, lam, Dbar, cmax, p);
    if (g(eps) >= 0) return 0;
    if (g(Dbar) <= 0) return Dbar;
    const r = brent(g, eps, Dbar, 1e-6, 80);
    return r == null ? 0 : r;
  }

  // ── Rider entry map ────────────────────────────────────────────────
  function vbarMech(mech, D, R, p) {
    D = Math.max(D, 1e-8); R = Math.max(R, 1e-8);
    const theta = R / D;
    let qd, qr, tr, pbm;
    if (mech === "DA") {
      qd = qDA(theta, p.delta, p.rho, p.T, p.A, p.beta);
      qr = qR(D, R, qd);
      tr = tauR_DA(theta, p.delta, p.rho, p.T, p.A, p.beta);
      pbm = pbarDA(theta, p.delta, p.rho, p.T, p.A, p.beta);
    } else if (mech === "FPi") {
      qd = qFP(theta, p.pbar, p.T, p.A, p.beta);
      qr = qR(D, R, qd);
      tr = tauR_FPi(theta, p.pbar, p.T, p.A, p.beta);
      pbm = p.pbar;
    } else { // FPb
      qd = qFP(theta, p.pbar, p.T, p.A, p.beta);
      qr = qR(D, R, qd);
      tr = tauR_FPb(p.T);
      pbm = p.pbar;
    }
    if (qr <= 1e-12) return 1;
    return pbm + (p.kappa * tr) / qr;
  }
  function phiR(D, R, mech, Rbar, p) {
    const vb = vbarMech(mech, D, R, p);
    const surv = Math.max(0, Math.min(1, 1 - vb));
    return Rbar * surv;
  }
  function solveRiderResponse(D, mech, Rbar, p) {
    const g = R => R - phiR(D, R, mech, Rbar, p);
    const lo = 1e-6, hi = Rbar;
    if (g(lo) >= 0) return 0;
    if (g(hi) <= 0) return Rbar;
    const r = brent(g, lo, hi, 1e-6, 80);
    return r == null ? 0 : r;
  }

  // Two-sided fixed point — Picard iteration on (D,R) -> (phiD, phiR)
  function solveTwoSided(mech, p, x0) {
    let D = x0 ? x0[0] : 40;
    let R = x0 ? x0[1] : 40;
    for (let i = 0; i < 200; i++) {
      const D2 = phiM(D, mech, R, p.lam, p.Dbar, p.cmax, p);
      const R2 = phiR(D2, R, mech, p.R, p);
      const err = Math.abs(D2 - D) + Math.abs(R2 - R);
      D = 0.5 * D + 0.5 * D2;
      R = 0.5 * R + 0.5 * R2;
      if (err < 1e-5) break;
    }
    return [D, R];
  }

  // ── Equilibrium (one-sided, R fixed) ───────────────────────────────
  function computeEquilibrium(p, lamOverride) {
    const lam = (lamOverride == null) ? p.lam : lamOverride;
    const R = p.R;
    const out = {};
    for (const mech of ["DA", "FPi", "FPb"]) {
      const Dstar = solveEntry(mech, R, lam, p.Dbar, p.cmax, p);
      if (Dstar < 1e-10) {
        out[mech] = { Dstar: 0, q: 0, pi: 0, tau: 0, pbm: 0, m: 0, Rev: 0, W: 0, tauR: 0 };
        continue;
      }
      const theta = R / Dstar;
      const rf = reducedForm(mech, theta, p);
      const m = Dstar * rf.q;
      let tauR;
      if (mech === "DA") tauR = tauR_DA(theta, p.delta, p.rho, p.T, p.A, p.beta);
      else if (mech === "FPi") tauR = tauR_FPi(theta, p.pbar, p.T, p.A, p.beta);
      else tauR = tauR_FPb(p.T);
      const Rev = p.alpha * m * rf.pbm;
      const W = m * p.s - lam * Dstar * rf.tau - p.kappa * R * tauR;
      out[mech] = { Dstar, q: rf.q, pi: rf.pi, tau: rf.tau, pbm: rf.pbm, m, Rev, W, tauR };
    }
    return out;
  }

  // ── Default parameters ─────────────────────────────────────────────
  const BASELINE = {
    A: 0.5, beta: 0.5,
    T: 30.0, rho: 0.7, delta: 0.02,
    pbar: 0.5, alpha: 0.20, theta: 2.0,
    Dbar: 100.0, cmax: 0.5, R: 200.0,
    lam: 0.05, kappa: 0.03, s: 1.0,
  };

  root.Model = {
    BASELINE,
    simpson, brent,
    muD, muR,
    etaFP, qFP, tauFPi, tauFPb, piFP,
    H_DA, S_DA, h_DA, qDA, tauDA, pbarDA, piDA,
    cBar, dominanceCase,
    qR, tauR_DA, tauR_FPi, tauR_FPb,
    reducedForm,
    phiM, solveEntry,
    phiR, solveRiderResponse, solveTwoSided,
    computeEquilibrium,
  };
})(window);
