"""
Core mechanism functions and equilibrium solver for
"Timing, Entry, and Revenue in Clock-Based Platform Markets"
(Pitz and Ferraz, 2026).
"""

import numpy as np
from scipy import integrate, optimize

# ── Constants ────────────────────────────────────────────────────────
C_DA  = "#2B6CB0"
C_FPi = "#C05621"
C_FPb = "#9B2C2C"

BASELINE = dict(
    A=0.5, beta=0.5, T=30.0, rho=0.7, delta=0.02,
    p_bar=0.5, alpha=0.20, theta=2.0,
    D_bar=100.0, c_max=0.5, R=200.0,
    lam=0.05, kappa=0.03, s=1.0,
)

# ── Primitives ───────────────────────────────────────────────────────

def mu_D(theta, A, beta):
    return A * theta**beta

def mu_R(theta, A, beta):
    return A * theta**(beta - 1.0)

# ── Fixed-price benchmarks (FPi and FPb) ─────────────────────────────

def eta_FP(theta, p_bar, A, beta):
    return mu_D(theta, A, beta) * (1.0 - p_bar)

def q_FP(theta, p_bar, T, A, beta):
    e = eta_FP(theta, p_bar, A, beta)
    return 1.0 - np.exp(-e * T)

def tau_FPi(theta, p_bar, T, A, beta):
    e = eta_FP(theta, p_bar, A, beta)
    q = q_FP(theta, p_bar, T, A, beta)
    return q / e

def tau_FPb(T):
    return T

def pi_FP(alpha, p_bar):
    return (1.0 - alpha) * p_bar

def p_bar_FP(p_bar):
    return p_bar

# ── Dutch auction (DA) ───────────────────────────────────────────────

def H_DA(t, theta, delta, rho, A, beta):
    mu = mu_D(theta, A, beta)
    if delta < 1e-12:
        return mu * t * (1.0 - rho)
    return mu * (t - (rho / delta) * (1.0 - np.exp(-delta * t)))

def S_DA(t, theta, delta, rho, A, beta):
    return np.exp(-H_DA(t, theta, delta, rho, A, beta))

def h_DA(t, theta, delta, rho, A, beta):
    mu = mu_D(theta, A, beta)
    return mu * (1.0 - rho * np.exp(-delta * t))

def q_DA(theta, delta, rho, T, A, beta):
    return 1.0 - np.exp(-H_DA(T, theta, delta, rho, A, beta))

def tau_DA(theta, delta, rho, T, A, beta):
    val, _ = integrate.quad(
        lambda t: S_DA(t, theta, delta, rho, A, beta), 0, T)
    return val

def p_bar_DA(theta, delta, rho, T, A, beta):
    """Trade-weighted average Dutch price."""
    q = q_DA(theta, delta, rho, T, A, beta)
    if q < 1e-30:
        return rho
    num, _ = integrate.quad(
        lambda t: rho * np.exp(-delta * t)
                  * h_DA(t, theta, delta, rho, A, beta)
                  * S_DA(t, theta, delta, rho, A, beta),
        0, T)
    return num / q

def pi_DA(theta, delta, rho, T, A, beta, alpha):
    return (1.0 - alpha) * p_bar_DA(theta, delta, rho, T, A, beta)

# ── Driver-attractiveness cutoff ─────────────────────────���───────────

def c_bar(q, pi, tau, lam):
    return q * pi - lam * tau

# ── Break-even waiting cost (DA vs FPi) ──────────────────────────────

def dominance_case(theta, delta, rho, p_bar, T, alpha, A, beta):
    """Classify into Cases 1-4 and return (case, threshold).

    Returns (case, lam_threshold) where:
      Case 1: Dutch dom. for all lambda >= 0  (threshold = 0)
      Case 2: Dutch dom. for lambda >= threshold  (floor)
      Case 3: FPi dom. for all lambda > 0   (threshold = inf)
      Case 4: Dutch dom. for lambda <= threshold  (ceiling)
    """
    qf = q_FP(theta, p_bar, T, A, beta)
    pif = pi_FP(alpha, p_bar)
    qd = q_DA(theta, delta, rho, T, A, beta)
    pid = pi_DA(theta, delta, rho, T, A, beta, alpha)
    tf = tau_FPi(theta, p_bar, T, A, beta)
    td = tau_DA(theta, delta, rho, T, A, beta)
    delta_pi = qf * pif - qd * pid
    delta_tau = tf - td

    if delta_pi <= 0 and delta_tau >= 0:
        return 1, 0.0
    elif delta_pi > 0 and delta_tau > 0:
        return 2, delta_pi / delta_tau
    elif delta_pi >= 0 and delta_tau <= 0:
        return 3, np.inf
    else:
        return 4, abs(delta_pi) / abs(delta_tau)


def lambda_star(theta, delta, rho, p_bar, T, alpha, A, beta):
    """Break-even threshold (same numerical value for Cases 2 and 4)."""
    qf = q_FP(theta, p_bar, T, A, beta)
    pif = pi_FP(alpha, p_bar)
    qd = q_DA(theta, delta, rho, T, A, beta)
    pid = pi_DA(theta, delta, rho, T, A, beta, alpha)
    tf = tau_FPi(theta, p_bar, T, A, beta)
    td = tau_DA(theta, delta, rho, T, A, beta)
    denom = tf - td
    numer = qf * pif - qd * pid
    if abs(denom) < 1e-14:
        return np.inf if numer > 0 else -np.inf
    return numer / denom

# ── Acceptance-rate matching locus ────────────────────────────────────

def p_bar_ARM(delta, rho, T):
    if delta < 1e-12:
        return rho
    return rho * (1.0 - np.exp(-delta * T)) / (delta * T)

# ── Rider-side objects ────────────────────────────────────────────────

def q_R(D, R, q_D):
    return D * q_D / R

def H_R_DA(t, theta, delta, rho, A, beta):
    mu = mu_R(theta, A, beta)
    if delta < 1e-12:
        return mu * t * (1.0 - rho)
    return mu * (t - (rho / delta) * (1.0 - np.exp(-delta * t)))

def tau_R_DA(theta, delta, rho, T, A, beta):
    val, _ = integrate.quad(
        lambda t: np.exp(-H_R_DA(t, theta, delta, rho, A, beta)), 0, T)
    return val

def tau_R_FPi(theta, p_bar, T, A, beta):
    eta_r = mu_R(theta, A, beta) * (1.0 - p_bar)
    q_r = 1.0 - np.exp(-eta_r * T)
    return q_r / eta_r

def tau_R_FPb(T):
    return T

def rider_dominance_case(theta, delta, rho, p_bar, T, alpha, A, beta, D, R):
    """Classify rider-side dominance into Cases 1-4 and return (case, threshold).

    Parallel to driver-side dominance_case().  Uses:
        A_price = p_bar_FPi - p_bar_DA   (positive ⇒ DA cheaper for riders)
        B_time  = tauR_FPi/qR_FPi - tauR_DA/qR_DA  (positive ⇒ DA better time/match)
    Condition: A_price + kappa * B_time >= 0.

    Returns (case, kap_threshold) where:
      Case 1: DA dom. for all kappa >= 0         (threshold = 0)
      Case 2: DA dom. for kappa >= threshold      (floor)
      Case 3: FPi dom. for all kappa >= 0         (threshold = inf)
      Case 4: DA dom. for kappa <= threshold      (ceiling)
    """
    pd = p_bar_DA(theta, delta, rho, T, A, beta)
    pf = p_bar
    a_price = pf - pd                  # A >= 0 means DA cheaper

    qd_driver = q_DA(theta, delta, rho, T, A, beta)
    qf_driver = q_FP(theta, p_bar, T, A, beta)
    qr_da = q_R(D, R, qd_driver)
    qr_fp = q_R(D, R, qf_driver)

    tr_da = tau_R_DA(theta, delta, rho, T, A, beta)
    tr_fp = tau_R_FPi(theta, p_bar, T, A, beta)

    # denom has the same sign as B_time (since qr products > 0)
    denom = qr_da * tr_fp - qr_fp * tr_da

    if a_price >= 0 and denom >= 0:        # Case 1
        return 1, 0.0
    elif a_price < 0 and denom > 0:        # Case 2 (floor)
        return 2, (pd - pf) * qr_da * qr_fp / denom
    elif a_price < 0 and denom <= 0:       # Case 3 (FPi dominates)
        return 3, np.inf
    else:                                  # Case 4 (ceiling): a_price >= 0, denom < 0
        return 4, abs((pd - pf) * qr_da * qr_fp / denom)


def kappa_star(theta, delta, rho, p_bar, T, alpha, A, beta, D, R):
    """Rider break-even waiting cost (DA vs FPi).

    Thin wrapper around rider_dominance_case().  Returns the scalar
    threshold with sign convention: negative means 'no admissible kappa'.
    """
    case, ks = rider_dominance_case(theta, delta, rho, p_bar, T, alpha,
                                    A, beta, D, R)
    if case == 1:
        return -np.inf       # dominates for all kappa >= 0
    elif case == 3:
        return np.inf        # fails for all kappa >= 0
    else:
        return ks            # floor (case 2) or ceiling (case 4)

# ── Entry equilibrium solver ───────────────────────────────────���─────

def compute_reduced_form(mechanism, theta, p):
    """Return (q, pi, tau, p_bar_mech) for a mechanism and theta."""
    if mechanism == "DA":
        q = q_DA(theta, p["delta"], p["rho"], p["T"], p["A"], p["beta"])
        pi = pi_DA(theta, p["delta"], p["rho"], p["T"], p["A"], p["beta"], p["alpha"])
        tau = tau_DA(theta, p["delta"], p["rho"], p["T"], p["A"], p["beta"])
        pb = p_bar_DA(theta, p["delta"], p["rho"], p["T"], p["A"], p["beta"])
    elif mechanism == "FPi":
        q = q_FP(theta, p["p_bar"], p["T"], p["A"], p["beta"])
        pi = pi_FP(p["alpha"], p["p_bar"])
        tau = tau_FPi(theta, p["p_bar"], p["T"], p["A"], p["beta"])
        pb = p["p_bar"]
    elif mechanism == "FPb":
        q = q_FP(theta, p["p_bar"], p["T"], p["A"], p["beta"])
        pi = pi_FP(p["alpha"], p["p_bar"])
        tau = tau_FPb(p["T"])
        pb = p["p_bar"]
    else:
        raise ValueError(mechanism)
    return q, pi, tau, pb


def phi_M(D, mechanism, R, lam, D_bar, c_max, p):
    """Entry map: Phi_M(D) = (D_bar/c_max) * max(0, c_bar_M)."""
    if D < 1e-10:
        D = 1e-10
    theta = R / D
    q, pi, tau, _ = compute_reduced_form(mechanism, theta, p)
    cb = c_bar(q, pi, tau, lam)
    val = (D_bar / c_max) * max(0.0, cb)
    return min(val, D_bar)


def solve_entry(mechanism, R, lam, D_bar, c_max, p):
    """Solve D* = Phi_M(D*) via brentq."""
    eps = 0.01
    def g(D):
        return D - phi_M(D, mechanism, R, lam, D_bar, c_max, p)
    g_lo = g(eps)
    g_hi = g(D_bar)
    if g_lo >= 0:
        return 0.0
    if g_hi <= 0:
        return D_bar
    try:
        return optimize.brentq(g, eps, D_bar, xtol=1e-8)
    except ValueError:
        return 0.0


def compute_equilibrium(p, lam_override=None):
    """Compute D*, m, Rev, W for all three mechanisms."""
    lam = lam_override if lam_override is not None else p["lam"]
    R = p["R"]
    results = {}
    for mech in ["DA", "FPi", "FPb"]:
        D_star = solve_entry(mech, R, lam, p["D_bar"], p["c_max"], p)
        if D_star < 1e-10:
            results[mech] = dict(D_star=0, q=0, pi=0, tau=0, p_bar_m=0,
                                 m=0, Rev=0, W=0, tau_R=0)
            continue
        theta = R / D_star
        q, pi, tau, pb = compute_reduced_form(mech, theta, p)
        m = D_star * q
        if mech == "DA":
            tr = tau_R_DA(theta, p["delta"], p["rho"], p["T"], p["A"], p["beta"])
        elif mech == "FPi":
            tr = tau_R_FPi(theta, p["p_bar"], p["T"], p["A"], p["beta"])
        else:
            tr = tau_R_FPb(p["T"])
        Rev = p["alpha"] * m * pb
        W = m * p["s"] - lam * D_star * tau - p["kappa"] * R * tr
        results[mech] = dict(D_star=D_star, q=q, pi=pi, tau=tau,
                             p_bar_m=pb, m=m, Rev=Rev, W=W, tau_R=tr)
    return results


# ── Rider entry map and two-sided equilibrium ───────────────────────

def vbar_mech(mech, D, R, p):
    """Rider reservation value (break-even v) under mechanism *mech*.

    Returns v_bar such that riders with v >= v_bar enter.
    """
    D = max(float(D), 1e-8)
    R = max(float(R), 1e-8)
    theta = R / D
    if mech == "DA":
        qd = q_DA(theta, p["delta"], p["rho"], p["T"], p["A"], p["beta"])
        qr = q_R(D, R, qd)
        tr = tau_R_DA(theta, p["delta"], p["rho"], p["T"], p["A"], p["beta"])
        pb = p_bar_DA(theta, p["delta"], p["rho"], p["T"], p["A"], p["beta"])
    elif mech == "FPi":
        qd = q_FP(theta, p["p_bar"], p["T"], p["A"], p["beta"])
        qr = q_R(D, R, qd)
        tr = tau_R_FPi(theta, p["p_bar"], p["T"], p["A"], p["beta"])
        pb = p["p_bar"]
    else:
        raise ValueError(mech)
    if qr <= 1e-12:
        return 1.0
    return pb + p["kappa"] * tr / qr


def phi_R(D, R, mech, R_bar, p):
    """Rider entry map: Phi^R_M(D, R) = R_bar * (1 - v_bar_M)."""
    vb = vbar_mech(mech, D, R, p)
    surv = max(0.0, min(1.0, 1.0 - vb))
    return R_bar * surv


def solve_rider_response(D, mech, R_bar, p):
    """Solve R = Phi^R_M(D, R) for given D via brentq."""
    def g(R):
        return R - phi_R(D, R, mech, R_bar, p)
    lo, hi = 1e-6, R_bar
    glo, ghi = g(lo), g(hi)
    if glo >= 0:
        return 0.0
    if ghi <= 0:
        return R_bar
    return optimize.brentq(g, lo, hi, xtol=1e-8)


def solve_two_sided(mech, p, x0=None):
    """Solve the two-sided entry system (D, R) simultaneously.

    Returns (D*, R*) satisfying:
      D = Phi^D_M(D; R, lambda)
      R = Phi^R_M(D, R; R_bar)
    """
    R_bar = p["R"]
    if x0 is None:
        x0 = (40.0, 40.0)

    def F(z):
        D, R = float(max(z[0], 1e-8)), float(max(z[1], 1e-8))
        return [
            D - phi_M(D, mech, R, p["lam"], p["D_bar"], p["c_max"], p),
            R - phi_R(D, R, mech, R_bar, p),
        ]

    sol = optimize.root(F, np.array(x0, dtype=float))
    if not sol.success:
        raise RuntimeError(f"two-sided solver failed for {mech}: {sol.message}")
    return sol.x


# ── Sweeps ──────────────────────────────────────────────────────────

def dominance_sweep(param_name, param_vals, p):
    """Compute case and threshold over a sweep of one parameter."""
    thresholds = np.empty_like(param_vals)
    cases = np.empty(len(param_vals), dtype=int)
    for i, v in enumerate(param_vals):
        pp = p.copy()
        pp[param_name] = v
        c, thr = dominance_case(pp["theta"], pp["delta"], pp["rho"],
                                pp["p_bar"], pp["T"], pp["alpha"],
                                pp["A"], pp["beta"])
        thresholds[i] = thr
        cases[i] = c
    return thresholds, cases
