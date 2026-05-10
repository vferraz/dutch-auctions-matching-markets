#!/usr/bin/env python3
"""
Quantitative story figures — v3.

Changes from v2:
  - Panel labels are titles ABOVE each panel, not inside the plot area.
  - Each title has a short description: "A. Price path", etc.
  - Figure 1 back to single row, wider figure (6.5in), taller (2.8in).
  - Figure 1C: shorter legend entries, shaded dominance region, bolder line distinction.
  - All figures: more vertical space, no text inside plot areas.
"""

import sys, os
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lib

import matplotlib
matplotlib.use("pgf")
import matplotlib.pyplot as plt
from matplotlib.gridspec import GridSpec

PREAMBLE = r"""
\usepackage[T1]{fontenc}
\usepackage{mathpazo}
\usepackage{amsmath,amssymb}
"""

matplotlib.rcParams.update({
    "pgf.texsystem": "pdflatex",
    "pgf.preamble":  PREAMBLE,
    "font.family":   "serif",
    "font.size":     8.5,
    "axes.labelsize": 8.5,
    "axes.titlesize": 9,
    "xtick.labelsize": 7,
    "ytick.labelsize": 7,
    "legend.fontsize": 7,
    "axes.linewidth":  0.4,
    "xtick.major.width": 0.4,
    "ytick.major.width": 0.4,
    "xtick.major.size":  2.5,
    "ytick.major.size":  2.5,
    "xtick.direction": "out",
    "ytick.direction": "out",
    "axes.spines.top":   False,
    "axes.spines.right": False,
    "axes.titlelocation": "left",
    "axes.titleweight":   "bold",
    "axes.titlepad":      8,
    "lines.linewidth": 1.0,
    "figure.dpi": 150,
    "savefig.dpi": 300,
    "savefig.bbox": "tight",
    "savefig.pad_inches": 0.15,
})

C_DA  = "#2B6CB0"
C_FPi = "#C05621"
C_GR  = "#777777"

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                   "figures_story_quant")
os.makedirs(OUT, exist_ok=True)
p = lib.BASELINE.copy()


# ══════════════════════════════════════════════════════════════════════
#  FIGURE 1 — single row, 3 panels, wider figure
# ══════════════════════════════════════════════════════════════════════

def make_figure1():
    fig = plt.figure(figsize=(6.5, 1.85))
    gs = GridSpec(1, 3, figure=fig, width_ratios=[1, 1, 1.35],
                  wspace=0.40)

    theta, T = p["theta"], p["T"]
    t = np.linspace(0, T, 400)

    # ── A. Price path ─────────────────────────────────────────────
    ax_a = fig.add_subplot(gs[0, 0])
    ax_a.set_title(r"A. Price path")

    pDA = p["rho"] * np.exp(-p["delta"] * t)
    ax_a.plot(t, pDA, color=C_DA, label="DA")
    ax_a.axhline(p["p_bar"], color=C_FPi, ls="--", lw=0.9,
                 label=r"FP$^{\rm imm}$")

    ax_a.set_xlabel(r"Time $t$ (min)")
    ax_a.set_ylabel(r"Price")
    ax_a.set_xlim(0, T)
    ax_a.set_ylim(0, 0.82)
    ax_a.legend(loc="upper right", frameon=False, handlelength=1.4)

    # ── B. Cumulative match probability ───────────────────────────
    ax_b = fig.add_subplot(gs[0, 1])
    ax_b.set_title(r"B. Cumulative match prob.")

    cum_DA = np.array([1.0 - lib.S_DA(ti, theta, p["delta"], p["rho"],
                                        p["A"], p["beta"]) for ti in t])
    eta = lib.eta_FP(theta, p["p_bar"], p["A"], p["beta"])
    cum_FPi = 1.0 - np.exp(-eta * t)

    ax_b.plot(t, cum_DA, color=C_DA, label="DA")
    ax_b.plot(t, cum_FPi, color=C_FPi, ls="--",
              label=r"FP$^{\rm imm}$")
    ax_b.set_xlabel(r"Time $t$ (min)")
    ax_b.set_ylabel(r"Match probability")
    ax_b.set_xlim(0, T)
    ax_b.set_ylim(0, 1.05)
    ax_b.legend(loc="lower right", frameon=False, handlelength=1.4)

    # ── C. Driver-attractiveness decomposition ────────────────────
    ax_c = fig.add_subplot(gs[0, 2])
    ax_c.set_title(r"C. Attractiveness decomposition")

    lam_range = np.linspace(0, 0.15, 300)

    qd  = lib.q_DA(theta, p["delta"], p["rho"], T, p["A"], p["beta"])
    pid = lib.pi_DA(theta, p["delta"], p["rho"], T, p["A"], p["beta"],
                     p["alpha"])
    td  = lib.tau_DA(theta, p["delta"], p["rho"], T, p["A"], p["beta"])
    qf  = lib.q_FP(theta, p["p_bar"], T, p["A"], p["beta"])
    pif = lib.pi_FP(p["alpha"], p["p_bar"])
    tf  = lib.tau_FPi(theta, p["p_bar"], T, p["A"], p["beta"])

    earn = qd * pid - qf * pif
    timing = lam_range * (tf - td)
    total = earn + timing

    ax_c.axhline(0, color=C_GR, lw=0.35)

    # Earnings: horizontal line
    ax_c.plot(lam_range, np.full_like(lam_range, earn),
              color=C_DA, ls=(0, (2, 3)), lw=0.8, label=r"Earnings gap")
    # Timing: linear
    ax_c.plot(lam_range, timing, color=C_FPi, ls="--", lw=0.8,
              label=r"Timing gap")
    # Total: bold black
    ax_c.plot(lam_range, total, color="black", lw=1.4,
              label=r"Total margin")

    # Threshold and shaded dominance region
    case, thresh = lib.dominance_case(theta, p["delta"], p["rho"],
                                       p["p_bar"], T, p["alpha"],
                                       p["A"], p["beta"])
    if case == 4 and 0 < thresh < 0.15:
        # Case 4: dominance for lambda <= lambda**
        ax_c.axvspan(0, thresh, color=C_DA, alpha=0.06)
        ax_c.axvline(thresh, color=C_GR, ls=":", lw=0.5)
        ax_c.text(thresh - 0.005, ax_c.get_ylim()[0] * 0.15,
                  r"$\lambda^{**}$", fontsize=7.5, color=C_GR,
                  ha="right", va="bottom")
    elif case == 2 and 0 < thresh < 0.15:
        # Case 2: dominance for lambda >= lambda*
        ax_c.axvspan(thresh, 0.15, color=C_DA, alpha=0.06)
        ax_c.axvline(thresh, color=C_GR, ls=":", lw=0.5)
        ax_c.text(thresh + 0.005, ax_c.get_ylim()[0] * 0.15,
                  r"$\lambda^{*}$", fontsize=7.5, color=C_GR,
                  ha="left", va="bottom")

    ax_c.set_xlabel(r"Driver waiting cost $\lambda$")
    ax_c.set_ylabel(r"$\bar c_{\rm DA} - \bar c_{\rm FP}$")
    ax_c.set_xlim(0, 0.15)
    ax_c.legend(loc="lower left", frameon=False, handlelength=1.6)

    fig.savefig(os.path.join(OUT,
                "story_fig1_mechanism_to_attractiveness.pdf"))
    plt.close(fig)
    print("  Fig 1 saved")


# ══════════════════════════════════════════════════════════════════════
#  FIGURE 2 — Two-sided amplification (quantitative)
# ══════════════════════════════════════════════════════════════════════

def make_figure2_quant():
    fig = plt.figure(figsize=(6.5, 1.49))
    gs = GridSpec(1, 2, figure=fig, wspace=0.42)

    lam, R = p["lam"], p["R"]
    D_range = np.linspace(1, p["D_bar"], 200)

    # ── A. Fixed-point diagram ────────────────────────────────────
    ax_a = fig.add_subplot(gs[0, 0])
    ax_a.set_title(r"A. Driver entry fixed point")

    phi_DA  = [lib.phi_M(D, "DA",  R, lam, p["D_bar"], p["c_max"], p)
               for D in D_range]
    phi_FPi = [lib.phi_M(D, "FPi", R, lam, p["D_bar"], p["c_max"], p)
               for D in D_range]

    ax_a.plot(D_range, D_range, color=C_GR, lw=0.45)
    ax_a.plot(D_range, phi_DA,  color=C_DA, label="DA")
    ax_a.plot(D_range, phi_FPi, color=C_FPi, ls="--",
              label=r"FP$^{\rm imm}$")

    Ds_DA  = lib.solve_entry("DA",  R, lam, p["D_bar"], p["c_max"], p)
    Ds_FPi = lib.solve_entry("FPi", R, lam, p["D_bar"], p["c_max"], p)
    ax_a.plot(Ds_DA,  Ds_DA,  "o", color=C_DA,  ms=3.5, zorder=5)
    ax_a.plot(Ds_FPi, Ds_FPi, "o", color=C_FPi, ms=3.5, zorder=5)

    ax_a.set_xlabel(r"Driver mass $D$")
    ax_a.set_ylabel(r"$\Phi_M(D)$")
    ax_a.set_xlim(0, p["D_bar"])
    ax_a.set_ylim(0, p["D_bar"])
    ax_a.legend(loc="lower right", frameon=False, handlelength=1.4)

    # ── B. Two-sided closure ────────────────────────────────────
    ax_b = fig.add_subplot(gs[0, 1])
    ax_b.set_title(r"B. Two-sided closure")

    R_BAR = p["R"]

    # Driver response: for each R, solve D*(R)
    R_grid = np.linspace(1.0, R_BAR, 260)
    D_resp_da = np.array([lib.solve_entry("DA", Rv, lam,
                          p["D_bar"], p["c_max"], p) for Rv in R_grid])
    D_resp_fp = np.array([lib.solve_entry("FPi", Rv, lam,
                          p["D_bar"], p["c_max"], p) for Rv in R_grid])

    # Rider response: for each D, solve R*(D)
    D_grid_r = np.linspace(1.0, p["D_bar"], 260)
    R_resp_da = np.array([lib.solve_rider_response(Dv, "DA", R_BAR, p)
                          for Dv in D_grid_r])
    R_resp_fp = np.array([lib.solve_rider_response(Dv, "FPi", R_BAR, p)
                          for Dv in D_grid_r])

    # Two-sided equilibria
    sol_da = lib.solve_two_sided("DA", p, x0=(44.0, 45.0))
    sol_fp = lib.solve_two_sided("FPi", p, x0=(46.0, 62.0))

    # Solid = driver response, dashed = rider response
    ax_b.plot(D_resp_da, R_grid, color=C_DA, lw=1.0, label="DA driver")
    ax_b.plot(D_grid_r, R_resp_da, color=C_DA, ls="--", lw=0.9,
              label="DA rider")
    ax_b.plot(D_resp_fp, R_grid, color=C_FPi, lw=1.0, label="FPi driver")
    ax_b.plot(D_grid_r, R_resp_fp, color=C_FPi, ls="--", lw=0.9,
              label="FPi rider")
    ax_b.plot(sol_da[0], sol_da[1], "o", color=C_DA, ms=3.5, zorder=5)
    ax_b.plot(sol_fp[0], sol_fp[1], "o", color=C_FPi, ms=3.5, zorder=5)

    ax_b.set_xlabel(r"Driver mass $D$")
    ax_b.set_ylabel(r"Rider mass $R$")
    ax_b.set_xlim(0, p["D_bar"])
    ax_b.set_ylim(0, R_BAR)
    ax_b.legend(loc="upper left", frameon=False, handlelength=1.4,
                fontsize=6.5)

    fig.savefig(os.path.join(OUT,
                "story_fig2_two_sided_amplification_quant.pdf"))
    plt.close(fig)
    print("  Fig 2 (quant) saved")


# ══════════════════════════════════════════════════════════════════════
#  FIGURE 3 — Outcomes along rho
# ══════════════════════════════════════════════════════════════════════

def make_figure3():
    fig = plt.figure(figsize=(6.5, 1.40))
    gs = GridSpec(1, 3, figure=fig, wspace=0.55)

    rho_vals = np.linspace(0.35, 0.95, 80)

    D_da  = np.empty_like(rho_vals)
    D_fpi = np.empty_like(rho_vals)
    Rev_da  = np.empty_like(rho_vals)
    Rev_fpi = np.empty_like(rho_vals)
    W_da  = np.empty_like(rho_vals)
    W_fpi = np.empty_like(rho_vals)

    for i, rh in enumerate(rho_vals):
        pp = p.copy(); pp["rho"] = rh
        res = lib.compute_equilibrium(pp)
        D_da[i]   = res["DA"]["D_star"]
        D_fpi[i]  = res["FPi"]["D_star"]
        Rev_da[i]  = res["DA"]["Rev"]
        Rev_fpi[i] = res["FPi"]["Rev"]
        W_da[i]   = res["DA"]["W"]
        W_fpi[i]  = res["FPi"]["W"]

    entry_adv = D_da - D_fpi
    rev_ratio = np.where(Rev_fpi > 0, Rev_da / Rev_fpi, 1.0)
    welfare_diff = W_da - W_fpi

    titles = [
        r"A. Entry advantage",
        r"B. Revenue ratio",
        r"C. Welfare difference",
    ]
    ylabels = [
        r"$D^*_{\rm DA} - D^*_{\rm FP}$",
        r"$\mathrm{Rev}_{\rm DA}/\mathrm{Rev}_{\rm FP}$",
        r"$W_{\rm DA} - W_{\rm FP}$",
    ]
    ydata_list = [entry_adv, rev_ratio, welfare_diff]
    refs = [0, 1, 0]

    for col in range(3):
        ax = fig.add_subplot(gs[0, col])
        ax.set_title(titles[col])
        ax.plot(rho_vals, ydata_list[col], color="black", lw=1.0)
        ax.axhline(refs[col], color=C_GR, lw=0.35)
        ax.axvline(p["rho"], color=C_GR, ls=":", lw=0.45)
        ax.set_xlabel(r"$\rho = p_0/\bar v$")
        ax.set_ylabel(ylabels[col])
        ax.set_xlim(rho_vals[0], rho_vals[-1])

    fig.savefig(os.path.join(OUT, "story_fig3_outcomes_vs_rho.pdf"))
    plt.close(fig)
    print("  Fig 3 saved")


if __name__ == "__main__":
    print("Generating quantitative story figures (v3)...")
    make_figure1()
    make_figure2_quant()
    make_figure3()
    print(f"Done. Output in {OUT}/")
