#!/usr/bin/env python3
"""
Controlled-thickness simulation with two diagnostic variants:

Variant A: TIMING_ONLY
- DA price path stays near posted price p0 to remove price channel.

Variant B: TRADEOFF_CASE
- DA prices lower than FPi (so pi_DA < pi_FPi)
- FPi has an execution/confirmation delay delta_FPi > 0 (so tau_FPi larger)

Outputs per run:
- sessions.csv, drivers.csv, riders.csv, matches.csv
- cell_estimates.csv
- dominance_DA_vs_FPb.csv, dominance_DA_vs_FPi.csv
- lambda_star_tables.csv (thresholds for dominance where applicable)
- plots: tau_driver.png, q_driver.png, pbar.png, lambda_star_FPi.png (if applicable)

All estimators correspond to the LaTeX measurement appendix.
"""

from dataclasses import dataclass
import itertools, os, uuid
import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
import argparse


@dataclass
class Params:
    # Fees + waiting costs
    alpha: float = 0.2
    kappa: float = 0.1
    lam: float = 0.1

    # Session timing + search
    T_end: float = 10.0
    dt: float = 0.1
    mu: float = 5.0  # mean meetings per tick (Poisson)

    # FP (posted price)
    p0: float = 10.0

    # DA (Dutch clock) price path: p(t)=max(p_min, p_max - beta*t)
    p_max: float = 20.0
    p_min: float = 2.0
    beta: float = 1.5

    # FPb (batch execution) executes at T_batch
    T_batch: float = 10.0
    fpb_variant: str = "reserve"

    # Mechanism-specific confirmation delays (added)
    delta_FPi: float = 0.0
    delta_DA: float = 0.0
    delta_FPb: float = 0.0


def preset(variant: str) -> Params:
    """Parameter presets for the two variants."""
    v = variant.upper().strip()
    if v == "TIMING_ONLY":
        # Keep DA around p0, eliminate price channel
        return Params(
            p0=10.0,
            p_max=10.5,
            p_min=9.5,
            beta=0.1,
            mu=5.0,
            T_end=10.0,
            T_batch=10.0,
            delta_FPi=0.0,
        )
    if v == "TRADEOFF_CASE":
        # DA lower prices than FPi; FPi gets confirmation delay
        return Params(
            p0=10.0,
            p_max=9.0,
            p_min=5.0,
            beta=1.0,
            mu=5.0,
            T_end=10.0,
            T_batch=10.0,
            delta_FPi=2.0,
        )
    raise ValueError(f"Unknown variant: {variant}")


def price(mech: str, t: float, P: Params) -> float:
    if mech in ("FPi", "FPb"):
        return P.p0
    if mech == "DA":
        return max(P.p_min, P.p_max - P.beta * t)
    raise ValueError(f"Unknown mechanism: {mech}")


def exec_time(mech: str, t_accept: float, P: Params) -> float:
    """Execution time including confirmation delays / batch execution."""
    if mech == "DA":
        return min(t_accept + P.delta_DA, P.T_end)
    if mech == "FPi":
        return min(t_accept + P.delta_FPi, P.T_end)
    if mech == "FPb":
        return min(P.T_batch + P.delta_FPb, P.T_end)
    raise ValueError(f"Unknown mechanism: {mech}")


def run_session(mech: str, D: int, R: int, P: Params, seed: int):
    rng = np.random.default_rng(seed)

    # Types (edit if needed)
    v = rng.lognormal(mean=2.5, sigma=0.35, size=R)  # riders' gross values
    c = rng.lognormal(mean=1.8, sigma=0.40, size=D)  # drivers' per-trip costs

    rider_av = np.ones(R, dtype=bool)
    driver_av = np.ones(D, dtype=bool)

    matches = []
    mid = 0
    times = np.arange(0.0, P.T_end + 1e-12, P.dt)

    for t in times:
        if not rider_av.any() or not driver_av.any():
            break

        K = rng.poisson(P.mu)  # meetings this tick
        for _ in range(K):
            if not rider_av.any() or not driver_av.any():
                break

            i = rng.choice(np.flatnonzero(rider_av))
            j = rng.choice(np.flatnonzero(driver_av))

            p = price(mech, float(t), P)
            p_drv = (1.0 - P.alpha) * p

            # Myopic linear waiting-cost acceptance
            acc_r = (v[i] - p - P.kappa * t) >= 0.0
            acc_d = (p_drv - c[j] - P.lam * t) >= 0.0

            if acc_r and acc_d:
                t_accept = float(t)
                t_exec = exec_time(mech, t_accept, P)

                matches.append(
                    dict(
                        match_id=mid,
                        rider_id=int(i),
                        driver_id=int(j),
                        t_accept=t_accept,
                        t_exec=t_exec,
                        p_rider=float(p),
                        p_driver=float(p_drv),
                    )
                )
                mid += 1
                rider_av[i] = False
                driver_av[j] = False

    # Build agent logs (time-to-contract is t_exec; unmatched -> T_end)
    matched_r = np.zeros(R, dtype=int)
    matched_d = np.zeros(D, dtype=int)
    tau_r = np.full(R, P.T_end, dtype=float)
    tau_d = np.full(D, P.T_end, dtype=float)
    price_paid = np.zeros(R, dtype=float)
    pay_driver = np.zeros(D, dtype=float)
    match_r = np.full(R, -1, dtype=int)
    match_d = np.full(D, -1, dtype=int)

    for m in matches:
        i = m["rider_id"]
        j = m["driver_id"]
        matched_r[i] = 1
        matched_d[j] = 1
        tau_r[i] = m["t_exec"]
        tau_d[j] = m["t_exec"]
        price_paid[i] = m["p_rider"]
        pay_driver[j] = m["p_driver"]
        match_r[i] = m["match_id"]
        match_d[j] = m["match_id"]

    session_id = str(uuid.uuid4())[:8]
    sessions_row = dict(
        session_id=session_id,
        mechanism=mech,
        R=R,
        D=D,
        alpha=P.alpha,
        kappa=P.kappa,
        lambda_cost=P.lam,
        T_end=P.T_end,
        dt=P.dt,
        mu=P.mu,
        p0=P.p0,
        p_max=P.p_max,
        p_min=P.p_min,
        beta=P.beta,
        T_batch=P.T_batch,
        fpb_variant=P.fpb_variant,
        delta_FPi=P.delta_FPi,
        delta_DA=P.delta_DA,
        delta_FPb=P.delta_FPb,
        m_s=len(matches),
        seed=seed,
    )

    drivers_df = pd.DataFrame(
        dict(
            session_id=session_id,
            mechanism=mech,
            D=D,
            R=R,
            driver_id=np.arange(D, dtype=int),
            c_j=c,
            matched=matched_d,
            tau_driver=tau_d,
            pay_driver=pay_driver,
            match_id=match_d,
        )
    )
    riders_df = pd.DataFrame(
        dict(
            session_id=session_id,
            mechanism=mech,
            D=D,
            R=R,
            rider_id=np.arange(R, dtype=int),
            v_i=v,
            matched=matched_r,
            tau_rider=tau_r,
            price_paid=price_paid,
            match_id=match_r,
        )
    )

    matches_df = pd.DataFrame(matches)
    if len(matches_df) > 0:
        matches_df.insert(0, "session_id", session_id)
        matches_df.insert(1, "mechanism", mech)
        matches_df.insert(2, "D", D)
        matches_df.insert(3, "R", R)
    else:
        matches_df = pd.DataFrame(
            columns=[
                "session_id","mechanism","D","R","match_id","rider_id","driver_id",
                "t_accept","t_exec","p_rider","p_driver"
            ]
        )

    return sessions_row, drivers_df, riders_df, matches_df


def run_experiment(
    P: Params,
    mechanisms=("DA", "FPi", "FPb"),
    D_grid=(20, 40, 60),
    R_grid=(20, 40, 60),
    n_rep=50,
    seed0=1234,
):
    sessions = []
    drivers = []
    riders = []
    matches = []
    seed = seed0

    for mech, D, R in itertools.product(mechanisms, D_grid, R_grid):
        for _ in range(n_rep):
            row, ddf, rdf, mdf = run_session(mech, D, R, P, seed)
            sessions.append(row)
            drivers.append(ddf)
            riders.append(rdf)
            matches.append(mdf)
            seed += 1

    return (
        pd.DataFrame(sessions),
        pd.concat(drivers, ignore_index=True),
        pd.concat(riders, ignore_index=True),
        pd.concat(matches, ignore_index=True),
    )


def aggregate_cells(sessions_df, drivers_df, riders_df, matches_df):
    keys = ["mechanism", "D", "R"]

    gdr = drivers_df.groupby(keys, dropna=False)
    qhat = gdr["matched"].mean().rename("qhat")
    tauhat = gdr["tau_driver"].mean().rename("tauhat_driver")

    def mean_pay_cond(g):
        m = g.loc[g["matched"] == 1, "pay_driver"]
        return np.nan if len(m) == 0 else float(m.mean())

    pihat = gdr.apply(lambda g: mean_pay_cond(g), include_groups=False).rename("pihat_driver_cond")

    grr = riders_df.groupby(keys, dropna=False)
    tauR = grr["tau_rider"].mean().rename("tauhat_rider")

    mhat = sessions_df.groupby(keys)["m_s"].mean().rename("mhat")

    if len(matches_df) > 0:
        gm = matches_df.groupby(keys, dropna=False)
        pbar = gm["p_rider"].mean().rename("pbarhat")
    else:
        pbar = pd.Series(dtype=float, name="pbarhat")

    out = pd.concat([qhat, tauhat, pihat, tauR, mhat, pbar], axis=1).reset_index()
    return out


def dominance_residual(agg_df, P: Params, benchmark: str):
    key = ["D", "R"]
    da = agg_df[agg_df["mechanism"] == "DA"].set_index(key)
    bb = agg_df[agg_df["mechanism"] == benchmark].set_index(key)

    merged = da[["qhat", "tauhat_driver", "pihat_driver_cond"]].join(
        bb[["qhat", "tauhat_driver", "pihat_driver_cond"]],
        lsuffix="_DA",
        rsuffix=f"_{benchmark}",
        how="inner",
    ).reset_index()

    merged["Delta"] = (
        P.lam * (merged[f"tauhat_driver_{benchmark}"] - merged["tauhat_driver_DA"])
        - (
            merged[f"qhat_{benchmark}"] * merged[f"pihat_driver_cond_{benchmark}"]
            - merged["qhat_DA"] * merged["pihat_driver_cond_DA"]
        )
    )
    merged["benchmark"] = benchmark
    return merged


def lambda_star_table(agg_df, benchmark: str):
    key = ["D", "R"]
    da = agg_df[agg_df["mechanism"] == "DA"].set_index(key)
    bb = agg_df[agg_df["mechanism"] == benchmark].set_index(key)

    merged = da[["qhat", "tauhat_driver", "pihat_driver_cond"]].join(
        bb[["qhat", "tauhat_driver", "pihat_driver_cond"]],
        lsuffix="_DA",
        rsuffix=f"_{benchmark}",
        how="inner",
    )

    num = merged[f"qhat_{benchmark}"] * merged[f"pihat_driver_cond_{benchmark}"] - merged["qhat_DA"] * merged["pihat_driver_cond_DA"]
    den = merged[f"tauhat_driver_{benchmark}"] - merged["tauhat_driver_DA"]

    out = merged.reset_index()[["D", "R"]].copy()
    out["benchmark"] = benchmark
    out["num_payment_gap"] = num.values
    out["den_time_gap"] = den.values
    out["lambda_star"] = np.where(den.values > 0, num.values / den.values, np.nan)
    return out


def plot_cell_lines(agg_df, ycol: str, title: str, ylabel: str, outpath: str):
    mech_order = ["DA", "FPi", "FPb"]
    df = agg_df.copy()
    df["mechanism"] = pd.Categorical(df["mechanism"], categories=mech_order, ordered=True)
    df = df.sort_values(["D", "R", "mechanism"])

    plt.figure()
    for (D, R), g in df.groupby(["D", "R"]):
        plt.plot(g["mechanism"].astype(str), g[ycol], marker="o", label=f"D={D}, R={R}")
    plt.xlabel("Mechanism")
    plt.ylabel(ylabel)
    plt.title(title)
    plt.legend(title="Thickness cell")
    plt.tight_layout()
    plt.savefig(outpath, dpi=200)
    plt.close()


def plot_lambda_star(tab, benchmark: str, outpath: str):
    df = tab[tab["benchmark"] == benchmark].copy()
    df = df.dropna(subset=["lambda_star"])
    if len(df) == 0:
        return
    plt.figure()
    for D in sorted(df["D"].unique()):
        g = df[df["D"] == D].sort_values("R")
        plt.plot(g["R"], g["lambda_star"], marker="o", label=f"D={D}")
    plt.xlabel("R (riders)")
    plt.ylabel("lambda* threshold")
    plt.title(f"Lambda* thresholds for DA dominance vs {benchmark}")
    plt.legend(title="Driver mass D")
    plt.tight_layout()
    plt.savefig(outpath, dpi=200)
    plt.close()


def run_variant(
    variant: str,
    outdir: str,
    D_grid=(20, 40, 60),
    R_grid=(20, 40, 60),
    n_rep=50,
    seed0=1234,
):
    P = preset(variant)
    sessions_df, drivers_df, riders_df, matches_df = run_experiment(P, D_grid=D_grid, R_grid=R_grid, n_rep=n_rep, seed0=seed0)
    agg_df = aggregate_cells(sessions_df, drivers_df, riders_df, matches_df)

    delta_fpb = dominance_residual(agg_df, P, "FPb")
    delta_fpi = dominance_residual(agg_df, P, "FPi")

    lamtab_fpb = lambda_star_table(agg_df, "FPb")
    lamtab_fpi = lambda_star_table(agg_df, "FPi")
    lamtab = pd.concat([lamtab_fpb, lamtab_fpi], ignore_index=True)

    os.makedirs(outdir, exist_ok=True)

    sessions_df.to_csv(os.path.join(outdir, "sessions.csv"), index=False)
    drivers_df.to_csv(os.path.join(outdir, "drivers.csv"), index=False)
    riders_df.to_csv(os.path.join(outdir, "riders.csv"), index=False)
    matches_df.to_csv(os.path.join(outdir, "matches.csv"), index=False)
    agg_df.to_csv(os.path.join(outdir, "cell_estimates.csv"), index=False)
    delta_fpb.to_csv(os.path.join(outdir, "dominance_DA_vs_FPb.csv"), index=False)
    delta_fpi.to_csv(os.path.join(outdir, "dominance_DA_vs_FPi.csv"), index=False)
    lamtab.to_csv(os.path.join(outdir, "lambda_star_tables.csv"), index=False)

    # Plots
    plot_cell_lines(
        agg_df,
        "tauhat_driver",
        f"Time-to-contract by mechanism ({variant})",
        "Mean time-to-contract (driver) τ̂",
        os.path.join(outdir, "tau_driver.png"),
    )
    plot_cell_lines(
        agg_df,
        "qhat",
        f"Driver match probability by mechanism ({variant})",
        "Match probability (driver) q̂",
        os.path.join(outdir, "q_driver.png"),
    )
    plot_cell_lines(
        agg_df,
        "pbarhat",
        f"Mean transaction price by mechanism ({variant})",
        "Mean rider price (match) p̄",
        os.path.join(outdir, "pbar.png"),
    )
    plot_lambda_star(lamtab, "FPi", os.path.join(outdir, "lambda_star_FPi.png"))

    overall = agg_df.groupby("mechanism")[["qhat","tauhat_driver","pihat_driver_cond","mhat","pbarhat","tauhat_rider"]].mean().reset_index()
    overall.to_csv(os.path.join(outdir, "overall_means.csv"), index=False)

    return P, agg_df, overall


def main():
    parser = argparse.ArgumentParser(description="Controlled-thickness simulation variants (TIMING_ONLY, TRADEOFF_CASE).")
    parser.add_argument("--variants", nargs="+", default=["TIMING_ONLY","TRADEOFF_CASE"],
                        help="Which variants to run (default: both).")
    parser.add_argument("--D", nargs="+", type=int, default=[20,40,60],
                        help="Driver grid values, e.g. --D 20 40 60")
    parser.add_argument("--R", nargs="+", type=int, default=[20,40,60],
                        help="Rider grid values, e.g. --R 20 40 60")
    parser.add_argument("--n_rep", type=int, default=50,
                        help="Repetitions per (mechanism,D,R) cell (default: 50).")
    parser.add_argument("--seed0", type=int, default=1234, help="Base RNG seed (default: 1234).")
    parser.add_argument("--out", default="variants_out", help="Output directory (default: variants_out).")
    args = parser.parse_args()

    base_out = args.out
    os.makedirs(base_out, exist_ok=True)

    D_grid = tuple(args.D)
    R_grid = tuple(args.R)

    for variant in args.variants:
        v = variant.upper()
        outdir = os.path.join(base_out, v.lower())
        run_variant(v, outdir, D_grid=D_grid, R_grid=R_grid, n_rep=args.n_rep, seed0=args.seed0)

    print(f"Wrote outputs to: {base_out}/<variant>/")

if __name__ == "__main__":
    main()
