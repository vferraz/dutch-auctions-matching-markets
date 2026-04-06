#!/usr/bin/env python3
"""
Baseline controlled-thickness simulation for DA vs FPi vs FPb.

Design:
- Fix (D,R) exogenously (no endogenous entry).
- Run many sessions per cell, per mechanism.
- Log sessions/drivers/riders/matches.
- Aggregate to (mechanism,D,R) cell estimators:
    qhat, pihat (driver payment | match), tauhat (driver), tauhat_rider, mhat, pbarhat (rider price | match)
- Compute Lemma-2 dominance residuals for DA vs FPb and DA vs FPi.

Outputs to ./baseline_sim_out by default.
"""

from dataclasses import dataclass
import itertools, os, uuid
import numpy as np
import pandas as pd


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
    fpb_variant: str = "reserve"  # baseline: reserve on acceptance, execute at batch


def price(mech: str, t: float, P: Params) -> float:
    if mech in ("FPi", "FPb"):
        return P.p0
    if mech == "DA":
        return max(P.p_min, P.p_max - P.beta * t)
    raise ValueError(f"Unknown mechanism: {mech}")


def run_session(mech: str, D: int, R: int, P: Params, seed: int):
    rng = np.random.default_rng(seed)

    # --- Types (EDIT THESE DISTRIBUTIONS IF NEEDED) ---
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

        K = rng.poisson(P.mu)  # number of meetings this tick
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
                t_exec = t_accept if mech in ("DA", "FPi") else float(P.T_batch)

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

    # ---- Build agent logs (time-to-contract is t_exec; unmatched -> T_end) ----
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
        lambda=P.lam,
        T_end=P.T_end,
        dt=P.dt,
        mu=P.mu,
        p0=P.p0,
        p_max=P.p_max,
        p_min=P.p_min,
        beta=P.beta,
        T_batch=P.T_batch,
        fpb_variant=P.fpb_variant,
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
                "session_id",
                "mechanism",
                "D",
                "R",
                "match_id",
                "rider_id",
                "driver_id",
                "t_accept",
                "t_exec",
                "p_rider",
                "p_driver",
            ]
        )

    return sessions_row, drivers_df, riders_df, matches_df


def run_experiment(
    P: Params,
    mechanisms=("DA", "FPi", "FPb"),
    D_grid=(20, 40, 60),
    R_grid=(20, 40, 60),
    n_rep=30,
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

    # Payment conditional on match (guard for no matches)
    def mean_pay_cond(g):
        m = g.loc[g["matched"] == 1, "pay_driver"]
        return np.nan if len(m) == 0 else float(m.mean())

    # Avoid pandas future warning by selecting only required columns
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
    # Delta = lam*(tau_b - tau_DA) - (q_b*pi_b - q_DA*pi_DA)
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


def main():
    P = Params()
    sessions_df, drivers_df, riders_df, matches_df = run_experiment(P)
    agg_df = aggregate_cells(sessions_df, drivers_df, riders_df, matches_df)

    delta_fpb = dominance_residual(agg_df, P, "FPb")
    delta_fpi = dominance_residual(agg_df, P, "FPi")

    outdir = "baseline_sim_out"
    os.makedirs(outdir, exist_ok=True)

    sessions_df.to_csv(os.path.join(outdir, "sessions.csv"), index=False)
    drivers_df.to_csv(os.path.join(outdir, "drivers.csv"), index=False)
    riders_df.to_csv(os.path.join(outdir, "riders.csv"), index=False)
    matches_df.to_csv(os.path.join(outdir, "matches.csv"), index=False)
    agg_df.to_csv(os.path.join(outdir, "cell_estimates.csv"), index=False)
    delta_fpb.to_csv(os.path.join(outdir, "dominance_DA_vs_FPb.csv"), index=False)
    delta_fpi.to_csv(os.path.join(outdir, "dominance_DA_vs_FPi.csv"), index=False)

    print(f"Wrote outputs to: {outdir}")


if __name__ == "__main__":
    main()
