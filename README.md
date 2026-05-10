# Dutch auctions in clock-based platform markets

Public artifacts for the paper:

> **Timing, Entry, and Revenue in Clock-Based Platform Markets**  
> Pitz and Ferraz (2026)  
> Submitted to Management Science

## Repository contents

- `lean4/` - Lean 4 formalization of the paper's theorems
- `code/` - simulation code, replication scripts, and figure generation
- `code/paper_figures/` - figures used in the paper

The repository is organized as a compact public companion for the
project rather than a full research workspace.

## Lean formalization

The Lean tree contains 57 theorems across 7 files, with 1 remaining
`sorry`: the Brouwer fixed-point theorem in
`lean4/DutchAuction/TwoSidedEntry.lean`, which remains gated on Mathlib
coverage.

Toolchain: `leanprover/lean4:v4.29.0-rc8`, aligned with the Mathlib
`master-2026-03-29` pin.

To build:

```bash
cd lean4
lake build
```

Key theorems:

- `DriverEntry.driver_dominance_case1`,
  `DriverEntry.driver_lambda_threshold`,
  `DriverEntry.driver_dominance_case3`, and
  `DriverEntry.driver_dominance_case4` - driver-side four-case
  classification for local attractiveness.
- `TwoSidedEntry.rider_dominance_case1`,
  `TwoSidedEntry.rider_kappa_threshold`,
  `TwoSidedEntry.rider_dominance_case3`, and
  `TwoSidedEntry.rider_dominance_case4` - rider-side four-case
  classification for local attractiveness.
- `Microfoundation.tau_ge_under_convex_hazard` - reverse timing
  inequality under ARM via a convex-hazard chord bound.
- `PaymentInequality.pi_DA_ge_pi_FPb_under_premium_average` -
  conditional payment inequality with a named diagnostic.
- `Revenue.revenue_three_channel_decomposition` - three-channel
  decomposition for the revenue ratio.

## Quantitative artifacts

Generate the quantitative story figures with:

```bash
cd code
python3 script_figures_quant.py
```

The exported PNGs used by the paper are in `code/paper_figures/`.
Generated story-figure outputs are in `code/figures_story_quant/`.

## Companion paper

A companion paper studies the one-lot Dutch auction with bidder waiting
costs and identifies a void-tax effect under voluntary participation.
That work has its own repository at
`github.com/vferraz/dutch-auctions-clock-speed` (in progress).

## Tags

- `v1-geb-submission` - state at the April 2026 GEB submission.
- `v2-mansci-submission` - state at the Management Science submission
  (May 2026).
