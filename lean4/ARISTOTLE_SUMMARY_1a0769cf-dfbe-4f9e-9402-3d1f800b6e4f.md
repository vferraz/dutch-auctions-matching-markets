# Summary of changes
## Summary

I filled **15 out of 16** `sorry` placeholders across the four target files. `lake build` succeeds (8033 jobs, no errors).

### Files changed and theorems proved

**`DutchAuction/Microfoundation.lean`** — 2/2 filled:
- `poisson_match_prob_bounds` — Poisson match probability lies in (0,1), proved using `positivity` and `Real.exp_pos`.
- `batch_timing_gap` — Batch clears at session end so τ_FPb − τ_DA > 0, proved by `linarith`.

**`DutchAuction/TwoSidedEntry.lean`** — 10/11 filled:
- `two_sided_equilibrium_uniqueness` — Contraction implies unique fixed point, proved via `abs_cases` + `nlinarith` + `grind`.
- `rider_match_prob_accounting` — q^R = D·q/R accounting identity, proved by `hm ▸ rfl`.
- `batch_rider_cutoff` — Batch rider cutoff simplification, proved by `htauR_batch ▸ rfl`.
- `rider_batch_dominance` — **[REVISED]** Dutch attracts more riders than batch **conditionally**: requires the timing advantage to dominate the price disadvantage, i.e., `(p̄_DA − p̄_FPb) · q^R < κ · (τ^R_FPb − τ^R_DA)`. This is the denominator-cleared form of the `κ > κ₀` condition from the revised Proposition 13(b). The old unconditional version (which assumed `κ > 0` plus `p̄_DA ≤ p̄_FPb`) has been replaced. Proved via `field_simp` + `nlinarith`.
- `rider_kappa_threshold` — κ* threshold iff, proved via `nlinarith` + `mul_div_cancel₀`.
- `rider_dominance_case1` — A ≥ 0, B ≥ 0 ⟹ A + κB ≥ 0, proved by `positivity`.
- `rider_dominance_case3` — A < 0, B ≤ 0 ⟹ A + κB < 0, proved by `nlinarith`.
- `rider_dominance_case4` — Iff for A ≥ 0, B < 0 case, proved via `nlinarith` + `mul_div_cancel₀`.
- ⚠️ `two_sided_equilibrium_existence` — **remains `sorry`** (out-of-scope Brouwer/Mathlib limitation; see below).

**`DutchAuction/Revenue.lean`** — 1/1 filled:
- `revenue_three_channel_decomposition` — Three-channel revenue decomposition Rev_DA/Rev_FP = (D*/D*)(q/q)(p̄/p̄), proved via `unfold Rev; grind`.

**`DutchAuction/Welfare.lean`** — 4/4 filled:
- `welfare_fixed_thickness_iff` — Fixed-thickness welfare iff, proved via `constructor <;> intro <;> unfold Welfare <;> linarith`.
- `welfare_vs_immediate_volume_reversal` — Volume-reversal welfare threshold, proved via `le_div_iff₀` + `linarith`.
- `equilibrium_welfare_case_b_iff` — Case (b) full iff with s** threshold, proved via `div_le_iff₀` + `nlinarith`.
- `equilibrium_welfare_case_c` — Case (c) welfare failure, proved via `unfold Welfare Delta_wait; nlinarith`.

### Remaining sorry

`two_sided_equilibrium_existence` (line 253 of `DutchAuction/TwoSidedEntry.lean`) states that a continuous self-map of the compact rectangle [0, D̄] × [0, R̄] has a fixed point. This is mathematically correct — it is a direct instance of the **Brouwer fixed-point theorem** in two dimensions. However, Brouwer's fixed-point theorem (and its equivalent forms: Poincaré–Miranda, Schauder for finite-dimensional spaces) is **not available in the current version of Mathlib** (commit `8f9d9cff…`, Lean 4.28.0). This sorry is out-of-scope and intentionally preserved.

### Revision log

| Date | Change | Reason |
|------|--------|--------|
| 2026-04-07 | `rider_batch_dominance`: replaced unconditional `κ > 0` + `p̄_DA ≤ p̄_FPb` formulation with conditional dominance hypothesis `(DA.pbar − FPb.pbar) * qR < κ * (FPb.tauR − DA.tauR)` | Paper math-consistency pass revised Proposition 13(b): the timing advantage must dominate the price disadvantage (κ > κ₀) |

### Build status

`lake build` completes successfully. The one remaining `sorry` (`two_sided_equilibrium_existence`) produces a compiler warning but no error. All other definitions, theorem statements, existing proofs, imports, options, and file structure are preserved exactly as provided.
