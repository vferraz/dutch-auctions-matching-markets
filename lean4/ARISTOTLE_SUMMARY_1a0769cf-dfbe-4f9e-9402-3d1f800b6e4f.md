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
- `rider_batch_dominance` — Dutch attracts more riders than batch, proved via `field_simp` + `nlinarith`.
- `rider_kappa_threshold` — κ* threshold iff, proved via `nlinarith` + `mul_div_cancel₀`.
- `rider_dominance_case1` — A ≥ 0, B ≥ 0 ⟹ A + κB ≥ 0, proved by `positivity`.
- `rider_dominance_case3` — A < 0, B ≤ 0 ⟹ A + κB < 0, proved by `nlinarith`.
- `rider_dominance_case4` — Iff for A ≥ 0, B < 0 case, proved via `nlinarith` + `mul_div_cancel₀`.
- ⚠️ `two_sided_equilibrium_existence` — **remains `sorry`** (see below).

**`DutchAuction/Revenue.lean`** — 1/1 filled:
- `revenue_three_channel_decomposition` — Three-channel revenue decomposition Rev_DA/Rev_FP = (D*/D*)(q/q)(p̄/p̄), proved via `unfold Rev; grind`.

**`DutchAuction/Welfare.lean`** — 4/4 filled:
- `welfare_fixed_thickness_iff` — Fixed-thickness welfare iff, proved via `constructor <;> intro <;> unfold Welfare <;> linarith`.
- `welfare_vs_immediate_volume_reversal` — Volume-reversal welfare threshold, proved via `le_div_iff₀` + `linarith`.
- `equilibrium_welfare_case_b_iff` — Case (b) full iff with s** threshold, proved via `div_le_iff₀` + `nlinarith`.
- `equilibrium_welfare_case_c` — Case (c) welfare failure, proved via `unfold Welfare Delta_wait; nlinarith`.

### Remaining sorry

`two_sided_equilibrium_existence` (line 253 of `DutchAuction/TwoSidedEntry.lean`) states that a continuous self-map of the compact rectangle [0, D̄] × [0, R̄] has a fixed point. This is mathematically correct — it is a direct instance of the **Brouwer fixed-point theorem** in two dimensions. However, Brouwer's fixed-point theorem (and its equivalent forms: Poincaré–Miranda, Schauder for finite-dimensional spaces) is **not available in the current version of Mathlib** (commit `8f9d9cff…`, Lean 4.28.0). Mathlib provides the 1D intermediate-value fixed-point theorem (`exists_mem_Icc_isFixedPt_of_mapsTo`) and the Banach contraction mapping theorem, but neither generalises to the 2D non-contractive setting required here. Proving Brouwer from scratch is a substantial formalisation project involving algebraic topology or degree theory, which exceeds what can be done in this session.

### Build status

`lake build` completes successfully. The one remaining `sorry` produces a compiler warning but no error. All other definitions, theorem statements, existing proofs, imports, options, and file structure are preserved exactly as provided.