This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# Lean 4 Formal Verification

Machine-verified proofs for **all 23 formalized theorems** in
"Dutch Clock Trading vs. Posted Prices in Time-Sensitive Matching Markets:
A Timing-Entry-Volume Framework" (Pitz & Ferraz, 2026).

**Status:** 23/23 theorems machine-verified (Aristotle Run 2, March 2026).
**Toolchain:** Lean 4, Mathlib
**Verification engine:** [Aristotle](https://aristotle.harmonic.fun) (Harmonic)

## Building

```bash
cd lean4
lake build
```

Expected output: `Build completed successfully` with zero `sorry` warnings and zero errors.

## Directory structure

- `DutchAuction/` -- Lean 4 files with machine-generated proofs (Aristotle)

## File-to-paper mapping

| File | Paper results covered |
|------|----------------------|
| `Basic.lean` | Core definitions: `Mechanism` structure, entry maps, welfare function, `Delta_wait` |
| `Microfoundation.lean` | Props 3-7 (volume accounting, congestion/volume monotonicity under CRS, Dutch dominance conditions for batch and immediate benchmarks) |
| `DriverEntry.lean` | Lemmas 1-2, **Theorem 1**, Corollary 1 (timing advantage, driver-attractiveness decomposition, one-sided entry dominance, volume dominance) |
| `TwoSidedEntry.lean` | Lemmas 3-4, **Theorem 2**, Corollaries 2-4 (rider-attractiveness decomposition, two-sided entry map monotonicity, two-sided entry dominance, propagation, volume and revenue comparisons) |
| `Revenue.lean` | Prop 13, Corollary 5, **Theorem 3**, Corollary 6 (Dutch price bounds, price dominance, revenue dominance with one-sided + two-sided cases, revenue lower bound) |
| `Welfare.lean` | Props 14-17, Corollary 7 (welfare decomposition, welfare dominance conditions, welfare vs. batch/immediate, **equilibrium welfare comparison with threshold s\*\***) |

## Verification notes

All 23 formalized results were machine-verified by Aristotle. During
verification, five auxiliary hypotheses required strengthening:

1. **Prop 6** (`dutch_dominance_vs_batch`): `hpi_le` (pi_DA <= pi_FPb)
   upgraded to `hpi_eq` (pi_DA = pi_FPb). Under acceptance-rate matching
   the conditional payments are equal in the limiting case.
2. **Lemma 4** (`two_sided_entry_map_monotonicity`): Added `hD_bar_nonneg`
   and `hR_bar_nonneg` (population masses are nonneg).
3. **Theorem 2** (`two_sided_dutch_entry_dominance`): Replaced `huniq_DA`
   (uniqueness) with `hgreatest_DA` (greatest-fixed-point property,
   a consequence of Topkis supermodular theory).
4. **Corollary 2** (`driver_dominance_propagates`): Added equilibrium
   fixed-point equations, rider-side congestion monotonicity, and
   cross-side outward shift.
5. **Corollary 6** (`revenue_lower_bound`): Added `hq_FP_pos`
   (match probability positive, needed for Rev_FP > 0).

The paper's Proposition 6 claims Dutch dominance vs. batch clearing for all
lambda > 0 — the full statement involves a quantifier alternation (for every
lambda > 0, there exists delta*(lambda) > 0 such that dominance holds) that
was not formalized. The verification covers the limiting case (delta -> 0)
where pi_DA = pi_FPb and the timing advantage alone drives dominance.
