# Lean 4 formalization

This directory contains a Lean 4 machine-checked audit of the algebraic and
order-theoretic components of:

> **Timing, Entry, and Revenue in Clock-Based Platform Markets**
> Pitz and Ferraz (2026)

It is a focused audit rather than a full machine certification of the paper.
It machine-verifies the algebra, order theory, and four-case sign analysis
underlying the entry, dominance, revenue, and welfare propositions. The
existence step in the two-sided amplification theorem (Brouwer's fixed-point
theorem) is not currently derivable in the pinned Mathlib environment and is
retained as a single transparent `sorry`.

For audit modularity, each Lean file redeclares the reduced-form `Mechanism`
structure locally. The files should therefore be read as independent formal
checks of corresponding algebraic and order-theoretic claims, not as a single
dependent formal development of the entire model.

## Status

- **57** theorem and lemma declarations across seven files in `DutchAuction/`.
- **1** retained `sorry`:
  `TwoSidedEntry.two_sided_equilibrium_existence`.
  This step requires Brouwer's fixed-point theorem and is treated as a
  Mathlib coverage gap rather than a mathematical gap in the manuscript.
- Toolchain: `leanprover/lean4:v4.29.0-rc8`.
- Mathlib pin: `master-2026-03-29`.

## File-to-paper mapping

| File | Paper results covered |
|------|-----------------------|
| `Basic.lean` | Core definitions: `Mechanism` structure, entry cutoffs, equilibrium maps, revenue and welfare functionals. |
| `Microfoundation.lean` | Propositions 3–7 (volume accounting, CRS congestion and volume monotonicity, Dutch-vs-batch and Dutch-vs-immediate dominance conditions, convex-hazard timing comparison). |
| `DriverEntry.lean` | Lemmas 1–2, Theorem 1, Corollary 1: one-sided driver entry; driver-attractiveness decomposition; four-case sign analysis on the driver side. |
| `TwoSidedEntry.lean` | Lemmas 3–4, Theorem 2, Corollaries 2–4: rider-attractiveness decomposition; two-sided entry map monotonicity; two-sided Dutch entry dominance; propagation; volume and revenue comparisons; rider-side four-case analysis. The existence step (Proposition 2) is the retained `sorry`. |
| `Revenue.lean` | Proposition 13, Corollary 5, Theorem 3, Corollary 6: Dutch price bounds and dominance; one-sided and two-sided revenue dominance; three-channel revenue decomposition. |
| `Welfare.lean` | Propositions 14–17, Corollary 7: welfare at fixed thickness; welfare dominance conditions; welfare vs. batch and immediate benchmarks; equilibrium welfare comparison with threshold `s**`. |
| `PaymentInequality.lean` | Front-loading payment inequality; the conditional `π_DA ≥ π_FPb` result under a trade-weighted-average premise; ARM-based dominance margin lower bound. |

## Build

```bash
cd lean4
lake build
```

A successful build completes with no errors and the single `sorry` warning at
`TwoSidedEntry.two_sided_equilibrium_existence`.

## Scope and known gaps

- The two-sided equilibrium existence theorem is retained as `sorry` because
  Brouwer's fixed-point theorem is not available in the Mathlib snapshot used
  here. The manuscript treats existence under the usual continuity-and-compact-
  convex-self-map hypotheses; Lean leaves that step as a transparent gap.
- The audit covers the algebraic and order-theoretic content of the entry,
  dominance, revenue, and welfare propositions, instantiated against named
  hypotheses. Primitive derivations of those hypotheses (e.g., a fully
  primitive proof of the front-loading payment inequality, or one-sided
  existence and uniqueness from continuity and self-map conditions) are
  outside the current scope.
