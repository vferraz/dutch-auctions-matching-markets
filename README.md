# Dutch Auctions in Matching Markets with Waiting Costs

**Pitz & Ferraz (2026)**

This repository contains the code and formal verification materials for "Dutch Auctions in Matching Markets with Waiting Costs."

## Structure

### `lean4/`

Canonical Lean 4 formalization of the paper's theoretical results, built against Mathlib.

**Status:** All theorems are fully verified except for `two_sided_equilibrium_existence` in `TwoSidedEntry.lean`, which contains one remaining `sorry`. This proof requires a Brouwer fixed-point theorem that is not yet available in current Mathlib.

### `code/`

Public replication materials:

- `lib.py` — shared library of model primitives and numerical routines
- `script_figures_quant.py` — generates the three story figures used in the paper
- `paper_figures/` — the shipped PNG figures (story figures 1--3)
- `sims/` — simulation runs:
  - `baseline_controlled_thickness/` — baseline simulation with controlled market thickness
  - `controlled_thickness_variants/` — parameter variants
  - `controlled_thickness_variants_v2_cli/` — CLI-based variant runs

## Note

The paper source (LaTeX) is not included in this repository.
