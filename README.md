# Dutch Auctions in Matching Markets with Waiting Costs

Code and Lean formalization for the project by Thomas Pitz and Vinicius Ferraz.

## Overview

This repository contains two public components of the project:

- `code/`: numerical code, simulation outputs, and quantitative paper figures
- `lean4/`: Lean 4 formalization of the paper's theoretical results

The repository is organized as a compact public companion for the project rather than a full private research workspace.

## Repository Structure

### `code/`

`code/` contains the numerical and figure-generation side of the project.

- `lib.py`
  Core model primitives and numerical routines used across the codebase.
- `script_figures_quant.py`
  Main script for generating the quantitative story figures.
- `paper_figures/`
  Exported figure files currently used in the paper.
- `sims/baseline_controlled_thickness/`
  Baseline controlled-thickness simulation and outputs.
- `sims/controlled_thickness_variants/`
  Controlled-thickness parameter variants and archived outputs.
- `sims/controlled_thickness_variants_v2_cli/`
  CLI-based variant runs and associated outputs.

### `lean4/`

`lean4/` is the canonical Lean 4 formalization for the project.

- `DutchAuction/`
  Main Lean source files.
- `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`
  Lean/Lake project configuration.
- `ARISTOTLE_SUMMARY_*.md`
  Record of the automated proof-filling pass.

Current status:

- the formalization builds successfully with `lake build`
- one theorem remains incomplete:
  - `DutchAuction/TwoSidedEntry.lean`
  - `two_sided_equilibrium_existence`
- this remaining gap is tied to Brouwer-style fixed-point support in the current Mathlib stack

## Quick Start

### Generate the quantitative figures

```bash
cd code
python3 script_figures_quant.py
```

### Build the Lean formalization

```bash
cd lean4
lake build
```

## Notes

- The three PNGs in `code/paper_figures/` are the current exported story figures.
- The Lean directory is the current best verified version of the formalization.
