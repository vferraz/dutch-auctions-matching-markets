# Summary of changes
## Changes made

### 1. `DutchAuction/TwoSidedEntry.lean` — `rider_batch_dominance` updated ✅

The theorem statement already had the correct conditional form (with the dominance hypothesis `hdom`), matching the revised Proposition 13(b). The changes were:

- **Docstring revised**: Removed the stale "p̄_DA ≥ p̄_FPb (payment inequality)" language from the old unconditional version. The docstring now accurately describes the conditional κ > κ₀ result and explains why the dominance condition is needed.
- **Proof replaced**: The old proof (`field_simp` + `nlinarith`) had broken (likely due to a Mathlib `field_simp` behavior change). The new proof uses `unfold v_bar; rw [← hqR_eq, add_div', add_div']; rw [div_lt_div_iff_of_pos_right]; linarith`.

### 2. `ARISTOTLE_SUMMARY_*.md` refreshed ✅

- The `rider_batch_dominance` entry now explicitly describes it as a **conditional** result requiring `(p̄_DA − p̄_FPb) · q^R < κ · (τ^R_FPb − τ^R_DA)`, not the old unconditional `κ > 0` claim.
- Added a **Revision log** table recording the 2026-04-07 change and its reason (paper math-consistency pass).

### Build status

`lake build TwoSidedEntry` succeeds (8026 jobs, no errors). The only `sorry` in the file is `two_sided_equilibrium_existence` (line 253) — the out-of-scope Brouwer fixed-point theorem, which is intentionally preserved and unchanged.

### Summary of what was NOT changed

- No `.tex` files touched
- `two_sided_equilibrium_existence` sorry unchanged
- All other theorems, definitions, imports, namespaces, and file structure preserved
- No unrelated theorems refactored