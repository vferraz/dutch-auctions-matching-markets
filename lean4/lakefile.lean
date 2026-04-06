import Lake
open Lake DSL

package DutchAuction where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"@"master-2026-03-29"

-- Each .lean file is self-contained (for Aristotle).
-- We build them as independent roots under a single library.
@[default_target]
lean_lib DutchAuction where
  srcDir := "DutchAuction"
  roots := #[`Basic, `Microfoundation, `DriverEntry, `TwoSidedEntry, `Revenue, `Welfare, `PaymentInequality]

