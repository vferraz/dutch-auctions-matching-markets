import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-!
# Basic Definitions for Dutch Auction TEV Framework

Core definitions shared across all files. Each theorem file redeclares the
definitions it needs for Aristotle compatibility.

Paper: "Dutch Clock Trading vs. Posted Prices in Time-Sensitive Matching Markets"
(Pitz & Ferraz, 2026), v11.
-/

/-- A reduced-form mechanism in a matching market, characterized by six
    measurable objects as functions of market thickness (D, R).
    Paper reference: Section 2, equations (4)-(6). -/
structure Mechanism where
  /-- Driver match probability q_M(D,R) ∈ [0,1]. -/
  q    : ℝ → ℝ → ℝ
  /-- Expected driver payment conditional on match π_M(D,R) ≥ 0. -/
  pi   : ℝ → ℝ → ℝ
  /-- Expected driver time-to-contract τ_M(D,R) ≥ 0. -/
  tau  : ℝ → ℝ → ℝ
  /-- Expected rider time-to-contract τ^R_M(D,R) ≥ 0. -/
  tauR : ℝ → ℝ → ℝ
  /-- Expected match volume per session m_M(D,R) ≥ 0. -/
  m    : ℝ → ℝ → ℝ
  /-- Expected rider-paid transaction price conditional on match p̄_M(D,R) ≥ 0. -/
  pbar : ℝ → ℝ → ℝ

/-- Driver-entry cutoff: c̄_M(D,R) = q_M · π_M - λ · τ_M.
    A driver enters iff c ≤ c̄_M. Paper Eq. (7), line ~520 of v11. -/
def c_bar (M : Mechanism) (lam : ℝ) (D R : ℝ) : ℝ :=
  M.q D R * M.pi D R - lam * M.tau D R

/-- Rider match probability from accounting identity: q^R_M = m_M / R.
    Paper Prop. 10, Eq. (26), line ~2248. -/
def qR (M : Mechanism) (D R : ℝ) : ℝ :=
  M.m D R / R

/-- Rider-entry cutoff: v̄_M(D,R) = p̄_M + κ · τ^R_M / q^R_M.
    A rider enters iff v ≥ v̄_M. Paper Eq. (18), line ~1692. -/
def v_bar (M : Mechanism) (kap : ℝ) (D R : ℝ) : ℝ :=
  M.pbar D R + kap * M.tauR D R / (qR M D R)

/-- Driver-side entry map: Φ^D_M(D,R) = D̄ · F_C(c̄_M(D,R)).
    Paper Eq. (12), line ~1427. -/
def Phi_D (M : Mechanism) (lam D_bar : ℝ) (F_C : ℝ → ℝ) (D R : ℝ) : ℝ :=
  D_bar * F_C (c_bar M lam D R)

/-- Rider-side entry map: Φ^R_M(D,R) = R̄ · F̄_V(v̄_M(D,R)).
    Paper Eq. (22), line ~1717. -/
def Phi_R (M : Mechanism) (kap R_bar : ℝ) (F_V_bar : ℝ → ℝ) (D R : ℝ) : ℝ :=
  R_bar * F_V_bar (v_bar M kap D R)

/-- Platform revenue: Rev_M = α · m_M · p̄_M.
    Paper Eq. (25), line ~2417. -/
def Rev (M : Mechanism) (alpha D R : ℝ) : ℝ :=
  alpha * M.m D R * M.pbar D R

/-- Welfare at fixed thickness: W_M(D,R) = m·s - λ·D·τ - κ·R·τ^R.
    Paper Prop. 14, line ~2819. -/
def Welfare (M : Mechanism) (s lam kap D R : ℝ) : ℝ :=
  M.m D R * s - lam * D * M.tau D R - kap * R * M.tauR D R

/-- Aggregate waiting-cost change at equilibrium: Δ_wait.
    Paper Eq. (29), line ~2965 of v11. -/
def Delta_wait (DA FP : Mechanism) (lam kap D1 R1 D2 R2 : ℝ) : ℝ :=
  lam * (D1 * DA.tau D1 R1 - D2 * FP.tau D2 R2) +
  kap * (R1 * DA.tauR D1 R1 - R2 * FP.tauR D2 R2)

end
