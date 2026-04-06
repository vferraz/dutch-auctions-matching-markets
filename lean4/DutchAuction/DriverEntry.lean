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
# One-Sided Driver Entry (Sections 5–6)

Lemmas 1–2, Theorem 1 (Dutch entry dominance), Corollary 1 (volume dominance).
-/

-- ============================================================
-- Definitions (self-contained for Aristotle)
-- ============================================================

structure Mechanism where
  q    : ℝ → ℝ → ℝ
  pi   : ℝ → ℝ → ℝ
  tau  : ℝ → ℝ → ℝ
  tauR : ℝ → ℝ → ℝ
  m    : ℝ → ℝ → ℝ
  pbar : ℝ → ℝ → ℝ

def c_bar (M : Mechanism) (lam : ℝ) (D R : ℝ) : ℝ :=
  M.q D R * M.pi D R - lam * M.tau D R

def Phi_D (M : Mechanism) (lam D_bar : ℝ) (F_C : ℝ → ℝ) (D R : ℝ) : ℝ :=
  D_bar * F_C (c_bar M lam D R)

-- ============================================================
-- Results
-- ============================================================

namespace DriverEntry

/-
PROBLEM
Lemma 1 (Timing advantage for FPb, `lem:timing-batch`):
    If DA concludes at first acceptance and FPb executes only at T,
    then τ_DA ≤ τ_FPb and τ^R_DA ≤ τ^R_FPb.

PROVIDED SOLUTION
Split into two conjuncts. For each D R, htau_DA gives DA.tau D R ≤ T and htau_FPb rewrites FPb.tau D R = T, so DA.tau D R ≤ FPb.tau D R. Similarly for tauR.
-/
theorem timing_advantage_batch
    (DA FPb : Mechanism) (T : ℝ)
    (htau_DA : ∀ D R, DA.tau D R ≤ T)
    (htauR_DA : ∀ D R, DA.tauR D R ≤ T)
    (htau_FPb : ∀ D R, FPb.tau D R = T)
    (htauR_FPb : ∀ D R, FPb.tauR D R = T) :
    (∀ D R, DA.tau D R ≤ FPb.tau D R) ∧
    (∀ D R, DA.tauR D R ≤ FPb.tauR D R) := by
  aesop

/-
PROBLEM
Lemma 2 (Driver-attractiveness decomposition, `lem:dominance-decomposition`):
    c̄_DA ≥ c̄_FP ⟺ λ(τ_FP - τ_DA) ≥ q_FP·π_FP - q_DA·π_DA.

PROVIDED SOLUTION
Unfold c_bar on both sides. The inequality c_bar DA ≥ c_bar FP becomes q_DA·π_DA - λ·τ_DA ≥ q_FP·π_FP - λ·τ_FP. Rearranging: λ·(τ_FP - τ_DA) ≥ q_FP·π_FP - q_DA·π_DA. This is a straightforward iff by linarith/ring after unfolding.
-/
theorem driver_attractiveness_decomposition
    (DA FP : Mechanism) (lam : ℝ) (D R : ℝ) :
    c_bar DA lam D R ≥ c_bar FP lam D R ↔
    lam * (FP.tau D R - DA.tau D R) ≥
    FP.q D R * FP.pi D R - DA.q D R * DA.pi D R := by
  unfold c_bar; constructor <;> intro h <;> linarith;

/-
PROBLEM
Theorem 1 (Dutch entry dominance, `thm:entry`):
    Under continuity, congestion monotonicity, and Dutch dominance
    at fixed thickness, the entry equilibrium is unique for each
    mechanism and D*_DA ≥ D*_FP.

PROVIDED SOLUTION
By contradiction. Suppose D_star_DA < D_star_FP. Since Φ_DA is decreasing: Phi_DA(D_star_FP) ≤ Phi_DA(D_star_DA) = D_star_DA. By dominance: Phi_FP(D_star_FP) ≤ Phi_DA(D_star_FP) ≤ D_star_DA < D_star_FP. But D_star_FP = Phi_FP(D_star_FP), contradiction. Use hdom, hdecr_DA, hfix_DA, hfix_FP and linarith.
-/
theorem dutch_entry_dominance
    (DA FP : Mechanism) (lam D_bar : ℝ) (F_C : ℝ → ℝ) (R : ℝ)
    (hD_bar_pos : D_bar > 0)
    -- Assumption 1 (Continuity): Φ_M continuous on [0, D̄]
    (hcont_DA : Continuous (fun D => Phi_D DA lam D_bar F_C D R))
    (hcont_FP : Continuous (fun D => Phi_D FP lam D_bar F_C D R))
    -- Assumption 4 (Congestion monotonicity): Φ_M weakly decreasing in D
    (hdecr_DA : ∀ D₁ D₂ : ℝ, D₁ ≤ D₂ →
                Phi_D DA lam D_bar F_C D₁ R ≥ Phi_D DA lam D_bar F_C D₂ R)
    (hdecr_FP : ∀ D₁ D₂ : ℝ, D₁ ≤ D₂ →
                Phi_D FP lam D_bar F_C D₁ R ≥ Phi_D FP lam D_bar F_C D₂ R)
    -- Assumption 2/3 (Dutch dominance at fixed thickness): Φ_DA ≥ Φ_FP
    (hdom : ∀ D : ℝ, Phi_D DA lam D_bar F_C D R ≥ Phi_D FP lam D_bar F_C D R)
    -- Equilibria as hypotheses (fixed points)
    (D_star_DA : ℝ)
    (hfix_DA : D_star_DA = Phi_D DA lam D_bar F_C D_star_DA R)
    (hD_DA_range : 0 ≤ D_star_DA ∧ D_star_DA ≤ D_bar)
    (D_star_FP : ℝ)
    (hfix_FP : D_star_FP = Phi_D FP lam D_bar F_C D_star_FP R)
    (hD_FP_range : 0 ≤ D_star_FP ∧ D_star_FP ≤ D_bar) :
    D_star_DA ≥ D_star_FP := by
  contrapose! hdom; contrapose! hdecr_DA; contrapose! hdecr_FP; (
  exact ⟨ D_star_DA, D_star_FP, hdom.le, by linarith [ hdecr_FP _ _ hdom.le, hdecr_DA D_star_DA, hdecr_DA D_star_FP ] ⟩);

/-
PROBLEM
Corollary 1 (Dutch weakly increases completed matches, `cor:volume`):
    Under Theorem 1 + volume monotonicity + fixed-thickness volume dominance,
    m_DA(D*_DA, R) ≥ m_FP(D*_FP, R).

PROVIDED SOLUTION
Chain: FP.m D_star_FP R ≤ DA.m D_star_FP R (by hvol_dom) ≤ DA.m D_star_DA R (by hvol_mono since D_star_FP ≤ D_star_DA from hentry). Use calc or linarith with these two facts.
-/
theorem dutch_volume_dominance
    (DA FP : Mechanism) (R : ℝ)
    (D_star_DA D_star_FP : ℝ)
    -- Entry dominance (from Theorem 1)
    (hentry : D_star_DA ≥ D_star_FP)
    -- Assumption 5 (Volume monotonicity): m_DA increasing in D
    (hvol_mono : ∀ D₁ D₂ : ℝ, D₁ ≤ D₂ → DA.m D₁ R ≤ DA.m D₂ R)
    -- Fixed-thickness volume dominance
    (hvol_dom : ∀ D : ℝ, DA.m D R ≥ FP.m D R) :
    DA.m D_star_DA R ≥ FP.m D_star_FP R := by
  exact le_trans ( hvol_dom _ ) ( hvol_mono _ _ hentry )

end DriverEntry

end