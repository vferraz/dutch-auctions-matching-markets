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
# Revenue Analysis (Section 9)

Props 10–13 (rider-side micro, price bounds), Theorem 3 (revenue dominance),
Corollaries 5–6.
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

def Rev (M : Mechanism) (alpha D R : ℝ) : ℝ :=
  alpha * M.m D R * M.pbar D R

-- ============================================================
-- Results
-- ============================================================

namespace Revenue

/-- Proposition 13 (Dutch price bounds, `prop:price-bounds`):
    The expected rider-paid price under DA satisfies
    p₀·e^{-δT} ≤ p̄_DA ≤ p₀. -/
theorem dutch_price_bounds
    (DA : Mechanism) (p0 pmin : ℝ) (D R : ℝ)
    -- p̄_DA is a weighted average of clock prices in [pmin, p0]
    (hpbar_le : DA.pbar D R ≤ p0)
    (hpbar_ge : DA.pbar D R ≥ pmin) :
    pmin ≤ DA.pbar D R ∧ DA.pbar D R ≤ p0 := by
  exact ⟨hpbar_ge, hpbar_le⟩

/-
PROBLEM
Corollary 5 (Sufficient condition for Dutch price dominance, `cor:price-dominance`):
    If the minimum clock price exceeds the posted price, p̄_DA ≥ p̄.

PROVIDED SOLUTION
From hfloor: pmin ≥ pbar_FP, and hpbar_ge: DA.pbar D R ≥ pmin. By transitivity: DA.pbar D R ≥ pmin ≥ pbar_FP. Use linarith.
-/
theorem dutch_price_dominance
    (DA : Mechanism) (pbar_FP pmin : ℝ) (D R : ℝ)
    -- Floor exceeds posted price
    (hfloor : pmin ≥ pbar_FP)
    -- DA price bounded below by floor
    (hpbar_ge : DA.pbar D R ≥ pmin) :
    DA.pbar D R ≥ pbar_FP := by
  -- By transitivity of inequalities, if $pmin \geq pbar_FP$ and $DA.pbar D R \geq pmin$, then $DA.pbar D R \geq pbar_FP$.
  apply le_trans hfloor hpbar_ge

/-
PROBLEM
Theorem 3 (Revenue dominance, `thm:revenue`), one-sided case:
    Under (i) driver-side dominance, (ii) price non-deterioration,
    (iii) volume monotonicity: Rev_DA ≥ Rev_FP.

PROVIDED SOLUTION
Unfold Rev. Need α·m_DA·p̄_DA ≥ α·m_FP·p̄_FP. Since α > 0, suffices m_DA·p̄_DA ≥ m_FP·p̄_FP. We have m_DA ≥ m_FP ≥ 0 and p̄_DA ≥ p̄_FP ≥ 0. So m_DA·p̄_DA ≥ m_FP·p̄_DA ≥ m_FP·p̄_FP. Use nlinarith with hvol, hprice, hm_pos, hp_pos, halpha.
-/
theorem revenue_dominance_one_sided
    (DA FP : Mechanism) (alpha R : ℝ)
    (D_star_DA D_star_FP : ℝ)
    (halpha : alpha > 0)
    -- (i) Entry dominance (from Theorem 1)
    (hentry : D_star_DA ≥ D_star_FP)
    -- (ii) Price non-deterioration
    (hprice : DA.pbar D_star_DA R ≥ FP.pbar D_star_FP R)
    -- (iii) Volume monotonicity + fixed-thickness dominance → volume dominance
    (hvol : DA.m D_star_DA R ≥ FP.m D_star_FP R)
    -- Non-negativity
    (hm_pos : FP.m D_star_FP R ≥ 0)
    (hp_pos : FP.pbar D_star_FP R ≥ 0) :
    Rev DA alpha D_star_DA R ≥ Rev FP alpha D_star_FP R := by
  unfold Rev;
  gcongr ; nlinarith [ mul_le_mul_of_nonneg_left hprice halpha.le, mul_le_mul_of_nonneg_left hvol halpha.le ] ;

/-
PROBLEM
Theorem 3, two-sided extension:
    When rider entry is endogenous, the argument uses Theorem 2
    for entry dominance in both D and R.

PROVIDED SOLUTION
Same as one_sided: unfold Rev. Need α·m_DA·p̄_DA ≥ α·m_FP·p̄_FP. Since α > 0, suffices m_DA·p̄_DA ≥ m_FP·p̄_FP. We have m_DA ≥ m_FP ≥ 0 and p̄_DA ≥ p̄_FP ≥ 0. Use nlinarith.
-/
theorem revenue_dominance_two_sided
    (DA FP : Mechanism) (alpha : ℝ)
    (D_star_DA R_star_DA D_star_FP R_star_FP : ℝ)
    (halpha : alpha > 0)
    -- Two-sided entry dominance
    (hentry_D : D_star_DA ≥ D_star_FP)
    (hentry_R : R_star_DA ≥ R_star_FP)
    -- Price non-deterioration
    (hprice : DA.pbar D_star_DA R_star_DA ≥ FP.pbar D_star_FP R_star_FP)
    -- Volume dominance (from Corollary 3)
    (hvol : DA.m D_star_DA R_star_DA ≥ FP.m D_star_FP R_star_FP)
    -- Non-negativity
    (hm_pos : FP.m D_star_FP R_star_FP ≥ 0)
    (hp_pos : FP.pbar D_star_FP R_star_FP ≥ 0) :
    Rev DA alpha D_star_DA R_star_DA ≥
    Rev FP alpha D_star_FP R_star_FP := by
  unfold Rev;
  nlinarith [ mul_le_mul_of_nonneg_left hprice halpha.le, mul_le_mul_of_nonneg_left hvol halpha.le, mul_le_mul_of_nonneg_left hp_pos halpha.le, mul_le_mul_of_nonneg_left hm_pos halpha.le ]

/-
PROBLEM
Corollary 6 (Revenue lower bound, `cor:rev-lower-bound`):
    D*_DA / D*_FP ≤ Rev_DA / Rev_FP (entry advantage is a lower bound).
    Requires q_FP > 0 to ensure Rev_FP > 0.

PROVIDED SOLUTION
Show Rev_FP > 0, clear denominators with field_simp, then nlinarith.
-/
theorem revenue_lower_bound
    (DA FP : Mechanism) (alpha : ℝ)
    (D_star_DA R_star_DA D_star_FP R_star_FP : ℝ)
    (halpha : alpha > 0)
    (hrev_DA : Rev DA alpha D_star_DA R_star_DA ≥
               Rev FP alpha D_star_FP R_star_FP)
    (hprice : DA.pbar D_star_DA R_star_DA ≥ FP.pbar D_star_FP R_star_FP)
    (hD_FP_pos : D_star_FP > 0)
    (hp_FP_pos : FP.pbar D_star_FP R_star_FP > 0)
    (hm_DA : DA.m D_star_DA R_star_DA = D_star_DA * DA.q D_star_DA R_star_DA)
    (hm_FP : FP.m D_star_FP R_star_FP = D_star_FP * FP.q D_star_FP R_star_FP)
    (hq_ge : DA.q D_star_DA R_star_DA ≥ FP.q D_star_FP R_star_FP)
    (hq_FP_pos : FP.q D_star_FP R_star_FP > 0) :
    D_star_DA / D_star_FP ≤
    Rev DA alpha D_star_DA R_star_DA / Rev FP alpha D_star_FP R_star_FP := by
  have h_rev_pos : Rev FP alpha D_star_FP R_star_FP > 0 := by
    exact mul_pos ( mul_pos halpha ( by nlinarith ) ) hp_FP_pos;
  field_simp;
  unfold Rev at *;
  by_cases hD_DA_pos : D_star_DA > 0 <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
  · nlinarith [ mul_le_mul_of_nonneg_left hprice hq_FP_pos.le, mul_le_mul_of_nonneg_left hq_ge hp_FP_pos.le ];
  · nlinarith [ mul_pos hD_FP_pos ( mul_pos hq_FP_pos hp_FP_pos ) ]

/-
Theorem 3 revenue decomposition (`eq:three-channel`):
    Rev_DA / Rev_FP = (D*_DA / D*_FP) · (q_DA / q_FP) · (p̄_DA / p̄_FP).
    This follows from Rev_M = α · m_M · p̄_M = α · D · q_M · p̄_M.
-/
theorem revenue_three_channel_decomposition
    (DA FP : Mechanism) (alpha : ℝ)
    (D_star_DA R_star_DA D_star_FP R_star_FP : ℝ)
    (halpha : alpha > 0)
    (hD_FP_pos : D_star_FP > 0)
    (hq_FP_pos : FP.q D_star_FP R_star_FP > 0)
    (hp_FP_pos : FP.pbar D_star_FP R_star_FP > 0)
    (hm_DA : DA.m D_star_DA R_star_DA = D_star_DA * DA.q D_star_DA R_star_DA)
    (hm_FP : FP.m D_star_FP R_star_FP = D_star_FP * FP.q D_star_FP R_star_FP) :
    Rev DA alpha D_star_DA R_star_DA / Rev FP alpha D_star_FP R_star_FP =
    (D_star_DA / D_star_FP) *
    (DA.q D_star_DA R_star_DA / FP.q D_star_FP R_star_FP) *
    (DA.pbar D_star_DA R_star_DA / FP.pbar D_star_FP R_star_FP) := by
  unfold Rev;
  grind

end Revenue

end