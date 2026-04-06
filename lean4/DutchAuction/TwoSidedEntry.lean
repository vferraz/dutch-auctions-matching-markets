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
# Two-Sided Entry Equilibrium (Sections 7–8)

Lemmas 3–4, Definition 1, Theorem 2 (two-sided Dutch entry dominance),
Corollaries 2–4.
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

def qR (M : Mechanism) (D R : ℝ) : ℝ :=
  M.m D R / R

def v_bar (M : Mechanism) (kap : ℝ) (D R : ℝ) : ℝ :=
  M.pbar D R + kap * M.tauR D R / (qR M D R)

def Phi_D (M : Mechanism) (lam D_bar : ℝ) (F_C : ℝ → ℝ) (D R : ℝ) : ℝ :=
  D_bar * F_C (c_bar M lam D R)

def Phi_R (M : Mechanism) (kap R_bar : ℝ) (F_V_bar : ℝ → ℝ) (D R : ℝ) : ℝ :=
  R_bar * F_V_bar (v_bar M kap D R)

def Rev (M : Mechanism) (alpha D R : ℝ) : ℝ :=
  alpha * M.m D R * M.pbar D R

-- ============================================================
-- Results
-- ============================================================

namespace TwoSidedEntry

/-
PROBLEM
Lemma 3 (Rider-attractiveness dominance, `lem:rider-dominance`):
    Dutch attracts weakly more riders at fixed thickness iff
    (p̄_FP - p̄_DA) + κ[τ^R_FP/q^R_FP - τ^R_DA/q^R_DA] ≥ 0.

PROVIDED SOLUTION
Unfold v_bar and qR. The inequality v_bar DA ≤ v_bar FP expands to pbar_DA + κ·τR_DA/qR_DA ≤ pbar_FP + κ·τR_FP/qR_FP. Rearranging: (pbar_FP - pbar_DA) + κ·(τR_FP/qR_FP - τR_DA/qR_DA) ≥ 0. This is direct by constructor <;> intro h <;> linarith or simp [v_bar, qR] and linarith.
-/
theorem rider_attractiveness_decomposition
    (DA FP : Mechanism) (kap : ℝ) (D R : ℝ) :
    v_bar DA kap D R ≤ v_bar FP kap D R ↔
    (FP.pbar D R - DA.pbar D R) +
    kap * (FP.tauR D R / (qR FP D R) - DA.tauR D R / (qR DA D R)) ≥ 0 := by
  unfold v_bar;
  grind

/-
PROBLEM
Lemma 4 (Monotonicity of the two-sided entry map, `lem:two-sided-monotone`):
    Under congestion, rider congestion, and cross-side complementarity
    (with D̄ ≥ 0, R̄ ≥ 0), the four-part monotonicity structure holds.

PROVIDED SOLUTION
Split into 4 conjuncts using mul_le_mul_of_nonneg_left.
-/
theorem two_sided_entry_map_monotonicity
    (M : Mechanism) (lam kap D_bar R_bar : ℝ) (F_C F_V_bar : ℝ → ℝ)
    (hF_C_mono : Monotone F_C)
    (hF_V_bar_anti : Antitone F_V_bar)
    (hD_bar_nonneg : D_bar ≥ 0)
    (hR_bar_nonneg : R_bar ≥ 0)
    (hcong_D : ∀ D₁ D₂ R, D₁ ≤ D₂ → c_bar M lam D₁ R ≥ c_bar M lam D₂ R)
    (hcong_R : ∀ D R₁ R₂, R₁ ≤ R₂ → v_bar M kap D R₁ ≤ v_bar M kap D R₂)
    (hcross_i : ∀ D R₁ R₂, R₁ ≤ R₂ → c_bar M lam D R₁ ≤ c_bar M lam D R₂)
    (hcross_ii : ∀ D₁ D₂ R, D₁ ≤ D₂ → v_bar M kap D₁ R ≥ v_bar M kap D₂ R) :
    (∀ D₁ D₂ R, D₁ ≤ D₂ →
      Phi_D M lam D_bar F_C D₁ R ≥ Phi_D M lam D_bar F_C D₂ R) ∧
    (∀ D R₁ R₂, R₁ ≤ R₂ →
      Phi_D M lam D_bar F_C D R₁ ≤ Phi_D M lam D_bar F_C D R₂) ∧
    (∀ D R₁ R₂, R₁ ≤ R₂ →
      Phi_R M kap R_bar F_V_bar D R₁ ≥ Phi_R M kap R_bar F_V_bar D R₂) ∧
    (∀ D₁ D₂ R, D₁ ≤ D₂ →
      Phi_R M kap R_bar F_V_bar D₁ R ≤ Phi_R M kap R_bar F_V_bar D₂ R) := by
  refine' ⟨ fun D₁ D₂ R h => _, fun D R₁ R₂ h => _, fun D R₁ R₂ h => _, fun D₁ D₂ R h => _ ⟩;
  · exact mul_le_mul_of_nonneg_left ( hF_C_mono ( hcong_D _ _ _ h ) ) hD_bar_nonneg;
  · exact mul_le_mul_of_nonneg_left ( hF_C_mono ( hcross_i D R₁ R₂ h ) ) hD_bar_nonneg;
  · exact mul_le_mul_of_nonneg_left ( hF_V_bar_anti ( hcong_R _ _ _ h ) ) hR_bar_nonneg;
  · exact mul_le_mul_of_nonneg_left ( hF_V_bar_anti ( hcross_ii _ _ _ h ) ) hR_bar_nonneg

/-
PROBLEM
Theorem 2 (Two-sided Dutch entry dominance, `thm:two-sided-entry`):
    The DA equilibrium is the greatest fixed point of Φ_DA (Topkis).
    Any sub-fixed-point of Φ_DA is dominated by the DA equilibrium.
    Since Φ_DA ≥ Φ_FP (outward shift), the FP equilibrium is a
    sub-fixed-point, hence D*_DA ≥ D*_FP and R*_DA ≥ R*_FP.

PROVIDED SOLUTION
Apply hgreatest_DA to (D*_FP, R*_FP) using the outward shift and FP fixed-point equations.
-/
theorem two_sided_dutch_entry_dominance
    (DA FP : Mechanism) (lam kap D_bar R_bar : ℝ)
    (F_C F_V_bar : ℝ → ℝ)
    (hdom_D : ∀ D R, c_bar DA lam D R ≥ c_bar FP lam D R)
    (hdom_R : ∀ D R, v_bar DA kap D R ≤ v_bar FP kap D R)
    (hF_C_mono : Monotone F_C)
    (hF_V_bar_anti : Antitone F_V_bar)
    (hshift_D : ∀ D R,
      Phi_D DA lam D_bar F_C D R ≥ Phi_D FP lam D_bar F_C D R)
    (hshift_R : ∀ D R,
      Phi_R DA kap R_bar F_V_bar D R ≥ Phi_R FP kap R_bar F_V_bar D R)
    (D_star_DA R_star_DA : ℝ)
    (hfix_DA_D : D_star_DA = Phi_D DA lam D_bar F_C D_star_DA R_star_DA)
    (hfix_DA_R : R_star_DA = Phi_R DA kap R_bar F_V_bar D_star_DA R_star_DA)
    (D_star_FP R_star_FP : ℝ)
    (hfix_FP_D : D_star_FP = Phi_D FP lam D_bar F_C D_star_FP R_star_FP)
    (hfix_FP_R : R_star_FP = Phi_R FP kap R_bar F_V_bar D_star_FP R_star_FP)
    -- Topkis: DA equilibrium dominates any sub-fixed-point of Φ_DA
    (hgreatest_DA : ∀ D' R',
      D' ≤ Phi_D DA lam D_bar F_C D' R' →
      R' ≤ Phi_R DA kap R_bar F_V_bar D' R' →
      D' ≤ D_star_DA ∧ R' ≤ R_star_DA) :
    D_star_DA ≥ D_star_FP ∧ R_star_DA ≥ R_star_FP := by
  exact hgreatest_DA _ _ ( by linarith [ hshift_D D_star_FP R_star_FP ] ) ( by linarith [ hshift_R D_star_FP R_star_FP ] ) |> fun h => ⟨ h.1, h.2 ⟩

/-
PROBLEM
Corollary 2 (Driver-side dominance propagates to riders, `cor:propagation`):
    With fixed-point equations, rider-side congestion monotonicity, and
    cross-side outward shift, driver-side entry dominance propagates to riders.

PROVIDED SOLUTION
By contradiction using the one-sided contraction argument on the rider-side entry map.
-/
theorem driver_dominance_propagates
    (DA FP : Mechanism) (kap R_bar : ℝ) (F_V_bar : ℝ → ℝ)
    (D_star_DA R_star_DA D_star_FP R_star_FP : ℝ)
    (hentry_D : D_star_DA ≥ D_star_FP)
    -- Cross-side effect strong enough at equilibrium driver masses
    (hprop : ∀ R, v_bar DA kap D_star_DA R ≤ v_bar FP kap D_star_FP R)
    (hF_V_bar_anti : Antitone F_V_bar)
    (hR_bar_nonneg : R_bar ≥ 0)
    -- Fixed-point equations
    (hfix_DA_R : R_star_DA = Phi_R DA kap R_bar F_V_bar D_star_DA R_star_DA)
    (hfix_FP_R : R_star_FP = Phi_R FP kap R_bar F_V_bar D_star_FP R_star_FP)
    -- Φ^R_DA is decreasing in R (congestion on rider side)
    (hdecr_DA : ∀ R₁ R₂,
      R₁ ≤ R₂ → Phi_R DA kap R_bar F_V_bar D_star_DA R₁ ≥
                 Phi_R DA kap R_bar F_V_bar D_star_DA R₂)
    (hdecr_FP : ∀ R₁ R₂,
      R₁ ≤ R₂ → Phi_R FP kap R_bar F_V_bar D_star_FP R₁ ≥
                 Phi_R FP kap R_bar F_V_bar D_star_FP R₂)
    -- Outward shift from cross-side effect
    (hshift_R : ∀ R,
      Phi_R DA kap R_bar F_V_bar D_star_DA R ≥
      Phi_R FP kap R_bar F_V_bar D_star_FP R) :
    R_star_DA ≥ R_star_FP := by
  by_contra h_contra;
  linarith [ hshift_R R_star_FP, hdecr_DA _ _ ( le_of_not_ge h_contra ), hdecr_FP _ _ ( le_of_not_ge h_contra ) ]

/-
PROBLEM
Corollary 3 (Two-sided volume dominance, `cor:two-sided-volume`):
    Under Theorem 2 conditions + volume increasing in both D and R
    + fixed-thickness volume dominance,
    m_DA(D*_DA, R*_DA) ≥ m_FP(D*_FP, R*_FP).

PROVIDED SOLUTION
Chain: FP.m D*_FP R*_FP ≤ DA.m D*_FP R*_FP (by hvol_dom) ≤ DA.m D*_DA R*_FP (by hvol_mono_D since D*_FP ≤ D*_DA) ≤ DA.m D*_DA R*_DA (by hvol_mono_R since R*_FP ≤ R*_DA). Use calc or linarith with these three facts.
-/
theorem two_sided_volume_dominance
    (DA FP : Mechanism)
    (D_star_DA R_star_DA D_star_FP R_star_FP : ℝ)
    -- Entry dominance (from Theorem 2)
    (hentry_D : D_star_DA ≥ D_star_FP)
    (hentry_R : R_star_DA ≥ R_star_FP)
    -- Volume monotonicity in both D and R
    (hvol_mono_D : ∀ D₁ D₂ R, D₁ ≤ D₂ → DA.m D₁ R ≤ DA.m D₂ R)
    (hvol_mono_R : ∀ D R₁ R₂, R₁ ≤ R₂ → DA.m D R₁ ≤ DA.m D R₂)
    -- Fixed-thickness volume dominance
    (hvol_dom : ∀ D R, DA.m D R ≥ FP.m D R) :
    DA.m D_star_DA R_star_DA ≥ FP.m D_star_FP R_star_FP := by
  exact le_trans ( hvol_dom _ _ ) ( le_trans ( hvol_mono_R _ _ _ hentry_R ) ( hvol_mono_D _ _ _ hentry_D ) )

/-
PROBLEM
Corollary 4 (Two-sided revenue comparison, `cor:two-sided-revenue`):
    Dutch yields weakly higher revenue whenever
    m_DA/m_FP ≥ p̄_FP/p̄_DA.

PROVIDED SOLUTION
Unfold Rev. Rev DA = α · m_DA · p̄_DA and Rev FP = α · m_FP · p̄_FP. Since α > 0, it suffices to show m_DA · p̄_DA ≥ m_FP · p̄_FP, which is exactly hvol. Use mul_le_mul_of_nonneg_left hvol (le_of_lt halpha).
-/
theorem two_sided_revenue_comparison
    (DA FP : Mechanism) (alpha : ℝ)
    (D_star_DA R_star_DA D_star_FP R_star_FP : ℝ)
    (halpha : alpha > 0)
    (hvol : DA.m D_star_DA R_star_DA * DA.pbar D_star_DA R_star_DA ≥
            FP.m D_star_FP R_star_FP * FP.pbar D_star_FP R_star_FP) :
    Rev DA alpha D_star_DA R_star_DA ≥ Rev FP alpha D_star_FP R_star_FP := by
  unfold Rev; nlinarith;

/-
PROBLEM
Proposition 2 (Two-sided equilibrium existence, `prop:two-sided-existence`):
    The map Φ_M : [0, D̄] × [0, R̄] → [0, D̄] × [0, R̄] is continuous
    and maps a compact convex set to itself. By Brouwer's fixed-point
    theorem, a fixed point (D*, R*) exists.

PROVIDED SOLUTION
Apply BrouwerFixedPoint or IsCompact.exists_fixedPoint_of_continuous
from Mathlib. The hypotheses hrange_D and hrange_R ensure the map sends
[0,D̄]×[0,R̄] into itself; continuity + compactness + convexity give Brouwer.
-/
theorem two_sided_equilibrium_existence
    (M : Mechanism) (lam kap D_bar R_bar : ℝ) (F_C F_V_bar : ℝ → ℝ)
    (hD_bar_pos : D_bar > 0) (hR_bar_pos : R_bar > 0)
    (hcont : Continuous (fun p : ℝ × ℝ =>
      (Phi_D M lam D_bar F_C p.1 p.2, Phi_R M kap R_bar F_V_bar p.1 p.2)))
    (hrange_D : ∀ D R, 0 ≤ D → D ≤ D_bar → 0 ≤ R → R ≤ R_bar →
      0 ≤ Phi_D M lam D_bar F_C D R ∧ Phi_D M lam D_bar F_C D R ≤ D_bar)
    (hrange_R : ∀ D R, 0 ≤ D → D ≤ D_bar → 0 ≤ R → R ≤ R_bar →
      0 ≤ Phi_R M kap R_bar F_V_bar D R ∧ Phi_R M kap R_bar F_V_bar D R ≤ R_bar) :
    ∃ D_star R_star,
      0 ≤ D_star ∧ D_star ≤ D_bar ∧
      0 ≤ R_star ∧ R_star ≤ R_bar ∧
      D_star = Phi_D M lam D_bar F_C D_star R_star ∧
      R_star = Phi_R M kap R_bar F_V_bar D_star R_star := by
  sorry

/-
Proposition 3 (Two-sided equilibrium uniqueness, `prop:two-sided-unique`):
    If Φ_M is a contraction in the ℓ¹ norm (spectral radius < 1),
    any two fixed points must coincide.
-/
theorem two_sided_equilibrium_uniqueness
    (M : Mechanism) (lam kap D_bar R_bar : ℝ) (F_C F_V_bar : ℝ → ℝ)
    (D₁ R₁ D₂ R₂ : ℝ)
    (hfix₁_D : D₁ = Phi_D M lam D_bar F_C D₁ R₁)
    (hfix₁_R : R₁ = Phi_R M kap R_bar F_V_bar D₁ R₁)
    (hfix₂_D : D₂ = Phi_D M lam D_bar F_C D₂ R₂)
    (hfix₂_R : R₂ = Phi_R M kap R_bar F_V_bar D₂ R₂)
    (k : ℝ) (hk : k < 1) (hk_nonneg : k ≥ 0)
    (hcontraction :
      |Phi_D M lam D_bar F_C D₁ R₁ - Phi_D M lam D_bar F_C D₂ R₂| +
      |Phi_R M kap R_bar F_V_bar D₁ R₁ - Phi_R M kap R_bar F_V_bar D₂ R₂| ≤
      k * (|D₁ - D₂| + |R₁ - R₂|)) :
    D₁ = D₂ ∧ R₁ = R₂ := by
  -- By the properties of absolute values and the contraction condition, we can deduce that $|D_1 - D_2| + |R_1 - R_2| = 0$.
  have hsum_zero : abs (D₁ - D₂) + abs (R₁ - R₂) = 0 := by
    exact le_antisymm ( le_of_not_gt fun h => by cases abs_cases ( D₁ - D₂ ) <;> cases abs_cases ( R₁ - R₂ ) <;> cases abs_cases ( Phi_D M lam D_bar F_C D₁ R₁ - Phi_D M lam D_bar F_C D₂ R₂ ) <;> cases abs_cases ( Phi_R M kap R_bar F_V_bar D₁ R₁ - Phi_R M kap R_bar F_V_bar D₂ R₂ ) <;> nlinarith ) ( by positivity );
  grind

/-
Proposition 4(a) (Rider match probability accounting, `prop:rider-micro`, `eq:qR-micro`):
    Under m_M = D · q_M, the rider match probability satisfies
    q^R_M = m_M / R = D · q_M / R.
-/
theorem rider_match_prob_accounting
    (M : Mechanism) (D R : ℝ)
    (hm : M.m D R = D * M.q D R) :
    qR M D R = D * M.q D R / R := by
  exact hm ▸ rfl

/-
Proposition 4(a) (Batch rider cutoff, `prop:rider-micro`, `eq:vbar-FPb-micro`):
    Since τ^R_FPb = T (batch clears at session end), the rider entry cutoff
    simplifies to v̄_FPb = p̄ + κ · T / q^R_FPb.
    This connects the general v_bar definition to the Poisson batch formula.
-/
theorem batch_rider_cutoff
    (FPb : Mechanism) (kap T : ℝ) (D R : ℝ)
    (htauR_batch : FPb.tauR D R = T) :
    v_bar FPb kap D R = FPb.pbar D R + kap * T / (qR FPb D R) := by
  exact htauR_batch ▸ rfl

/-
Proposition 4(b) (Dutch attracts more riders than batch, `prop:rider-micro`):
    Under acceptance-rate matching (q^R_DA = q^R_FPb) and τ^R_DA < T = τ^R_FPb,
    the rider entry cutoff satisfies v̄_DA < v̄_FPb, so Dutch attracts
    strictly more riders than batch clearing for any κ > 0.
-/
theorem rider_batch_dominance
    (DA FPb : Mechanism) (kap : ℝ) (D R : ℝ)
    (hkap : kap > 0)
    (hqR_eq : qR DA D R = qR FPb D R)
    (hqR_pos : qR DA D R > 0)
    (htauR_strict : DA.tauR D R < FPb.tauR D R)
    (hpbar : DA.pbar D R ≤ FPb.pbar D R) :
    v_bar DA kap D R < v_bar FPb kap D R := by
  unfold v_bar;
  field_simp;
  rw [ ← hqR_eq ] ; nlinarith [ mul_lt_mul_of_pos_left htauR_strict hkap, mul_div_cancel₀ ( kap * FPb.tauR D R ) ( ne_of_gt hqR_pos ) ]

/-
Proposition 4(c) Case 2 (κ* threshold, `prop:rider-micro`, `eq:kappa-star`):
    When A < 0 and B > 0 (genuine tradeoff), A + κ·B ≥ 0 iff κ ≥ −A/B =: κ*.
-/
theorem rider_kappa_threshold
    (A B kap : ℝ)
    (hA_neg : A < 0) (hB_pos : B > 0) :
    A + kap * B ≥ 0 ↔ kap ≥ -A / B := by
  constructor <;> intro <;> nlinarith [ mul_div_cancel₀ ( -A ) hB_pos.ne' ]

/-
Proposition 4(c) Cases 1, 3, 4 (rider dominance classification, `prop:rider-micro`):
    Case 1: A ≥ 0, B ≥ 0 → A + κ·B ≥ 0 for all κ ≥ 0.
    Case 3: A < 0, B ≤ 0 → A + κ·B < 0 for all κ ≥ 0.
    Case 4: A ≥ 0, B < 0 → A + κ·B ≥ 0 iff κ ≤ A / |B| =: κ**.
-/
theorem rider_dominance_case1
    (A B kap : ℝ) (hA : A ≥ 0) (hB : B ≥ 0) (hkap : kap ≥ 0) :
    A + kap * B ≥ 0 := by
  positivity

theorem rider_dominance_case3
    (A B kap : ℝ) (hA_neg : A < 0) (hB_nonpos : B ≤ 0) (hkap : kap ≥ 0) :
    A + kap * B < 0 := by
  nlinarith

theorem rider_dominance_case4
    (A B kap : ℝ) (hA : A ≥ 0) (hB_neg : B < 0) :
    A + kap * B ≥ 0 ↔ kap ≤ A / (-B) := by
  constructor <;> intros <;> nlinarith [ mul_div_cancel₀ A ( by linarith : ( -B ) ≠ 0 ) ]

end TwoSidedEntry

end