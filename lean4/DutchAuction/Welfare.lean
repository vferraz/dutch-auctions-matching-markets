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
# Welfare Analysis (Section 10)

Propositions 14–17, Corollary 7. Includes the reformulated Proposition 17
(equilibrium welfare comparison with threshold s**) from the Phase 1 audit fix.
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

/-- Welfare at fixed thickness: W_M(D,R) = m·s - λ·D·τ - κ·R·τ^R. -/
def Welfare (M : Mechanism) (s lam kap D R : ℝ) : ℝ :=
  M.m D R * s - lam * D * M.tau D R - kap * R * M.tauR D R

/-- Aggregate waiting-cost change at equilibrium: Δ_wait (Eq. 29 in v11). -/
def Delta_wait (DA FP : Mechanism) (lam kap D1 R1 D2 R2 : ℝ) : ℝ :=
  lam * (D1 * DA.tau D1 R1 - D2 * FP.tau D2 R2) +
  kap * (R1 * DA.tauR D1 R1 - R2 * FP.tauR D2 R2)

-- ============================================================
-- Results
-- ============================================================

namespace WelfareAnalysis

/-- Proposition 14 (Welfare at fixed thickness, `prop:welfare-fixed-thickness`):
    Under quasilinear welfare accounting,
    W_M = m_M · s - λ · D · τ_M - κ · R · τ^R_M. -/
theorem welfare_fixed_thickness
    (M : Mechanism) (s lam kap D R : ℝ) :
    Welfare M s lam kap D R =
    M.m D R * s - lam * D * M.tau D R - kap * R * M.tauR D R := by
  rfl

/-
PROBLEM
Corollary 7 (Conditions for welfare dominance, `cor:welfare-dominance`):
    If Dutch weakly increases volume and weakly reduces both waiting times,
    then W_DA ≥ W_FP for any s ≥ 0.

PROVIDED SOLUTION
Unfold Welfare. Need m_DA·s - λ·D·τ_DA - κ·R·τR_DA ≥ m_FP·s - λ·D·τ_FP - κ·R·τR_FP. Rearrange: (m_DA - m_FP)·s + λ·D·(τ_FP - τ_DA) + κ·R·(τR_FP - τR_DA) ≥ 0. Each term is nonneg: (m_DA - m_FP) ≥ 0 and s ≥ 0; λ ≥ 0, D ≥ 0, τ_FP - τ_DA ≥ 0; κ ≥ 0, R ≥ 0, τR_FP - τR_DA ≥ 0. Use nlinarith.
-/
theorem welfare_dominance_conditions
    (DA FP : Mechanism) (s lam kap D R : ℝ)
    (hs : s ≥ 0) (hlam : lam ≥ 0) (hkap : kap ≥ 0)
    (hD : D ≥ 0) (hR : R ≥ 0)
    -- Volume dominance
    (hm : DA.m D R ≥ FP.m D R)
    -- Timing dominance (both sides)
    (htau : DA.tau D R ≤ FP.tau D R)
    (htauR : DA.tauR D R ≤ FP.tauR D R) :
    Welfare DA s lam kap D R ≥ Welfare FP s lam kap D R := by
  -- By definition of Welfare, we can expand both sides.
  unfold Welfare;
  nlinarith [ mul_nonneg hlam hD, mul_nonneg hkap hR ]

/-
PROBLEM
Proposition 15 (Welfare dominance vs. batch, `prop:welfare-batch`):
    Under acceptance-rate matching, W_DA > W_FPb for any λ,κ > 0, s ≥ 0.

PROVIDED SOLUTION
Unfold Welfare. With hm_eq (volumes equal), the difference is: λ·D·(τ_FPb - τ_DA) + κ·R·(τR_FPb - τR_DA). Both terms are strictly positive: λ > 0, D > 0, τ_FPb > τ_DA; κ > 0, R > 0, τR_FPb > τR_DA. Use nlinarith.
-/
theorem welfare_vs_batch
    (DA FPb : Mechanism) (s lam kap D R : ℝ)
    (hs : s ≥ 0) (hlam : lam > 0) (hkap : kap > 0)
    (hD : D > 0) (hR : R > 0)
    -- Acceptance-rate matching: volumes equal
    (hm_eq : DA.m D R = FPb.m D R)
    -- Strict timing advantage on both sides
    (htau_strict : DA.tau D R < FPb.tau D R)
    (htauR_strict : DA.tauR D R < FPb.tauR D R) :
    Welfare DA s lam kap D R > Welfare FPb s lam kap D R := by
  unfold Welfare; nlinarith [ mul_pos hlam hD, mul_pos hlam hR, mul_pos hkap hD, mul_pos hkap hR ] ;

/-
PROBLEM
Proposition 16 (Welfare vs. immediate: threshold, `prop:welfare-imm`):
    If m_DA ≥ m_FPi, dominance holds for all s ≥ 0.
    If m_DA < m_FPi, dominance requires s ≤ s*.

PROVIDED SOLUTION
Unfold Welfare. Need m_DA·s - λ·D·τ_DA - κ·R·τR_DA ≥ m_FPi·s - λ·D·τ_FPi - κ·R·τR_FPi. Rearrange: (m_DA - m_FPi)·s + λ·D·(τ_FPi - τ_DA) + κ·R·(τR_FPi - τR_DA) ≥ 0. Each term nonneg: hm gives m_DA ≥ m_FPi, hs gives s ≥ 0, hlam/hD/htau give λ·D·(τ_FPi-τ_DA) ≥ 0, hkap/hR/htauR give κ·R·(τR_FPi-τR_DA) ≥ 0. nlinarith.
-/
theorem welfare_vs_immediate
    (DA FPi : Mechanism) (s lam kap D R : ℝ)
    (hs : s ≥ 0) (hlam : lam ≥ 0) (hkap : kap ≥ 0)
    (hD : D ≥ 0) (hR : R ≥ 0)
    -- Timing advantage
    (htau : DA.tau D R ≤ FPi.tau D R)
    (htauR : DA.tauR D R ≤ FPi.tauR D R)
    -- Volume dominance case
    (hm : DA.m D R ≥ FPi.m D R) :
    Welfare DA s lam kap D R ≥ Welfare FPi s lam kap D R := by
  unfold Welfare;
  nlinarith [ mul_nonneg hlam hD, mul_nonneg hkap hR ]

/-
PROBLEM
Proposition 17 (Equilibrium welfare comparison, `prop:welfare-eq`):
    The reformulated result from the Phase 1 audit (fix C1).
    Dutch equilibrium welfare dominance holds iff
    (m_DA - m_FP) · s ≥ Δ_wait.

    Case (a): Δ_wait ≤ 0 → dominance for all s ≥ 0.
    Case (b): Δ_wait > 0, volume gain strict → threshold s**.
    Case (c): Δ_wait > 0, volume gain zero → fails.

PROVIDED SOLUTION
Unfold Welfare and Delta_wait. W_DA - W_FP = (m_DA - m_FP)·s - Δ_wait. By hvol, m_DA ≥ m_FP so (m_DA - m_FP)·s ≥ 0 (since s ≥ 0). By hdelta, Δ_wait ≤ 0 so -Δ_wait ≥ 0. Sum is ≥ 0. nlinarith.
-/
theorem equilibrium_welfare_case_a
    (DA FP : Mechanism) (s lam kap : ℝ)
    (D_star_DA R_star_DA D_star_FP R_star_FP : ℝ)
    (hs : s ≥ 0) (hlam : lam ≥ 0) (hkap : kap ≥ 0)
    -- Volume gain nonneg (from Cor 3)
    (hvol : DA.m D_star_DA R_star_DA ≥ FP.m D_star_FP R_star_FP)
    -- Case (a): Δ_wait ≤ 0
    (hdelta : Delta_wait DA FP lam kap D_star_DA R_star_DA
                D_star_FP R_star_FP ≤ 0) :
    Welfare DA s lam kap D_star_DA R_star_DA ≥
    Welfare FP s lam kap D_star_FP R_star_FP := by
  unfold Delta_wait Welfare at *;
  nlinarith

/-
PROVIDED SOLUTION
Unfold Welfare and Delta_wait. W_DA - W_FP = (m_DA - m_FP)·s - Δ_wait. Let Δm = m_DA - m_FP > 0 (by hvol_strict). The hypothesis hs_ge says s ≥ Δ_wait/Δm, i.e., s·Δm ≥ Δ_wait, i.e., (m_DA - m_FP)·s ≥ Δ_wait. So W_DA - W_FP ≥ 0. Use div_le_iff (with Δm > 0) to convert hs_ge, then nlinarith.
-/
theorem equilibrium_welfare_case_b
    (DA FP : Mechanism) (s lam kap : ℝ)
    (D_star_DA R_star_DA D_star_FP R_star_FP : ℝ)
    (hs : s ≥ 0) (hlam : lam ≥ 0) (hkap : kap ≥ 0)
    -- Case (b): Δ_wait > 0 and volume gain strict
    (hdelta : Delta_wait DA FP lam kap D_star_DA R_star_DA
                D_star_FP R_star_FP > 0)
    (hvol_strict : DA.m D_star_DA R_star_DA > FP.m D_star_FP R_star_FP)
    -- s exceeds threshold s**
    (hs_ge : s ≥ Delta_wait DA FP lam kap D_star_DA R_star_DA
               D_star_FP R_star_FP /
             (DA.m D_star_DA R_star_DA - FP.m D_star_FP R_star_FP)) :
    Welfare DA s lam kap D_star_DA R_star_DA ≥
    Welfare FP s lam kap D_star_FP R_star_FP := by
  unfold Delta_wait Welfare at *;
  rw [ ge_iff_le, div_le_iff₀ ] at hs_ge <;> linarith

/-
PROBLEM
The welfare difference decomposes as volume gain minus Δ_wait.

PROVIDED SOLUTION
Unfold Welfare and Delta_wait. Both sides expand to the same expression. Use ring or simp [Welfare, Delta_wait] and ring.
-/
theorem welfare_difference_decomposition
    (DA FP : Mechanism) (s lam kap : ℝ)
    (D1 R1 D2 R2 : ℝ) :
    Welfare DA s lam kap D1 R1 - Welfare FP s lam kap D2 R2 =
    (DA.m D1 R1 - FP.m D2 R2) * s -
    Delta_wait DA FP lam kap D1 R1 D2 R2 := by
  unfold Welfare Delta_wait; ring;

/-
Proposition `prop:welfare`(b)/(d) (Fixed-thickness welfare iff, v17 line 2220):
    At fixed thickness, W_DA ≥ W_FP iff
    (m_DA − m_FP)·s ≥ λ·D·(τ_DA − τ_FP) + κ·R·(τR_DA − τR_FP).
-/
theorem welfare_fixed_thickness_iff
    (DA FP : Mechanism) (s lam kap D R : ℝ) :
    Welfare DA s lam kap D R ≥ Welfare FP s lam kap D R ↔
    (DA.m D R - FP.m D R) * s ≥
    lam * D * (DA.tau D R - FP.tau D R) +
    kap * R * (DA.tauR D R - FP.tauR D R) := by
  constructor <;> intro h <;> unfold Welfare at * <;> linarith

/-
Proposition `prop:welfare`(d) (Volume-reversal welfare threshold, v17 line 2220):
    When m_DA < m_FPi at fixed thickness but Dutch has timing advantage,
    W_DA ≥ W_FPi iff s ≤ s* where
    s* = [λ·D·(τ_FPi − τ_DA) + κ·R·(τR_FPi − τR_DA)] / (m_FPi − m_DA).
-/
theorem welfare_vs_immediate_volume_reversal
    (DA FPi : Mechanism) (s lam kap D R : ℝ)
    (hs : s ≥ 0) (hlam : lam ≥ 0) (hkap : kap ≥ 0)
    (hD : D ≥ 0) (hR : R ≥ 0)
    (hvol_rev : FPi.m D R > DA.m D R)
    (htau : DA.tau D R ≤ FPi.tau D R)
    (htauR : DA.tauR D R ≤ FPi.tauR D R)
    (htiming_pos : lam * D * (FPi.tau D R - DA.tau D R) +
                   kap * R * (FPi.tauR D R - DA.tauR D R) > 0) :
    Welfare DA s lam kap D R ≥ Welfare FPi s lam kap D R ↔
    s ≤ (lam * D * (FPi.tau D R - DA.tau D R) +
         kap * R * (FPi.tauR D R - DA.tauR D R)) /
        (FPi.m D R - DA.m D R) := by
  rw [ le_div_iff₀ ( sub_pos.2 hvol_rev ) ];
  constructor <;> intro h <;> unfold Welfare at * <;> linarith

/-
Proposition `prop:welfare-eq` case (b) full iff (v17 line 2305):
    When Δ_wait > 0 and volume gain is strict (m_DA > m_FP),
    W_DA ≥ W_FP if and only if s ≥ s** := Δ_wait / (m_DA − m_FP).
-/
theorem equilibrium_welfare_case_b_iff
    (DA FP : Mechanism) (s lam kap : ℝ)
    (D_star_DA R_star_DA D_star_FP R_star_FP : ℝ)
    (hs : s ≥ 0) (hlam : lam ≥ 0) (hkap : kap ≥ 0)
    (hdelta : Delta_wait DA FP lam kap D_star_DA R_star_DA
                D_star_FP R_star_FP > 0)
    (hvol_strict : DA.m D_star_DA R_star_DA > FP.m D_star_FP R_star_FP) :
    Welfare DA s lam kap D_star_DA R_star_DA ≥
    Welfare FP s lam kap D_star_FP R_star_FP ↔
    s ≥ Delta_wait DA FP lam kap D_star_DA R_star_DA
          D_star_FP R_star_FP /
        (DA.m D_star_DA R_star_DA - FP.m D_star_FP R_star_FP) := by
  constructor <;> intro <;> rw [ ge_iff_le ] at * <;> rw [ div_le_iff₀ ( by linarith ) ] at * <;> nlinarith [ WelfareAnalysis.welfare_difference_decomposition DA FP s lam kap D_star_DA R_star_DA D_star_FP R_star_FP ]

/-
Proposition `prop:welfare-eq` case (c) (v17 line 2305):
    If Δ_wait > 0 and the volume gain is zero (m_DA = m_FP at equilibrium),
    then W_DA < W_FP for all s ≥ 0. Dominance fails.
-/
theorem equilibrium_welfare_case_c
    (DA FP : Mechanism) (s lam kap : ℝ)
    (D_star_DA R_star_DA D_star_FP R_star_FP : ℝ)
    (hs : s ≥ 0) (hlam : lam ≥ 0) (hkap : kap ≥ 0)
    (hvol_eq : DA.m D_star_DA R_star_DA = FP.m D_star_FP R_star_FP)
    (hdelta : Delta_wait DA FP lam kap D_star_DA R_star_DA
                D_star_FP R_star_FP > 0) :
    Welfare DA s lam kap D_star_DA R_star_DA <
    Welfare FP s lam kap D_star_FP R_star_FP := by
  unfold Welfare Delta_wait at *; nlinarith [ mul_nonneg hs hlam, mul_nonneg hs hkap ] ;

end WelfareAnalysis

end