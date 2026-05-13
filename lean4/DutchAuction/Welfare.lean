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
(equilibrium welfare comparison with threshold s**).
-/

-- ============================================================
-- Definitions (self-contained)
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

/-- Aggregate waiting-cost change at equilibrium: Δ_wait. -/
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

/-- Corollary 7 (Conditions for welfare dominance, `cor:welfare-dominance`):
    If Dutch weakly increases volume and weakly reduces both waiting times,
    then `W_DA ≥ W_FP` for any `s ≥ 0`. -/
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

/-- Proposition 15 (Welfare dominance vs. batch, `prop:welfare-batch`):
    Under acceptance-rate matching, `W_DA > W_FPb` for any
    `λ, κ > 0` and `s ≥ 0`. -/
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

/-- Proposition 16 (Welfare vs. immediate: threshold, `prop:welfare-imm`):
    If `m_DA ≥ m_FPi`, dominance holds for all `s ≥ 0`.
    If `m_DA < m_FPi`, dominance requires `s ≤ s*`. -/
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

/-- Proposition 17 (Equilibrium welfare comparison, `prop:welfare-eq`),
    case (a): when `Δ_wait ≤ 0`, dominance `W_DA ≥ W_FP` holds for all
    `s ≥ 0`. Cases (b) and (c) follow below.

    The full statement: Dutch equilibrium welfare dominance holds iff
    `(m_DA − m_FP) · s ≥ Δ_wait`. Case (b) is `Δ_wait > 0` with strict
    volume gain (threshold `s**`); case (c) is `Δ_wait > 0` with zero
    volume gain (dominance fails). -/
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

/-- Proposition 17 case (b): when `Δ_wait > 0` and the volume gain is
    strict (`m_DA > m_FP`), dominance holds for `s ≥ s** := Δ_wait /
    (m_DA − m_FP)`. -/
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

/-- The welfare difference decomposes as volume gain minus `Δ_wait`. -/
theorem welfare_difference_decomposition
    (DA FP : Mechanism) (s lam kap : ℝ)
    (D1 R1 D2 R2 : ℝ) :
    Welfare DA s lam kap D1 R1 - Welfare FP s lam kap D2 R2 =
    (DA.m D1 R1 - FP.m D2 R2) * s -
    Delta_wait DA FP lam kap D1 R1 D2 R2 := by
  unfold Welfare Delta_wait; ring;

/-- Proposition `prop:welfare` (b)/(d) (Fixed-thickness welfare iff):
    At fixed thickness, `W_DA ≥ W_FP` iff
    `(m_DA − m_FP) · s ≥ λ · D · (τ_DA − τ_FP) + κ · R · (τR_DA − τR_FP)`. -/
theorem welfare_fixed_thickness_iff
    (DA FP : Mechanism) (s lam kap D R : ℝ) :
    Welfare DA s lam kap D R ≥ Welfare FP s lam kap D R ↔
    (DA.m D R - FP.m D R) * s ≥
    lam * D * (DA.tau D R - FP.tau D R) +
    kap * R * (DA.tauR D R - FP.tauR D R) := by
  constructor <;> intro h <;> unfold Welfare at * <;> linarith

/-- Proposition `prop:welfare` (d) (Volume-reversal welfare threshold):
    When `m_DA < m_FPi` at fixed thickness but Dutch has a timing advantage,
    `W_DA ≥ W_FPi` iff `s ≤ s*` where
    `s* = [λ · D · (τ_FPi − τ_DA) + κ · R · (τR_FPi − τR_DA)] / (m_FPi − m_DA)`. -/
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

/-- Proposition `prop:welfare-eq` case (b), full iff:
    When `Δ_wait > 0` and the volume gain is strict (`m_DA > m_FP`),
    `W_DA ≥ W_FP` iff `s ≥ s** := Δ_wait / (m_DA − m_FP)`. -/
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

/-- Proposition `prop:welfare-eq` case (c):
    If `Δ_wait > 0` and the volume gain is zero (`m_DA = m_FP` at
    equilibrium), then `W_DA < W_FP` for all `s ≥ 0`; dominance fails. -/
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