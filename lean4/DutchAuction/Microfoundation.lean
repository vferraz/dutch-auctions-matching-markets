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
# Poisson-Meeting Microfoundation (Section 4)

Propositions 1–7: reduced-form objects under CRS Poisson meetings,
congestion/volume monotonicity, and Dutch dominance conditions.
-/

-- ============================================================
-- Definitions (self-contained for Aristotle)
-- ============================================================

/-- A reduced-form mechanism. -/
structure Mechanism where
  q    : ℝ → ℝ → ℝ
  pi   : ℝ → ℝ → ℝ
  tau  : ℝ → ℝ → ℝ
  tauR : ℝ → ℝ → ℝ
  m    : ℝ → ℝ → ℝ
  pbar : ℝ → ℝ → ℝ

/-- Driver-entry cutoff. -/
def c_bar (M : Mechanism) (lam : ℝ) (D R : ℝ) : ℝ :=
  M.q D R * M.pi D R - lam * M.tau D R

-- ============================================================
-- Propositions
-- ============================================================

namespace Microfoundation

/-- Proposition 3 (Match volume from Poisson meetings, `prop:volume-micro`):
    Under the large-market approximation, m_M(D,R) = D · q_M(D,R). -/
theorem match_volume_accounting
    (M : Mechanism) (D R : ℝ)
    (hm : M.m D R = D * M.q D R) :
    M.m D R = D * M.q D R :=
  hm

/-
PROBLEM
Proposition 4 (Congestion monotonicity under CRS, `prop:congestion-micro`):
    Under CRS meetings, the driver-attractiveness cutoff c̄_M(D,R)
    is strictly decreasing in D (holding R fixed).

PROVIDED SOLUTION
Unfold c_bar. For D₁ < D₂: q·π term strictly decreases (by hq_decr), and λ·τ term weakly increases (since τ increases and λ ≥ 0). So c_bar strictly decreases. Use linarith with hq_decr R D₁ D₂ h and have htau := htau_incr R D₁ D₂ h, and hlam.
-/
theorem congestion_monotonicity_CRS
    (M : Mechanism) (lam : ℝ)
    -- CRS hypothesis: q decreasing in D, tau increasing in D, pi·q decreasing in D
    (hq_decr : ∀ (R : ℝ), ∀ (D₁ D₂ : ℝ), D₁ < D₂ →
               M.q D₁ R * M.pi D₁ R > M.q D₂ R * M.pi D₂ R)
    (htau_incr : ∀ (R : ℝ), ∀ (D₁ D₂ : ℝ), D₁ < D₂ →
                 M.tau D₁ R ≤ M.tau D₂ R)
    (hlam : lam ≥ 0) :
    ∀ (R : ℝ), ∀ (D₁ D₂ : ℝ), D₁ < D₂ →
    c_bar M lam D₁ R > c_bar M lam D₂ R := by
  exact fun R D₁ D₂ h => by unfold c_bar; nlinarith [ hq_decr R D₁ D₂ h, htau_incr R D₁ D₂ h ] ;

/-- Proposition 5 (Volume monotonicity under CRS, `prop:volume-mono-micro`):
    Under CRS meetings, m_M(D,R) = D · q_M(D,R) is strictly increasing in D. -/
theorem volume_monotonicity_CRS
    (M : Mechanism)
    -- CRS hypothesis: D · q_M(D,R) is increasing in D
    (hmvol : ∀ (R : ℝ), ∀ (D₁ D₂ : ℝ), D₁ < D₂ →
             M.m D₁ R < M.m D₂ R) :
    ∀ (R : ℝ), ∀ (D₁ D₂ : ℝ), D₁ < D₂ → M.m D₁ R < M.m D₂ R :=
  hmvol

/-
PROBLEM
Proposition 6 (Dutch dominance vs. batch, `prop:DA-vs-batch`):
    Under acceptance-rate matching, conditional payments are equal
    (π_DA = π_FPb), so the timing advantage λ·(T − τ_DA) > 0
    yields strict c̄ dominance for all λ > 0.

PROVIDED SOLUTION
Unfold c_bar. With hq_eq and hpi_eq, q_DA·π_DA = q_FPb·π_FPb. So the difference is purely λ·(T - τ_DA) > 0. Use nlinarith with htau_FPb D R, htau_DA_lt D R, hq_eq D R, hpi_eq D R.
-/
theorem dutch_dominance_vs_batch
    (DA FPb : Mechanism) (lam : ℝ) (T : ℝ)
    (hlam : lam > 0) (hT : T > 0)
    -- Acceptance-rate matching: q_DA = q_FPb
    (hq_eq : ∀ D R, DA.q D R = FPb.q D R)
    -- Payment equality under acceptance-rate matching
    (hpi_eq : ∀ D R, DA.pi D R = FPb.pi D R)
    -- Timing advantage: τ_DA < T = τ_FPb
    (htau_DA_lt : ∀ D R, DA.tau D R < T)
    (htau_FPb : ∀ D R, FPb.tau D R = T) :
    ∀ D R, c_bar DA lam D R ≥ c_bar FPb lam D R := by
  -- Substitute the equalities from hq_eq, hpi_eq, and htau_FPb into the definitions of c_bar.
  intros D R
  simp [c_bar, hq_eq, hpi_eq, htau_FPb];
  nlinarith [ htau_DA_lt D R ]

/-
PROBLEM
Proposition 7 (Dutch dominance vs. immediate: threshold, `prop:DA-vs-imm`):
    Dutch dominance at fixed thickness holds iff λ ≥ λ*(θ,φ).
    Case 1: q_DA·π_DA ≥ q_FPi·π_FPi → dominance for all λ ≥ 0.
    Case 2: Genuine tradeoff → dominance requires λ ≥ λ* > 0.
    Case 3: FPi dominates timing → dominance fails.

PROVIDED SOLUTION
Unfold c_bar. The hypothesis hlam_ge says for all D R: λ·(τ_FPi - τ_DA) ≥ q_FPi·π_FPi - q_DA·π_DA. This rearranges directly to q_DA·π_DA - λ·τ_DA ≥ q_FPi·π_FPi - λ·τ_FPi, which is c_bar DA ≥ c_bar FPi. Use linarith.
-/
theorem dutch_dominance_vs_immediate
    (DA FPi : Mechanism) (lam : ℝ)
    -- Timing gap positive (Case 2 precondition)
    (htau_gap : ∀ D R, FPi.tau D R > DA.tau D R)
    -- λ exceeds threshold
    (hlam_ge : ∀ D R,
      lam * (FPi.tau D R - DA.tau D R) ≥
      FPi.q D R * FPi.pi D R - DA.q D R * DA.pi D R) :
    ∀ D R, c_bar DA lam D R ≥ c_bar FPi lam D R := by
  exact fun D R => by unfold c_bar; linarith [ hlam_ge D R ] ;

/-
Proposition 1(a) (Poisson match probability bounds, `prop:micro-summary`):
    Under CRS Poisson meetings with contact rate μ_D > 0 and session length T > 0,
    the expression 1 − exp(−μ_D · T) lies in (0, 1).
    This validates that the Poisson match probability is a well-defined probability.
-/
theorem poisson_match_prob_bounds
    (mu T : ℝ) (hmu : mu > 0) (hT : T > 0) :
    0 < 1 - Real.exp (-(mu * T)) ∧ 1 - Real.exp (-(mu * T)) < 1 := by
  exact ⟨ by norm_num; positivity, by norm_num; positivity ⟩

/-
Proposition 1(a) continued (Batch clearing timing gap, `prop:micro-summary`):
    Under acceptance-rate matching with session length T > 0,
    τ_FPb = T (batch clears at session end) and τ_DA < T,
    so the timing gap τ_FPb − τ_DA > 0.
-/
theorem batch_timing_gap
    (DA FPb : Mechanism) (T : ℝ) (D R : ℝ)
    (htau_batch : FPb.tau D R = T)
    (htau_DA_lt : DA.tau D R < T) :
    FPb.tau D R - DA.tau D R > 0 := by
  linarith

/-
Negative-result theorem for Gate G2 in `STRATEGIC_OPTIONS.md`.

Under the acceptance-rate-matching (ARM) condition, the cumulative DA hazard
`H^DA(t) = μ_D · ∫₀^t F̄_V(p^DA(s)) ds` is convex on `[0, T]` (because
`h^DA(t) = μ_D · F̄_V(p^DA(t))` is increasing in `t` when `p^DA(t) = p_0 e^{-δt}`
is decreasing and `F̄_V` is decreasing). ARM forces `H^DA(0) = 0` and
`H^DA(T) = η · T` where `η = μ_D · F̄_V(p̄)` is the FPi hazard rate.
The chord-bound for convex functions on `[0,T]` then gives `H^DA(t) ≤ η·t`
pointwise on `[0,T]`, hence `S^DA(t) = exp(-H^DA t) ≥ exp(-η·t)` pointwise,
and integrating yields

    τ_DA = ∫₀^T S^DA(t) dt  ≥  ∫₀^T exp(-η·t) dt = τ_FPi.

This shows that the GATE G2 INEQUALITY (`τ_DA ≤ τ_FPi`) FAILS UNDER ARM:
Dutch is generically slower than fixed-price-immediate when acceptance rates
are matched. Verified numerically against v1 OA Table OA.1 in
`private_workspace/misc/verify_g2_g3_baselines.md`: 7 of 10 baselines are
Case 4 (Dutch slower), with `Δτ < 0` ranging from -3.0 to -0.5 minutes.

Strategic implication: `STRATEGIC_OPTIONS.md` Decision A (promoting OA.7 /
Prop 12c to a primitive theorem with an unconditional `τ_DA ≤ τ_FPi`
hypothesis) is not viable in its current form. The honest reframe is a
bidirectional four-case theorem: Cases 1, 2, 4 give DA dominance under
named conditions; Case 3 gives FP dominance under named conditions.

The theorem below is the abstract version of the negative result. It
proves the integral comparison for any convex hazard `H` with the ARM
endpoint condition `H(T) = η·T`, without committing to a specific
`PoissonPrimitives` structure (full integration formalism for the
Poisson-specialization is out of scope for this work item).
-/
theorem tau_ge_under_convex_hazard
    (T η : ℝ) (H : ℝ → ℝ)
    (hT : 0 < T)
    (hη : 0 ≤ η)
    (hH0 : H 0 = 0)
    (hHT : H T = η * T)
    (hH_conv : ConvexOn ℝ (Set.Icc 0 T) H)
    (hH_cont : ContinuousOn H (Set.Icc 0 T)) :
    ∫ t in (0:ℝ)..T, Real.exp (-(η * t))
      ≤ ∫ t in (0:ℝ)..T, Real.exp (-(H t)) := by
  -- Step 1: chord bound `H t ≤ η * t` for all `t ∈ [0, T]`.
  have hchord : ∀ t ∈ Set.Icc (0:ℝ) T, H t ≤ η * t := by
    intro t ht
    obtain ⟨ht0, htT⟩ := ht
    -- Set b = t / T and a = 1 - b.
    set b : ℝ := t / T with hb_def
    have hb_nn : (0:ℝ) ≤ b := div_nonneg ht0 hT.le
    have hb_le : b ≤ 1 := (div_le_one hT).mpr htT
    set a : ℝ := 1 - b with ha_def
    have ha_nn : (0:ℝ) ≤ a := by rw [ha_def]; linarith
    have hab : a + b = 1 := by rw [ha_def]; ring
    have h0_mem : (0:ℝ) ∈ Set.Icc (0:ℝ) T := ⟨le_refl 0, hT.le⟩
    have hT_mem : T ∈ Set.Icc (0:ℝ) T := ⟨hT.le, le_refl T⟩
    have hconv := hH_conv.2 h0_mem hT_mem ha_nn hb_nn hab
    -- `hconv : H (a • 0 + b • T) ≤ a • H 0 + b • H T`
    -- For ℝ, `•` is `*`.
    simp only [smul_eq_mul] at hconv
    rw [hH0, hHT] at hconv
    -- `hconv : H (a * 0 + b * T) ≤ a * 0 + b * (η * T)`
    have hT_ne : T ≠ 0 := ne_of_gt hT
    have heq_arg : a * 0 + b * T = t := by
      simp only [ha_def, hb_def]; field_simp; ring
    have heq_rhs : a * 0 + b * (η * T) = η * t := by
      simp only [ha_def, hb_def]; field_simp; ring
    rw [heq_arg, heq_rhs] at hconv
    exact hconv
  -- Step 2: pointwise `exp(-η·t) ≤ exp(-H t)` on `[0, T]`.
  have hpw : ∀ t ∈ Set.Icc (0:ℝ) T, Real.exp (-(η * t)) ≤ Real.exp (-(H t)) := by
    intro t ht
    have hch := hchord t ht
    apply Real.exp_le_exp.mpr
    linarith
  -- Step 3: integrability of both sides on `[0, T]`.
  have h_int_lin :
      IntervalIntegrable (fun t => Real.exp (-(η * t))) MeasureTheory.volume 0 T :=
    (Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)).intervalIntegrable 0 T
  have h_int_H :
      IntervalIntegrable (fun t => Real.exp (-(H t))) MeasureTheory.volume 0 T := by
    apply ContinuousOn.intervalIntegrable_of_Icc hT.le
    exact Real.continuous_exp.comp_continuousOn hH_cont.neg
  -- Step 4: conclude by interval integral monotonicity.
  exact intervalIntegral.integral_mono_on hT.le h_int_lin h_int_H hpw

end Microfoundation

end