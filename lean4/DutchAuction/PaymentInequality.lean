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
# Payment Inequality under Acceptance-Rate Matching (Section 4, corrected)

This file corrects the payment-equality claim in Proposition OA.6 / main text
Proposition 1(d). The original code (`Microfoundation.lean`, theorem
`dutch_dominance_vs_batch`) assumes `hpi_eq : ∀ D R, DA.pi D R = FPb.pi D R`.

The numerical diagnostics (`dutch_auction/verify_section4.py`) illustrate that
under the Poisson microfoundation with uniform rider values and a declining Dutch
price path p(t) = p₀ e^{−δt}:

  E[p^DA(X) | X ≤ T] > p̄_ARM

because the survival function S^DA(t) front-loads trades to early times where
prices are high. The acceptance-rate-matching (ARM) condition equates the
**time-averaged** acceptance rate to (1 − p̄), while the **trade-weighted**
average price can exceed p̄.

This file does not derive the payment inequality from the Poisson primitives.
It records the corrected conditional statement: if the trade-weighted Dutch
payment is at least the posted-price benchmark, then the batch comparison gains
a non-negative earnings term in addition to the timing term.

We provide:
1. A conditional `dutch_dominance_vs_batch_corrected` replacing `hpi_eq`
   with the explicit hypothesis `hpi_ge : ∀ D R, DA.pi D R ≥ FPb.pi D R`.
2. The corrected c̄ difference decomposition under ARM.
3. Reduced-form diagnostics for the trade-weighted price condition.

Paper reference: Section 4 (corrected), Proposition 1(d), Remark 4
(rem:payment-equality, corrected), and Proposition OA.6 in the Online Appendix.
-/

-- ============================================================
-- Definitions (self-contained)
-- ============================================================

/-- A reduced-form mechanism. -/
structure Mechanism where
  q    : ℝ → ℝ → ℝ
  pi   : ℝ → ℝ → ℝ
  tau  : ℝ → ℝ → ℝ
  tauR : ℝ → ℝ → ℝ
  m    : ℝ → ℝ → ℝ
  pbar : ℝ → ℝ → ℝ

/-- Driver-entry cutoff: c̄_M(D,R) = q_M · π_M - λ · τ_M. -/
def c_bar (M : Mechanism) (lam : ℝ) (D R : ℝ) : ℝ :=
  M.q D R * M.pi D R - lam * M.tau D R

-- ============================================================
-- Results
-- ============================================================

namespace PaymentInequality

/-- Front-loading principle for declining Dutch price paths (reduced-form
    assumption form).

    Under ARM with a strictly decreasing Dutch price path
    `p^DA(t) = p₀ · e^{−δt}` and a decreasing survival function `S^DA(t)`,
    trades concentrate at early times where prices are high. The
    trade-weighted average price then exceeds the time-averaged price;
    since ARM equates the time-averaged acceptance rate to `(1 − p̄)`,
    the trade-weighted average price exceeds `p̄`. Consequently
    `π_DA ≥ π_FPb` under ARM, with strict inequality when `δ > 0` and
    `q_DA > 0`.

    Numerical illustration at a representative baseline
    (A=0.5, β=0.5, T=30, ρ=0.7, δ=0.02, θ=1.0):
    `E[p^DA(X) | X ≤ T] = 0.630` vs `p̄_ARM = 0.526`.

    At the reduced-form level we expose `π_DA ≥ π_FPb` as a hypothesis
    `hpi_ge` rather than derive it from Poisson primitives. -/
theorem front_loading_payment_inequality
    (DA FPb : Mechanism) (D R : ℝ)
    (hpi_ge : DA.pi D R ≥ FPb.pi D R) :
    DA.pi D R ≥ FPb.pi D R :=
  by
    lia

/-- Corrected c̄ difference under ARM.

    Under ARM, `q_DA = q_FPb`. With the payment inequality
    `π_DA ≥ π_FPb` (rather than the limit-case equality), the dominance
    margin decomposes as

        c̄_DA − c̄_FPb = q · (π_DA − π_FPb) + λ · (T − τ_DA).

    Under the payment hypothesis, the earnings term
    `q · (π_DA − π_FPb)` is an additional non-negative contribution
    besides the timing term `λ · (T − τ_DA)`. -/
theorem cbar_difference_under_ARM
    (DA FPb : Mechanism) (lam T : ℝ) (D R : ℝ)
    -- ARM: match probabilities equal
    (hq_eq : DA.q D R = FPb.q D R)
    -- Batch clears at T
    (htau_FPb : FPb.tau D R = T) :
    c_bar DA lam D R - c_bar FPb lam D R =
    DA.q D R * (DA.pi D R - FPb.pi D R) + lam * (T - DA.tau D R) := by
  unfold c_bar; rw [ hq_eq, htau_FPb ] ; ring;

/-- Conditional Dutch dominance vs. batch (Proposition OA.6 /
    Proposition 1(d)).

    Under ARM with the explicit payment hypothesis `π_DA ≥ π_FPb`,
    Dutch dominates batch clearing for all `λ > 0`. This records the
    conditional comparison rather than deriving the payment inequality
    from Poisson primitives. -/
theorem dutch_dominance_vs_batch_corrected
    (DA FPb : Mechanism) (lam : ℝ) (T : ℝ)
    (hlam : lam > 0) (hT : T > 0)
    -- ARM: match probabilities equal
    (hq_eq : ∀ D R, DA.q D R = FPb.q D R)
    -- Payment INEQUALITY under ARM (corrected from equality)
    (hpi_ge : ∀ D R, DA.pi D R ≥ FPb.pi D R)
    -- Non-negativity of match probability
    (hq_nonneg : ∀ D R, DA.q D R ≥ 0)
    -- Timing advantage: τ_DA < T = τ_FPb
    (htau_DA_lt : ∀ D R, DA.tau D R < T)
    (htau_FPb : ∀ D R, FPb.tau D R = T) :
    ∀ D R, c_bar DA lam D R ≥ c_bar FPb lam D R := by
  intros D R
  have h_diff : c_bar DA lam D R - c_bar FPb lam D R = DA.q D R * (DA.pi D R - FPb.pi D R) + lam * (T - DA.tau D R) := by
    unfold c_bar; rw [ hq_eq, htau_FPb ] ; ring;
  nlinarith [ hq_nonneg D R, hpi_ge D R, htau_DA_lt D R ]

/-- The strengthened theorem implies the limit case: if `π_DA = π_FPb`,
    then certainly `π_DA ≥ π_FPb`. -/
theorem dutch_dominance_vs_batch_from_equality
    (DA FPb : Mechanism) (lam : ℝ) (T : ℝ)
    (hlam : lam > 0) (hT : T > 0)
    (hq_eq : ∀ D R, DA.q D R = FPb.q D R)
    -- Original (overly strong) payment equality assumption
    (hpi_eq : ∀ D R, DA.pi D R = FPb.pi D R)
    (hq_nonneg : ∀ D R, DA.q D R ≥ 0)
    (htau_DA_lt : ∀ D R, DA.tau D R < T)
    (htau_FPb : ∀ D R, FPb.tau D R = T) :
    ∀ D R, c_bar DA lam D R ≥ c_bar FPb lam D R :=
  by
    exact fun D R => dutch_dominance_vs_batch_corrected DA FPb lam T hlam hT hq_eq ( fun D R => hpi_eq D R ▸ le_rfl ) hq_nonneg htau_DA_lt htau_FPb D R

/-- Strict c̄ dominance: the strengthened form gives a strict inequality.
    Beyond the timing-only bound `c̄_DA − c̄_FPb = λ · (T − τ_DA) > 0`,
    the corrected decomposition yields the larger margin
    `c̄_DA − c̄_FPb ≥ λ · (T − τ_DA) > 0`. -/
theorem dutch_dominance_vs_batch_strict
    (DA FPb : Mechanism) (lam : ℝ) (T : ℝ) (D R : ℝ)
    (hlam : lam > 0)
    (hq_eq : DA.q D R = FPb.q D R)
    (hpi_ge : DA.pi D R ≥ FPb.pi D R)
    (hq_nonneg : DA.q D R ≥ 0)
    (htau_DA_lt : DA.tau D R < T)
    (htau_FPb : FPb.tau D R = T) :
    c_bar DA lam D R > c_bar FPb lam D R := by
  have h_ineq' : DA.pi D R * FPb.q D R - lam * DA.tau D R > FPb.pi D R * FPb.q D R - lam * FPb.tau D R := by
    rw [ ← hq_eq, htau_FPb ] ; nlinarith;
  convert h_ineq' using 1 <;> push_cast [ hq_eq, htau_FPb, c_bar ] <;> ring

/-- Lower bound on the dominance margin: under the corrected hypotheses,

        c̄_DA − c̄_FPb ≥ λ · (T − τ_DA).

    The paper's Eq. (10) is reinterpreted as a lower bound rather than an
    equality; the earnings term `q · (π_DA − π_FPb)` is the additional
    non-negative margin. -/
theorem dominance_margin_lower_bound
    (DA FPb : Mechanism) (lam T : ℝ) (D R : ℝ)
    (hq_eq : DA.q D R = FPb.q D R)
    (hpi_ge : DA.pi D R ≥ FPb.pi D R)
    (hq_nonneg : DA.q D R ≥ 0)
    (htau_FPb : FPb.tau D R = T) :
    c_bar DA lam D R - c_bar FPb lam D R ≥ lam * (T - DA.tau D R) := by
  unfold c_bar;
  cases le_total lam 0 <;> cases le_total ( DA.pi D R ) 0 <;> simp_all +decide <;> nlinarith

/-- Welfare invariance under the payment correction.

    Welfare at fixed thickness is

        W_M = m_M · s − λ · D · τ_M − κ · R · τ^R_M.

    Under ARM, `q_DA = q_FPb` gives `m_DA = m_FPb` (since `m = D · q`).
    Because monetary payments cancel in welfare (quasilinearity), the
    fixed-thickness welfare comparison depends only on volume and waiting
    times — the payment inequality `π_DA ≥ π_FPb` affects entry incentives
    via `c̄` (and hence `D*`), but not fixed-thickness welfare directly. -/
theorem welfare_vs_batch_invariant_under_payment_correction
    (DA FPb : Mechanism) (s lam kap D R : ℝ)
    -- These are the SAME hypotheses as in Welfare.welfare_vs_batch
    (hs : s ≥ 0) (hlam : lam > 0) (hkap : kap > 0)
    (hD : D > 0) (hR : R > 0)
    (hm_eq : DA.m D R = FPb.m D R)
    (htau_strict : DA.tau D R < FPb.tau D R)
    (htauR_strict : DA.tauR D R < FPb.tauR D R)
    -- Payment inequality does NOT appear — welfare is independent of π
    : DA.m D R * s - lam * D * DA.tau D R - kap * R * DA.tauR D R >
      FPb.m D R * s - lam * D * FPb.tau D R - kap * R * FPb.tauR D R := by
  nlinarith [ mul_pos hlam hD, mul_pos hkap hR ]

/-- Algebraic helper for the conditional payment-inequality structure.

    A trade-weighted average over a partition `[0, t*] ∪ (t*, T]` with mass
    fractions `θ ∈ [0, 1]` and `(1 − θ)` is at least `θ · p̄` whenever the
    pre-`t*` component price `p_pre` exceeds `p̄` and the post-`t*` price
    `p_post` is non-negative.

    This is the structural content of the front-loading argument behind
    Proposition OA.6: under ARM, if most trade mass concentrates at
    `t ≤ t*` where `p^DA(t) ≥ p̄`, then the trade-weighted price is bounded
    below by `θ · p̄`. Combined with `q_DA = q_FPb` (ARM) this gives
    `π_DA ≥ θ · π_FPb`, with `π_DA ≥ π_FPb` exactly when `θ = 1` or the
    post-`t*` average price compensates.

    Numerical verification across baseline scenarios from Table OA.1 shows
    `θ_pre ≈ 0.97` at typical baselines (T=30, ρ=0.7), versus
    `θ_pre ≈ 0.44` in short-session stress rows (T=1, ρ=0.7, η·T=0.5)
    where the substantive condition fails. -/
theorem trade_weighted_price_ge_threshold
    (theta pbar p_pre p_post : ℝ)
    (htheta_nn : 0 ≤ theta) (htheta_le : theta ≤ 1)
    (hpre  : p_pre  ≥ pbar)
    (hpost : 0 ≤ p_post)
    (hpbar : 0 ≤ pbar) :
    theta * p_pre + (1 - theta) * p_post ≥ theta * pbar := by
  nlinarith [htheta_nn, htheta_le, hpre, hpost, hpbar]

/-- Conditional payment inequality from the trade-weighted-average diagnostic.

    Refines the tautological form of `front_loading_payment_inequality`
    into a *conditional* theorem whose hypothesis `h_avg_ge` is directly
    verifiable from a numerical computation of the trade-weighted DA price.
    The hypothesis `DA.pi D R ≥ (1 − α) · p̄` is the substantive content
    that Proposition OA.6's front-loading argument establishes verbally;
    deriving it from Poisson primitives requires an integration formalism
    that is outside the current scope.

    This is *not* a primitive proof of `π_DA ≥ π_FPb`. It is a conditional
    theorem making the substantive dependency explicit — the
    trade-weighted-average DA-price diagnostic is named as a hypothesis,
    and callers must supply `h_avg_ge` together with its applicability
    conditions (numerically verified at typical baselines, fails in
    short-session stress regimes). -/
theorem pi_DA_ge_pi_FPb_under_premium_average
    (DA FPb : Mechanism) (D R alpha pbar : ℝ)
    (hα     : alpha < 1)
    (hpbar  : 0 ≤ pbar)
    -- Closed form for FPb's payment: π_FPb = (1 − α) · p̄.
    (hFPb_eq : FPb.pi D R = (1 - alpha) * pbar)
    -- Substantive diagnostic: trade-weighted DA price ≥ p̄ (after commission).
    -- Numerically true at baseline; FAILS in stress row (k) with η·T = 0.5.
    (h_avg_ge : DA.pi D R ≥ (1 - alpha) * pbar) :
    DA.pi D R ≥ FPb.pi D R := by
  rw [hFPb_eq]; exact h_avg_ge

end PaymentInequality

end
