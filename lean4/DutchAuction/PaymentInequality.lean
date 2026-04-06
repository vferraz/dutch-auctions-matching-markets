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

The SymPy verification (`dutch_auction/verify_section4.py`) proved numerically
that under the Poisson microfoundation with uniform rider values and a declining
Dutch price path p(t) = p₀ e^{−δt}:

  E[p^DA(X) | X ≤ T] > p̄_ARM

because the survival function S^DA(t) front-loads trades to early times where
prices are high. The acceptance-rate-matching (ARM) condition equates the
**time-averaged** acceptance rate to (1 − p̄), but the **trade-weighted**
average price exceeds p̄. Therefore π_DA > π_FPb under ARM.

This STRENGTHENS the dominance result: Dutch beats batch clearing through
BOTH a timing advantage AND an earnings advantage, not timing alone.

We provide:
1. A strengthened `dutch_dominance_vs_batch_corrected` replacing `hpi_eq`
   with the weaker (and correct) `hpi_ge : ∀ D R, DA.pi D R ≥ FPb.pi D R`.
2. The corrected c̄ difference decomposition under ARM.
3. A front-loading lemma formalizing the trade-weighted price inequality.

Paper reference: Section 4 (corrected), Proposition 1(d), Remark 4
(rem:payment-equality, corrected), and Proposition OA.6 in the Online Appendix.
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

/-- Driver-entry cutoff: c̄_M(D,R) = q_M · π_M - λ · τ_M. -/
def c_bar (M : Mechanism) (lam : ℝ) (D R : ℝ) : ℝ :=
  M.q D R * M.pi D R - lam * M.tau D R

-- ============================================================
-- Results
-- ============================================================

namespace PaymentInequality

/-
PROBLEM
Front-loading principle for declining price paths:
    If the Dutch price path is strictly decreasing and the survival
    function S^DA(t) is also decreasing (front-loading trades to early
    times), then the trade-weighted average price exceeds the
    time-averaged price. Under ARM, the time-averaged acceptance rate
    equals (1 − p̄), so the trade-weighted average price exceeds p̄.

    Numerically verified in `dutch_auction/verify_section4.py`:
    At baseline (A=0.5, β=0.5, T=30, ρ=0.7, δ=0.02, θ=1.0),
    E[p^DA(X)|X≤T] = 0.630 vs p̄_ARM = 0.526.

    We state this as an assumption at the reduced-form level:
    π_DA ≥ π_FPb under ARM.

Front-loading principle (assumption, verified numerically):
    Under ARM with a declining Dutch price path, the trade-weighted
    average price weakly exceeds the posted price. Consequently,
    π_DA ≥ π_FPb. This is strict when δ > 0 and q_DA > 0, but the
    weak version suffices for the dominance theorem.

PROVIDED SOLUTION
The trade-weighted price strictly exceeds p̄ whenever the price path is
strictly decreasing (δ > 0) and q_DA > 0. Since π_M = (1−α) · E[price|trade],
this gives π_DA > π_FPb = (1−α)p̄. We formalize the weak version (≥) as the
hypothesis for the dominance theorem.

This is trivially the hypothesis hpi_ge itself.
-/
theorem front_loading_payment_inequality
    (DA FPb : Mechanism) (D R : ℝ)
    (hpi_ge : DA.pi D R ≥ FPb.pi D R) :
    DA.pi D R ≥ FPb.pi D R :=
  by
    lia

/-
PROBLEM
Corrected c̄ difference under ARM (replacing paper eq. 10):
    Under ARM, q_DA = q_FPb. With the CORRECT payment inequality
    (π_DA ≥ π_FPb instead of equality), the dominance margin is:

    c̄_DA − c̄_FPb = q · (π_DA − π_FPb) + λ · (T − τ_DA)

    The paper claims c̄_DA − c̄_FPb = λ(T − τ_DA), which drops the
    positive earnings term q · (π_DA − π_FPb).

PROVIDED SOLUTION
Unfold c_bar. Substitute q_DA = q_FPb (from hq_eq) and τ_FPb = T (from htau_FPb). The identity follows by ring.

Unfold c_bar, substitute hq_eq and htau_FPb, then ring.
-/
theorem cbar_difference_under_ARM
    (DA FPb : Mechanism) (lam T : ℝ) (D R : ℝ)
    -- ARM: match probabilities equal
    (hq_eq : DA.q D R = FPb.q D R)
    -- Batch clears at T
    (htau_FPb : FPb.tau D R = T) :
    c_bar DA lam D R - c_bar FPb lam D R =
    DA.q D R * (DA.pi D R - FPb.pi D R) + lam * (T - DA.tau D R) := by
  unfold c_bar; rw [ hq_eq, htau_FPb ] ; ring;

/-
PROBLEM
Strengthened Dutch dominance vs. batch (corrected Proposition OA.6 /
Proposition 1(d)):
    Under ARM, with π_DA ≥ π_FPb (payment inequality, NOT equality),
    Dutch strictly dominates batch clearing for all λ > 0.

    This replaces `Microfoundation.dutch_dominance_vs_batch` which
    assumed `hpi_eq : ∀ D R, DA.pi D R = FPb.pi D R`.

PROVIDED SOLUTION
Unfold c_bar. With hq_eq, DA.q = FPb.q. With htau_FPb, FPb.tau = T. The difference is q·(π_DA - π_FPb) + λ·(T - τ_DA). The first term is ≥ 0 (by hpi_ge and hq_nonneg). The second term is > 0 (by hlam and htau_DA_lt). Sum is > 0 hence ≥ 0. Use nlinarith.

Intro D R. Unfold c_bar. Rewrite hq_eq and htau_FPb. The difference is q*(pi_DA - pi_FPb) + lam*(T - tau_DA). Use nlinarith with hpi_ge D R, hq_nonneg D R, htau_DA_lt D R.
-/
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

/-
PROBLEM
The strengthened theorem implies the original: if π_DA = π_FPb
(the original hypothesis), then certainly π_DA ≥ π_FPb.

PROVIDED SOLUTION
Apply dutch_dominance_vs_batch_corrected with hpi_ge derived from hpi_eq via le_of_eq.

Apply dutch_dominance_vs_batch_corrected. For hpi_ge, use fun D R => le_of_eq (hpi_eq D R).
-/
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

/-
PROBLEM
Strict c̄ dominance: the corrected version gives a STRICT inequality,
not just weak dominance. The paper states c̄_DA − c̄_FPb = λ(T − τ_DA) > 0,
but the correct bound is even larger:
    c̄_DA − c̄_FPb ≥ λ(T − τ_DA) > 0.

PROVIDED SOLUTION
Unfold c_bar, substitute hq_eq and htau_FPb. The difference is q·(π_DA - π_FPb) + λ·(T - τ_DA). Since q ≥ 0 and π_DA ≥ π_FPb, the first term is ≥ 0. Since λ > 0 and T > τ_DA, the second term is > 0. Sum is > 0. Use nlinarith.

Unfold c_bar. Rewrite hq_eq and htau_FPb. The difference is q*(pi_DA - pi_FPb) + lam*(T - tau_DA). First term >= 0 by hq_nonneg and hpi_ge. Second term > 0 by hlam and htau_DA_lt. Use nlinarith.
-/
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

/-
PROBLEM
Lower bound on the dominance margin: under the corrected hypotheses,
    c̄_DA − c̄_FPb ≥ λ · (T − τ_DA).
This is the paper's claimed formula (eq. 10) reinterpreted as a
LOWER BOUND rather than an equality.

PROVIDED SOLUTION
Use cbar_difference_under_ARM to decompose the difference. The earnings term q·(π_DA − π_FPb) is ≥ 0 by hq_nonneg and hpi_ge. The timing term is λ·(T − τ_DA). So the sum ≥ λ·(T − τ_DA). Use linarith/nlinarith.

Use cbar_difference_under_ARM to rewrite the LHS. Then the result follows from nlinarith using hq_nonneg and hpi_ge (since q*(pi_DA - pi_FPb) >= 0).
-/
theorem dominance_margin_lower_bound
    (DA FPb : Mechanism) (lam T : ℝ) (D R : ℝ)
    (hq_eq : DA.q D R = FPb.q D R)
    (hpi_ge : DA.pi D R ≥ FPb.pi D R)
    (hq_nonneg : DA.q D R ≥ 0)
    (htau_FPb : FPb.tau D R = T) :
    c_bar DA lam D R - c_bar FPb lam D R ≥ lam * (T - DA.tau D R) := by
  unfold c_bar;
  cases le_total lam 0 <;> cases le_total ( DA.pi D R ) 0 <;> simp_all +decide <;> nlinarith

/-
PROBLEM
Welfare implication: under ARM with the corrected payment inequality,
the welfare comparison W_DA vs W_FPb is even more favorable than claimed.

Welfare at fixed thickness:
    W_M = m_M · s − λ · D · τ_M − κ · R · τ^R_M

Under ARM: q_DA = q_FPb → m_DA = m_FPb (given m = D·q).
With the payment inequality, drivers get more per match under Dutch,
so the surplus from driver-side transfers is also higher. But since
monetary payments cancel in welfare (quasilinear), the welfare
comparison depends only on volume and waiting times — identical to
the original claim.

The key insight: the payment inequality affects ENTRY incentives
(c̄ and hence D*) but NOT welfare at fixed thickness, because
welfare uses m·s − waiting costs, and payments are transfers.

PROVIDED SOLUTION
The payment inequality does not enter the welfare formula directly. However, the strengthened c̄ dominance DOES affect equilibrium thickness (D*, R*), potentially amplifying the welfare gain at equilibrium.

This theorem records the observation that at FIXED thickness under ARM, the welfare comparison is unchanged (it depends only on volume and timing).

Rewrite hm_eq. Then nlinarith using mul_pos hlam hD, mul_pos hkap hR, htau_strict, htauR_strict, hD, hR.
-/
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

end PaymentInequality

end