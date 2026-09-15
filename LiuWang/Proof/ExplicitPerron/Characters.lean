import LiuWang.Proof.ExplicitPerron.Dyadic
import LiuWang.Proof.ExplicitPerron.Mangoldt
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.Coefficient
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LFunctionLogDerivativeRightHalfPlaneBound

/-!
# Actual Dirichlet characters and explicit finite-height errors

The character may be principal. The Chebyshev function is the existing
production sum evaluated at the natural floor, not a Perron-defined object.
-/

set_option autoImplicit false

noncomputable section

open Finset MeasureTheory
open scoped BigOperators

namespace LiuWang.Proof.ExplicitPerron

open BombieriVinogradov.SiegelWalfisz

def psi {q : ℕ} (chi : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  characterChebyshevSum ⌊x⌋₊ chi

theorem psi_eq_sum {q : ℕ} (chi : DirichletCharacter ℂ q) (x : ℝ) :
    psi chi x = ∑ n ∈ Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * chi n := rfl

theorem psi_eq_sum_twisted {q : ℕ} (chi : DirichletCharacter ℂ q) (x : ℝ) :
    psi chi x = ∑ n ∈ Icc 1 ⌊x⌋₊, twistedMangoldtSequence chi n := by
  rw [psi_eq_sum]
  exact sum_congr rfl (fun _ _ => mul_comm _ _)

def characterIntegrand {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (x : ℝ) (s : ℂ) : ℂ :=
  (-logDeriv chi.LFunction s) * ((x : ℂ) ^ s / s)

def centeredIntegrand {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (x y : ℝ) (s : ℂ) : ℂ :=
  (-logDeriv chi.LFunction s) * ((x : ℂ) ^ s - (y : ℂ) ^ s) / s

def logCentralCost (x b : ℝ) : ℝ :=
  ∑ n ∈ central x, Real.log n * (x / n) ^ b / |Real.log (x / n)|

def effectiveError (x b T : ℝ) : ℝ :=
  (x ^ b / Real.log 2 * ((Real.log 4 + 4) * b / (b - 1)) +
    logCentralCost x b) / (Real.pi * T)

theorem twisted_summable {q : ℕ} (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (twistedMangoldtSequence chi) s := by
  exact DirichletCharacter.LSeriesSummable_twist_vonMangoldt chi hs

theorem normSum_twisted_le {q : ℕ} (chi : DirichletCharacter ℂ q)
    {b : ℝ} (hb : 1 < b) :
    (∑' n, ‖LSeries.term (twistedMangoldtSequence chi) (b : ℂ) n‖) ≤
      (Real.log 4 + 4) * b / (b - 1) := by
  apply le_trans _ (mangoldt_normSum_le hb)
  apply (twisted_summable chi (by simpa using hb)).norm.tsum_le_tsum
  · intro n
    apply LSeries.norm_term_le
    simpa only [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      using norm_twistedMangoldtSequence_le_vonMangoldt chi n
  · exact (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (b : ℂ))
      (by simpa using hb)).norm

theorem centralCost_twisted_le {q : ℕ} (chi : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) (b : ℝ) :
    centralCost (twistedMangoldtSequence chi) x b ≤ logCentralCost x b := by
  apply sum_le_sum
  intro n hn
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  exact mul_le_mul_of_nonneg_right
    ((norm_twistedMangoldtSequence_le_vonMangoldt chi n).trans
      ArithmeticFunction.vonMangoldt_le_log) (Real.rpow_nonneg (by positivity) _)

theorem characterIntegrand_eq_series {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (x : ℝ) {s : ℂ} (hs : 1 < s.re) :
    characterIntegrand chi x s = seriesIntegrand (twistedMangoldtSequence chi) x s := by
  rw [characterIntegrand, seriesIntegrand, neg_logDeriv_LFunction_eq_LSeries chi hs]

theorem character_vertical_eq_series {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (x : ℝ) {b : ℝ} (hb : 1 < b) (lo hi : ℝ) :
    vertical (characterIntegrand chi x) b lo hi =
      vertical (seriesIntegrand (twistedMangoldtSequence chi) x) b lo hi := by
  unfold vertical
  congr 2
  funext u
  exact characterIntegrand_eq_series chi x (by simpa using hb)

theorem norm_character_perron_le {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {x b T : ℝ}
    (hx : 0 < x) (hxn : ∀ n : ℕ, x ≠ n) (hb : 1 < b) (hT : 0 < T) :
    ‖vertical (characterIntegrand chi x) b (-T) T - psi chi x‖ ≤
      effectiveError x b T := by
  rw [character_vertical_eq_series chi x hb, psi_eq_sum_twisted]
  apply (norm_vertical_sub_sum_le_dyadic (twistedMangoldtSequence chi)
    hx hxn (zero_lt_one.trans hb) hT (twisted_summable chi (by simpa using hb))).trans
  unfold effectiveError
  gcongr
  · exact normSum_twisted_le chi hb
  · exact centralCost_twisted_le chi hx b

theorem norm_logDeriv_le {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    ‖-logDeriv chi.LFunction s‖ ≤ (Real.log 4 + 4) * s.re / (s.re - 1) := by
  have h := norm_neg_logDeriv_LFunction_le_zeta_re chi hs
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (s := (s.re : ℂ)) (by simpa using hs), ← mangoldt_normSum_eq_norm] at h
  simpa only [logDeriv_apply, neg_div] using h.trans (mangoldt_normSum_le hs)

end LiuWang.Proof.ExplicitPerron
