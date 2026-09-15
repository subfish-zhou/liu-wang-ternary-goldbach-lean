import LiuWang.Proof.MajorZeroMomentPayment.Quadratic

/-! Actual-zero specializations and a separate empty-exception consumer.
The ordinary R24-complement packet and M2/M3 are not declared paid here. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.SingularSeries
open LiuWang.Proof.MajorArcApproximation LiuWang.Proof.MajorZeroInteraction

namespace LiuWang.Proof.MajorZeroMomentPayment

theorem actual_exceptional_mixed_moments {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hsmall : (q : ℝ) ≤ sourceP N / 1000)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    0.39 * (N : ℝ)^2 * baseWeight N rho.re ≤
        (finiteMoment N (deltaRadius N q) 1 1 rho).re ∧
    0.39 * (N : ℝ)^2 * baseWeight N rho.re^2 ≤
        (finiteMoment N (deltaRadius N q) 1 rho rho).re ∧
    0.39 * (N : ℝ)^2 * baseWeight N rho.re^3 ≤
        (finiteMoment N (deltaRadius N q) rho rho rho).re := by
  have hq : (q : ℝ) ≤ sourceP N := by linarith [sourceP_pos hN]
  have hi := (exceptionalValues_quadratic_simple hN hq hr).2.2.1
  have he : (rho.re : ℂ) = rho := by apply Complex.ext <;> simp [hi]
  have hv := mem_zeroValues.mp (Finset.mem_filter.mp hr).1
  have hb : 1/2 ≤ rho.re ∧ rho.re ≤ 1 := ⟨hv.2.2.2.2, hv.2.2.1.le⟩
  have h1 := actual_mixed_moment_positive hN (NeZero.pos q) hsmall
    (r := 1) (s := 1) (t := rho.re) (by norm_num) (by norm_num) hb
  have h2 := actual_mixed_moment_positive hN (NeZero.pos q) hsmall
    (r := 1) (s := rho.re) (t := rho.re) (by norm_num) hb hb
  have h3 := actual_mixed_moment_positive hN (NeZero.pos q) hsmall hb hb hb
  have hw : baseWeight N 1 = 1 := by simp [baseWeight]
  simp only [hw, one_mul, Complex.ofReal_one, he] at h1 h2 h3
  exact ⟨h1, by simpa only [pow_two] using h2,
    by simpa only [pow_succ, pow_zero, one_mul] using h3⟩

theorem exceptional_payment_none {N : ℕ}
    (hnone : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      ∀ chi : Character q, exceptionalValues N chi = ∅) :
    totalExceptionalPayment N = 0 := by
  rw [totalExceptionalPayment]
  apply Finset.sum_eq_zero
  intro q hq
  let : NeZero q := ⟨by have := (Finset.mem_Icc.mp hq).1; omega⟩
  exact (exceptionalArc_no_exception N (hnone q hq)).2

theorem lambdaTripleCount_ge_paid_exceptional_decimal {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) :
    0.481660839 * (N : ℝ)^2 + totalExceptionalPayment N +
      (regularInteractionIntegral N).re +
      (∫ alpha in M2 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re +
      (∫ alpha in M3 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re ≤
        lambdaTripleCount N := by
  linarith [lambdaTripleCount_ge_paid_exceptional hN hodd,
    log_power_le_decimal (exp_2000_le_of_exp_3100_le hN)]

theorem lambdaTripleCount_no_exceptional_decimal {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N)
    (hnone : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      ∀ chi : Character q, exceptionalValues N chi = ∅) :
    0.481660839 * (N : ℝ)^2 + (regularInteractionIntegral N).re +
      (∫ alpha in M2 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re +
      (∫ alpha in M3 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re ≤
        lambdaTripleCount N := by
  simpa only [exceptional_payment_none hnone, add_zero] using
    lambdaTripleCount_ge_paid_exceptional_decimal hN hodd

end LiuWang.Proof.MajorZeroMomentPayment
