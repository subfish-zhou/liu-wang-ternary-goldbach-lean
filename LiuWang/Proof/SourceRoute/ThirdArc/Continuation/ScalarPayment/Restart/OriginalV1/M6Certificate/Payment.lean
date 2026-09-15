import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.M6Certificate.Constants
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.M6Certificate.FiniteIntegral

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.WeightedLowZeros.Continuation

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.M6Certificate

theorem original_finite_scalar_certificate {L : ℝ} (hL : 3100 ≤ L) :
    m6OriginalScalar L ≤
      70000 * L ^ 4 * sourceNu (L ^ 6) *
        ((10 / 9 : ℝ) * Real.exp (-11.3) *
          (Real.exp (-(9 / 10 : ℝ) * Real.log (10 * Real.pi * L ^ 7)) -
            Real.exp (-(9 / 10 : ℝ) * Real.log (L ^ 21)))) := by
  have hnu := (sourceNu_sixth_bounds hL).1
  exact mul_le_mul_of_nonneg_left
    (original_finite_integral_certificate hL
      (original_log_interval hL).1 (original_log_interval hL).2) (by positivity)

theorem original_scalar_global_reduction {L : ℝ} (hL : 3100 ≤ L) :
    m6OriginalScalar L ≤ (700000 / 3100 : ℝ) * Real.exp (-24.76) := by
  have hL0 : 0 < L := by linarith
  have hnu := sourceNu_sixth_bounds hL
  have hnu0 := hnu.1
  have hl : 8 ≤ Real.log L :=
    log_3100_bounds.1.trans (Real.log_le_log (by norm_num) hL)
  have hfactor : 70000 * L ^ 4 * sourceNu (L ^ 6) ≤
      70000 * L ^ 4 * (9 * (L / 3100)) :=
    mul_le_mul_of_nonneg_left hnu.2 (by positivity)
  have hlog : 5 * Real.log L - (9 / 10 : ℝ) * Real.log (10 * Real.pi * L ^ 7) -
      11.3 ≤ -24.76 := by
    rw [Real.log_mul (by positivity : (10 * Real.pi : ℝ) ≠ 0) (pow_pos hL0 7).ne',
      Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [log_ten_pi_bounds.1]
  have hid : 70000 * L ^ 4 * (9 * (L / 3100)) *
      ((10 / 9 : ℝ) * Real.exp (-11.3) *
        Real.exp (-(9 / 10 : ℝ) * Real.log (10 * Real.pi * L ^ 7))) =
      (700000 / 3100 : ℝ) *
        Real.exp (5 * Real.log L - (9 / 10 : ℝ) * Real.log (10 * Real.pi * L ^ 7) -
          11.3) := by
    have he : Real.exp (5 * Real.log L) = L ^ (5 : ℕ) := by
      rw [show (5 : ℝ) = (5 : ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log hL0]
    rw [show 5 * Real.log L - (9 / 10 : ℝ) * Real.log (10 * Real.pi * L ^ 7) - 11.3 =
      5 * Real.log L + (-(9 / 10 : ℝ) * Real.log (10 * Real.pi * L ^ 7)) + (-11.3) by ring,
      Real.exp_add, Real.exp_add, he]
    ring
  calc
    _ ≤ _ := original_finite_scalar_certificate hL
    _ ≤ 70000 * L ^ 4 * sourceNu (L ^ 6) *
        ((10 / 9 : ℝ) * Real.exp (-11.3) *
          Real.exp (-(9 / 10 : ℝ) * Real.log (10 * Real.pi * L ^ 7))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left (sub_le_self _ (Real.exp_pos _).le) (by positivity)
    _ ≤ 70000 * L ^ 4 * (9 * (L / 3100)) *
        ((10 / 9 : ℝ) * Real.exp (-11.3) *
          Real.exp (-(9 / 10 : ℝ) * Real.log (10 * Real.pi * L ^ 7))) :=
      mul_le_mul_of_nonneg_right hfactor (by positivity)
    _ = _ := hid
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hlog) (by norm_num)

theorem m6OriginalScalar_le (L : ℝ) (hL : 3100 ≤ L) :
    m6OriginalScalar L ≤ 6 / 1000000000 :=
  (original_scalar_global_reduction hL).trans endpoint_rational_certificate

theorem equation_5_44_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q)
    (hnu : sourceNu q ≤ sourceNu (sourceL N ^ 6)) :
    sourceM6 N q ≤ (6 / 1000000000 : ℝ) * (N : ℝ) / sourceL N := by
  have hL0 := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  have h := mul_le_mul_of_nonneg_left (m6OriginalScalar_le (sourceL N) (sourceL_ge_3100 hN))
    (show 0 ≤ (N : ℝ) / sourceL N by positivity)
  exact (equation_5_44_original_integral hN hq hq1 htotient hnu).trans
    (h.trans_eq (by ring))

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.M6Certificate
