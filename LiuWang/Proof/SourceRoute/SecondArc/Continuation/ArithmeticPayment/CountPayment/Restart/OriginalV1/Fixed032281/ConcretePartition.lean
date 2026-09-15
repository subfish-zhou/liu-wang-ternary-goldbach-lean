import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.Constants

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281

theorem lower_endpoint : (25.329413 : ℝ) ≤ lowerLog 3100 := by
  have hs := Real.abs_log_sub_add_sum_range_le (x := (0.16 : ℝ)) (by norm_num) 16
  norm_num [Finset.sum_range_succ] at hs
  have hl := (abs_le.mp hs).1
  have he : Real.log (3.36 : ℝ) = 2 * Real.log 2 + Real.log (0.84 : ℝ) := by
    rw [show (3.36 : ℝ) = 2 ^ (2 : ℕ) * 0.84 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  unfold lowerLog
  rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow, he]
  norm_num only [Nat.cast_ofNat]
  linarith [Real.log_two_gt_d9, log_3100_interval.1]

theorem upper_endpoint : upperLog 3100 ≤ (59.721417 : ℝ) := by
  have hs := Real.abs_log_sub_add_sum_range_le
    (x := (1 - 10 * 3.141593 / 32 : ℝ)) (by norm_num) 8
  norm_num [Finset.sum_range_succ] at hs
  have hl := (abs_le.mp hs).2
  have hb : Real.log (10 * Real.pi) ≤ 5 * Real.log 2 + Real.log (10 * 3.141593 / 32 : ℝ) := by
    have ht := Real.log_le_log (by positivity : 0 < 10 * Real.pi)
      (mul_le_mul_of_nonneg_left Real.pi_lt_d6.le (by norm_num : (0 : ℝ) ≤ 10))
    have he : Real.log (10 * 3.141593 : ℝ) =
        5 * Real.log 2 + Real.log (10 * 3.141593 / 32 : ℝ) := by
      rw [show (10 * 3.141593 : ℝ) = 2 ^ (5 : ℕ) * (10 * 3.141593 / 32) by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
      norm_num
    exact ht.trans_eq he
  unfold upperLog
  rw [Real.log_mul (by positivity : 10 * Real.pi ≠ 0) (by norm_num), Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  norm_num only at hb
  linarith [Real.log_two_lt_d9, log_3100_interval.2]

def fixedPoint (i : ℕ) : ℝ :=
  25.329413 + (59.721417 - 25.329413) * i / 256

def fixedMidpoint (i : ℕ) : ℝ := (fixedPoint i + fixedPoint (i + 1)) / 2

theorem fixedPoint_monotone : Monotone fixedPoint := by
  intro i j hij
  have h : (i : ℝ) ≤ j := Nat.cast_le.mpr hij
  unfold fixedPoint
  linarith

theorem fixed_partition_bound :
    originalDensityScalar 3100 ≤
      (8 * 6.76661 * (1.7810725 * 3.182937 + 2.50637 / 3.182936) * 3100) *
        ∑ i ∈ Finset.range 256,
          FixedIntegral.cellValue 3093.092244719 (fixedPoint i) (fixedPoint (i + 1)) (fixedMidpoint i) := by
  apply FixedIntegral.original_fixed_directed_bound 256 fixedPoint fixedMidpoint
    (fixedPoint_monotone.monotoneOn _)
  · norm_num [fixedPoint]
  · simpa only [fixedPoint, Nat.cast_zero, mul_zero, zero_div, add_zero] using lower_endpoint
  · convert upper_endpoint using 1
    norm_num [fixedPoint]
  · norm_num [fixedPoint]
  · exact window_H_lower
  · intro i _
    have h := fixedPoint_monotone (Nat.le_succ i)
    unfold fixedMidpoint
    exact ⟨by linarith, by linarith⟩
  · exact exp_phase_upper
  · exact exp_euler_upper
  · norm_num
  · exact loglog_interval.1
  · exact loglog_interval.2

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281
