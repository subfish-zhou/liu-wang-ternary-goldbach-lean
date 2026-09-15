import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.CountScalar
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source26Certificate.Kernel

set_option autoImplicit false
noncomputable section

open Complex

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source20

theorem shifted_log {y : ℝ} (hy : 3.36 ≤ y) :
    Real.log (2 + y) ≤ Real.log y + 0.47 := by
  have hy0 : 0 < y := by linarith
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.47) 4
  norm_num [Finset.sum_range_succ] at he
  have hr : (2 + y) / y ≤ Real.exp 0.47 := by
    apply (div_le_iff₀ hy0).mpr
    have hh := mul_le_mul_of_nonneg_left he hy0.le
    nlinarith
  have hh := (Real.log_le_iff_le_exp (by positivity : 0 < (2 + y) / y)).mpr hr
  rw [Real.log_div (by positivity) hy0.ne'] at hh
  linarith

theorem norm_ge_height (a y : ℝ) :
    y ≤ ‖(a : ℂ) + (y : ℂ) * I‖ := by
  simpa using im_le_norm ((a : ℂ) + (y : ℂ) * I)

theorem log_norm_height {a y : ℝ} (hy : 0 < y) :
    Real.log ‖(a : ℂ) + (y : ℂ) * I‖ ≤ Real.log y + a ^ 2 / (2 * y ^ 2) := by
  have hn := norm_ge_height a y
  have hn0 : 0 < ‖(a : ℂ) + (y : ℂ) * I‖ := hy.trans_le hn
  have hs : ‖(a : ℂ) + (y : ℂ) * I‖ ^ 2 = a ^ 2 + y ^ 2 := by
    rw [← normSq_eq_norm_sq]
    simp [normSq_apply, sq]
  have ht := Real.log_le_sub_one_of_pos
    (div_pos (sq_pos_of_pos hn0) (sq_pos_of_pos hy))
  rw [Real.log_div (pow_ne_zero _ hn0.ne') (pow_ne_zero _ hy.ne'),
    Real.log_pow, Real.log_pow, hs] at ht
  have he : (a ^ 2 + y ^ 2) / y ^ 2 - 1 = a ^ 2 / y ^ 2 := by
    field_simp
    ring
  rw [he] at ht
  norm_num at ht
  rw [show a ^ 2 / (2 * y ^ 2) = (a ^ 2 / y ^ 2) / 2 by ring]
  linarith

theorem reciprocal_norm {a y : ℝ} (hy : 0 < y) :
    1 / ‖(a : ℂ) + (y : ℂ) * I‖ ≤ 1 / y :=
  one_div_le_one_div_of_le hy (norm_ge_height a y)

theorem log_two_pi_payment :
    (7 / 8 : ℝ) ≤ (1 + Real.log (2 * Real.pi)) / Real.pi := by
  apply (le_div_iff₀ Real.pi_pos).mpr
  linarith [log_two_pi_lower, Real.pi_lt_d4]

theorem source_log_bounds {L : ℝ} (hL : 3100 ≤ L) :
    5 ≤ Real.log L ∧ Real.log 3.36 ≤ 2 := by
  have hp := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 5
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  constructor
  · exact (Real.le_log_iff_exp_le (by linarith)).mpr (hp.trans (by linarith))
  · apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    have he := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    norm_num at he
    linarith

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source20
