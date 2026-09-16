import LiuWang.Proof.Campaign20260915.RosserCount.BacklundFiftyTail
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
noncomputable section

open Complex

namespace LiuWang.Proof.Campaign20260915.RosserCount

theorem backlund_log_fifty_lower : (89 / 25 : ℝ) < Real.log 50 := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 36) (by norm_num : (36 : ℝ) ≤ 50)
  have he : Real.log 36 = 2 * (Real.log 2 + Real.log 3) := by
    rw [show (36 : ℝ) = (2 * 3) ^ 2 by norm_num, Real.log_pow,
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [he] at h
  have h2 := (abs_le.mp Real.log_two_near_10).1
  linarith [Real.log_three_gt_d9]

theorem backlund_fifty_original_73 {s : ℂ}
    (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 1) (ht : s.im = 50) :
    ‖riemannZeta s‖ < (2491 / 2500 : ℝ) *
      (25 / Real.pi) ^ ((1 - s.re) / 2) * Real.log 50 := by
  have hp : 1 ≤ (25 / Real.pi) ^ ((1 - s.re) / 2) :=
    Real.one_le_rpow
      ((le_div_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_lt_four]))
      (by linarith)
  have hl : 0 ≤ Real.log 50 := Real.log_nonneg (by norm_num)
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2491 / 2500)) hl
  have hc : (7 / 2 : ℝ) < (2491 / 2500) * Real.log 50 := by
    linarith [backlund_log_fifty_lower]
  exact (backlund_fifty_zeta_bound hs hs' ht).trans
    (hc.trans_le (by simpa only [mul_one] using h))

#print axioms backlund_log_fifty_lower
#print axioms backlund_fifty_original_73

end LiuWang.Proof.Campaign20260915.RosserCount
