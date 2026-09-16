import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.MidpointPowerTail
import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.ThreeHalvesCertificates

set_option autoImplicit false
noncomputable section
open Complex

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

theorem rpow_neg_quarter_certificate {x l : ℝ} (hx : 0 < x) (hl : 0 < l)
    (hl4 : l ^ 4 ≤ x) : x ^ (-1 / 4 : ℝ) ≤ 1 / l := by
  have hp : l ^ (4 : ℝ) ≤ x := by simpa only [Real.rpow_ofNat] using! hl4
  have hr := (Real.le_rpow_inv_iff_of_pos hl.le hx.le (by norm_num : (0 : ℝ) < 4)).mpr hp
  norm_num at hr
  rw [neg_div, Real.rpow_neg hx.le, inv_eq_one_div]
  exact one_div_le_one_div_of_le hl hr

theorem rpow_neg_fiveFourths_certificate {x l : ℝ} (hx : 0 < x) (hl : 0 < l)
    (hl4 : l ^ 4 ≤ x) : x ^ (-5 / 4 : ℝ) ≤ 1 / (x * l) := by
  rw [show (-5 / 4 : ℝ) = -1 / 4 - 1 by norm_num, Real.rpow_sub_one hx.ne']
  calc
    x ^ (-1 / 4 : ℝ) / x ≤ (1 / l) / x :=
      div_le_div_of_nonneg_right (rpow_neg_quarter_certificate hx hl hl4) hx.le
    _ = 1 / (x * l) := by ring

theorem norm_zeta_fiveFourths_upper :
    ‖riemannZeta (5 / 4 : ℂ)‖ ≤ 23 / 5 := by
  have h := norm_zeta_real_midpoint_upper (s := 5 / 4) (by norm_num) 3
  have h2 := rpow_neg_fiveFourths_certificate (x := 2) (l := 2973 / 2500)
    (by norm_num) (by norm_num) (by norm_num)
  have h3 := rpow_neg_fiveFourths_certificate (x := 3) (l := 329 / 250)
    (by norm_num) (by norm_num) (by norm_num)
  have h7 := rpow_neg_quarter_certificate (x := 7 / 2) (l := 13677 / 10000)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h h2 h3 h7
  linarith

theorem log_twentyThree_upper : Real.log (23 : ℝ) ≤ 6271 / 2000 := by
  simpa using! log_nat_upper_certificate 23 4 (by norm_num) (by norm_num)
    (6271 / 2000) (by norm_num [Finset.sum_range_succ])

theorem log_five_lower : (8047 / 5000 : ℝ) ≤ Real.log 5 := by
  have h := Real.sum_range_le_log_div
    (by norm_num : (0 : ℝ) ≤ 1 / 9) (by norm_num : (1 / 9 : ℝ) < 1) 8
  rw [show (1 + (1 / 9 : ℝ)) / (1 - 1 / 9) = 5 / 4 by norm_num,
    Real.log_div (by norm_num) (by norm_num)] at h
  have he : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [he] at h
  norm_num [Finset.sum_range_succ] at h
  linarith [Real.log_two_gt_d9]

theorem realLogZeta_fiveFourths_upper : realLogZeta (5 / 4) ≤ 15261 / 10000 := by
  have hz := one_le_norm_zeta_real (x := 5 / 4) (by norm_num)
  have hu : ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ ≤ 23 / 5 := by
    simpa using! norm_zeta_fiveFourths_upper
  have h := Real.log_le_log (by linarith : 0 < ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖) hu
  rw [Real.log_div (by norm_num) (by norm_num)] at h
  unfold realLogZeta
  linarith [log_twentyThree_upper, log_five_lower]

theorem norm_zeta_right_fiveFourths_upper {s : ℂ} (hs : 5 / 4 ≤ s.re) :
    ‖riemannZeta s‖ ≤ 23 / 5 := by
  have h := norm_zeta_le_real (x := 5 / 4) (by norm_num) hs
  have hu : ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ ≤ 23 / 5 := by
    simpa using! norm_zeta_fiveFourths_upper
  exact h.trans hu

theorem log_norm_zeta_right_fiveFourths_upper {s : ℂ} (hs : 5 / 4 ≤ s.re) :
    Real.log ‖riemannZeta s‖ ≤ 15261 / 10000 := by
  have hn := riemannZeta_ne_zero_of_one_lt_re (s := s) (by linarith)
  have h := Real.log_le_log (norm_pos_iff.mpr hn)
    (norm_zeta_le_real (x := 5 / 4) (by norm_num) hs)
  exact h.trans realLogZeta_fiveFourths_upper

#print axioms norm_zeta_fiveFourths_upper
#print axioms realLogZeta_fiveFourths_upper
#print axioms norm_zeta_right_fiveFourths_upper
#print axioms log_norm_zeta_right_fiveFourths_upper

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
