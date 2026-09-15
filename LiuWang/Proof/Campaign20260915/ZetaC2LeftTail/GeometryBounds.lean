import LiuWang.Proof.Campaign20260915.ZetaValidation.SourceC2Integral
import LiuWang.Proof.Campaign20260915.ZetaValidation.RationalAngle

set_option autoImplicit false
noncomputable section
open Complex Set

namespace LiuWang.Proof.Campaign20260915.ZetaC2LeftTail
open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem corner_im_bounds {eta : ℝ} (he : 0 ≤ eta) :
    7 / 20 * eta ≤ (rsC2Corner eta).im ∧
      (rsC2Corner eta).im ≤ 5 / 14 * eta := by
  have hs0 := Real.sqrt_nonneg (2 : ℝ)
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsL : 7 / 5 ≤ Real.sqrt 2 := by nlinarith
  have hsU : Real.sqrt 2 ≤ 10 / 7 := by nlinarith
  rw [(rsC2Corner_coordinates eta).2]
  constructor
  · rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hsU he]
  · rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hsL he]

theorem corner_re_add_im (eta : ℝ) :
    (rsC2Corner eta).re + (rsC2Corner eta).im = eta := by
  rw [(rsC2Corner_coordinates eta).1, (rsC2Corner_coordinates eta).2]
  ring

theorem left_norm_ge_one {eta r : ℝ} {m : ℕ}
    (he : 10 ≤ eta) (hm : eta - 1 ≤ m) (hr : 0 ≤ r) :
    1 ≤ ‖rsC2LeftPoint eta m r‖ := by
  have he0 : 0 < eta := by linarith
  obtain ⟨hbL, hbU⟩ := corner_im_bounds he0.le
  have hab := corner_re_add_im eta
  obtain ⟨ha, hb⟩ := rsC2Corner_upper he0
  by_cases hr' : r ≤ 1 / 2
  · have hi : 1 ≤ (rsC2LeftPoint eta m r).im := by
      rw [(rsC2LeftPoint_coordinates eta r m).2]
      nlinarith
    exact hi.trans ((le_abs_self _).trans (abs_im_le_norm _))
  · have hi : (rsC2LeftPoint eta m r).re ≤ -1 := by
      rw [(rsC2LeftPoint_coordinates eta r m).1]
      have hx : (rsC2Corner eta).re + ((m : ℝ) + 1 / 2) ≥ 0 := by positivity
      nlinarith [mul_nonneg (show 0 ≤ r - 1 / 2 by linarith) hx]
    have h := (abs_le.mp (abs_re_le_norm (rsC2LeftPoint eta m r))).1
    linarith

theorem left_direction_norm {eta : ℝ} {m : ℕ}
    (he : 1 ≤ eta) (hm : (m : ℝ) ≤ eta) :
    ‖rsC2LeftDirection eta m‖ ≤ 3 * eta := by
  have he0 : 0 < eta := by linarith
  obtain ⟨ha, hb⟩ := rsC2Corner_upper he0
  have h := norm_le_abs_re_add_abs_im (rsC2LeftDirection eta m)
  have hR : (rsC2LeftDirection eta m).re = -((m : ℝ) + 1 / 2) -
      (rsC2Corner eta).re := by simp [rsC2LeftDirection]
  have hI : (rsC2LeftDirection eta m).im = -(rsC2Corner eta).im := by
    simp [rsC2LeftDirection]
  rw [hR, hI, abs_of_neg (by linarith [Nat.cast_nonneg (α := ℝ) m]),
    abs_neg, abs_of_pos hb] at h
  linarith [corner_re_add_im eta]

theorem left_axis_window {eta r : ℝ} {m : ℕ}
    (he : 1 ≤ eta) (hm : (m : ℝ) ≤ eta)
    (hr : |(rsC2LeftPoint eta m r).im| ≤ 1 / 32) :
    |(rsC2LeftPoint eta m r).re + ((m : ℝ) + 1 / 2)| ≤ 1 / 4 := by
  have he0 : 0 < eta := by linarith
  obtain ⟨ha, hb⟩ := rsC2Corner_upper he0
  obtain ⟨hbL, hbU⟩ := corner_im_bounds he0.le
  have hab := corner_re_add_im eta
  have hcoef : (rsC2Corner eta).re + ((m : ℝ) + 1 / 2) ≤
      8 * (rsC2Corner eta).im := by linarith
  have hfac : |1 - r| * (rsC2Corner eta).im ≤ 1 / 32 := by
    simpa only [(rsC2LeftPoint_coordinates eta r m).2, abs_mul, abs_of_pos hb] using hr
  have hR : (rsC2LeftPoint eta m r).re + ((m : ℝ) + 1 / 2) =
      (1 - r) * ((rsC2Corner eta).re + ((m : ℝ) + 1 / 2)) := by
    rw [(rsC2LeftPoint_coordinates eta r m).1]
    ring
  rw [hR, abs_mul, abs_of_nonneg
    (show 0 ≤ (rsC2Corner eta).re + ((m : ℝ) + 1 / 2) by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hcoef (abs_nonneg (1 - r))]

theorem arctan_eight_fifteenths :
    5 / 14 + 1 / 8 ≤ Real.arctan (8 / 15) := by
  have h := rationalAtanTaylor_error 8 (q := 1 / 4) (by norm_num)
  norm_num [rationalAtanTaylor, imagIPower, Finset.sum_range_succ] at h
  have ha := Real.arctan_add (x := 1 / 4) (y := 1 / 4) (by norm_num)
  norm_num at ha
  rw [abs_le] at h
  linarith [h.1]

theorem left_log_im_lower {eta r : ℝ} {m : ℕ}
    (he : 0 < eta) (hr : 0 ≤ r) :
    1 / (2 * Real.sqrt 2) + 1 / 8 ≤
      (rsHankelLog (rsC2LeftPoint eta m r)).im := by
  have hb := (rsC2Corner_upper he).2
  obtain ⟨hbL, hbU⟩ := corner_im_bounds he.le
  have hab := corner_re_add_im eta
  have hconst : 1 / (2 * Real.sqrt 2) ≤ 5 / 14 := by
    have h := (corner_im_bounds (eta := 1) (by norm_num)).2
    simpa only [(rsC2Corner_coordinates 1).2, mul_one] using h
  by_cases hx : 0 < (rsC2LeftPoint eta m r).re
  · have hratio : 8 / 15 ≤ (rsC2LeftPoint eta m r).im /
        (rsC2LeftPoint eta m r).re := by
      rw [le_div_iff₀ hx]
      rw [(rsC2LeftPoint_coordinates eta r m).1] at hx
      rw [(rsC2LeftPoint_coordinates eta r m).1,
        (rsC2LeftPoint_coordinates eta r m).2]
      have hr1 : r < 1 := by
        by_contra! hh
        have h := mul_nonpos_of_nonpos_of_nonneg (by linarith : 1 - r ≤ 0)
          (rsC2Corner_upper he).1.le
        have h' : 0 ≤ r * ((m : ℝ) + 1 / 2) := by positivity
        linarith
      have hbase : 8 / 15 * (rsC2Corner eta).re ≤ (rsC2Corner eta).im := by
        linarith
      nlinarith [mul_le_mul_of_nonneg_left hbase (by linarith : 0 ≤ 1 - r),
        mul_nonneg hr (show 0 ≤ (m : ℝ) + 1 / 2 by positivity)]
    rw [rsHankelLog_eq_principal hx, log_im_of_re_pos hx]
    have h := arctan_eight_fifteenths.trans (Real.arctan_le_arctan_iff.mpr hratio)
    linarith
  · have hi : 0 ≤ (-I * rsC2LeftPoint eta m r).im := by
      simp only [mul_im, I_re, neg_im, I_im, zero_mul, neg_mul, one_mul,
        zero_add]
      linarith
    have harg := arg_nonneg_iff.mpr hi
    have hlog : (rsHankelLog (rsC2LeftPoint eta m r)).im =
        (-I * rsC2LeftPoint eta m r).arg + Real.pi / 2 := by
      simp [rsHankelLog, log_im]
    rw [hlog]
    linarith [Real.pi_gt_three]

end LiuWang.Proof.Campaign20260915.ZetaC2LeftTail
