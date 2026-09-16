import LiuWang.Proof.Campaign20260915.ZetaRealNormalization.OriginalScaleBudgets

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Set

namespace LiuWang.Proof.Campaign20260915.ZetaRealNormalization
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaC2LeftTail

theorem critical_left_norm_eight {eta r : ℝ} {m : ℕ}
    (he : 8 ≤ eta) (hm : eta - 1 ≤ m) (hr : 0 ≤ r) :
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
      have hx : 0 ≤ (rsC2Corner eta).re + ((m : ℝ) + 1 / 2) := by positivity
      nlinarith [mul_nonneg (show 0 ≤ r - 1 / 2 by linarith) hx]
    have h := (abs_le.mp (abs_re_le_norm (rsC2LeftPoint eta m r))).1
    linarith

theorem critical_left_numerator_eight {eta r : ℝ} {m : ℕ}
    (he : 8 ≤ eta) (hmL : eta - 1 ≤ m) (hmU : (m : ℝ) ≤ eta) (hr : 0 ≤ r) :
    ‖rsHankelNumerator (criticalPoint (sourceTime eta)) m (rsC2LeftPoint eta m r)‖ ≤
      Real.exp (-Real.pi * eta ^ 2 / 4) *
        Real.exp (-(2 * Real.pi * m * (rsC2Corner eta).im) * r) := by
  have he0 : 0 < eta := by linarith
  have hreal : ((criticalPoint (sourceTime eta)).re - 1) *
      (rsHankelLog (rsC2LeftPoint eta m r)).re ≤ 0 := by
    rw [(rsHankelLog_coordinates_bound _).1]
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num [criticalPoint])
      (Real.log_nonneg (critical_left_norm_eight he hmL hr))
  have hphase := mul_le_mul_of_nonneg_left (left_log_im_lower (m := m) he0 hr)
    (show 0 ≤ 2 * Real.pi * eta ^ 2 by positivity)
  have hmphase : 2 * Real.pi * (m : ℝ) * (rsC2Corner eta).im ≤
      2 * Real.pi * eta * (rsC2Corner eta).im := by
    gcongr
    exact (rsC2Corner_upper he0).2.le
  have hcancel : -(2 * Real.pi * eta ^ 2) * (1 / (2 * Real.sqrt 2) + 1 / 8) +
      2 * Real.pi * eta * (rsC2Corner eta).im = -Real.pi * eta ^ 2 / 4 := by
    rw [(rsC2Corner_coordinates eta).2]
    ring
  rw [rsHankelNumerator, norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have ht : (criticalPoint (sourceTime eta)).im = 2 * Real.pi * eta ^ 2 := by
    simp [criticalPoint, sourceTime_eq]
  simp only [sub_re, mul_re, sub_im, mul_im, one_re, one_im, sub_zero, ofReal_re,
    ofReal_im, I_re, I_im, mul_zero, mul_one, zero_mul, zero_sub, sub_neg_eq_add,
    zero_add, add_zero, natCast_re, natCast_im, re_ofNat, im_ofNat, ht]
  rw [(rsC2LeftPoint_coordinates eta r m).2]
  nlinarith

theorem critical_left_integral_eight {eta : ℝ} (he : 8 ≤ eta) :
    ‖∫ r : ℝ in Ioi 0,
      rsC2LeftIntegrand (criticalPoint (sourceTime eta)) eta ⌊eta⌋₊ r‖ ≤
        3 * Real.exp (-Real.pi * eta ^ 2 / 4) := by
  have he0 : 0 < eta := by linarith
  have hmL : eta - 1 ≤ (⌊eta⌋₊ : ℝ) := by linarith [Nat.lt_floor_add_one eta]
  have hmU := Nat.floor_le he0.le
  have hm : 0 < ⌊eta⌋₊ := Nat.floor_pos.mpr (by linarith)
  have hrate : eta ^ 2 ≤ 2 * Real.pi * (⌊eta⌋₊ : ℝ) * (rsC2Corner eta).im := by
    have hm' : eta / 2 ≤ (⌊eta⌋₊ : ℝ) := by linarith
    have hb : eta / 3 ≤ (rsC2Corner eta).im := by linarith [(corner_im_bounds he0.le).1]
    calc
      _ ≤ 2 * Real.pi * (eta / 2) * (eta / 3) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr Real.pi_gt_three.le) (sq_nonneg eta)]
      _ ≤ _ := by gcongr
  have hrate0 : 0 < 2 * Real.pi * (⌊eta⌋₊ : ℝ) * (rsC2Corner eta).im := by nlinarith
  have hi := (rsC2Left_integrable (s := criticalPoint (sourceTime eta)) hm
    (by norm_num [criticalPoint]) he0).norm
  have hmajor := (integrableOn_exp_mul_Ioi (neg_neg_of_pos hrate0) 0).const_mul
    (24 * eta * Real.exp (-Real.pi * eta ^ 2 / 4))
  have hpoint (r : ℝ) (hr : 0 ≤ r) :
      ‖rsC2LeftIntegrand (criticalPoint (sourceTime eta)) eta ⌊eta⌋₊ r‖ ≤
        (24 * eta * Real.exp (-Real.pi * eta ^ 2 / 4)) *
          Real.exp (-(2 * Real.pi * (⌊eta⌋₊ : ℝ) * (rsC2Corner eta).im) * r) := by
    have hn := critical_left_numerator_eight he hmL hmU hr
    have hd := left_denominator_bound (by linarith : 1 ≤ eta) hmU r
    have hv := left_direction_norm (by linarith : 1 ≤ eta) hmU
    rw [rsC2LeftIntegrand, norm_mul, rsHankelKernel, norm_div]
    calc
      _ ≤ (3 * eta) * ((Real.exp (-Real.pi * eta ^ 2 / 4) *
          Real.exp (-(2 * Real.pi * (⌊eta⌋₊ : ℝ) * (rsC2Corner eta).im) * r)) / (1 / 8)) := by
        apply mul_le_mul hv _ (by positivity) (by linarith)
        exact div_le_div₀ (by positivity) hn (by norm_num) hd
      _ = _ := by ring
  have hbound := integral_mono_ae hi hmajor
    (ae_restrict_mem measurableSet_Ioi |>.mono fun r hr => hpoint r (le_of_lt hr))
  rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hrate0)] at hbound
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq] at hbound
  have hcoef : 24 * eta / (2 * Real.pi * (⌊eta⌋₊ : ℝ) * (rsC2Corner eta).im) ≤ 3 := by
    rw [div_le_iff₀ hrate0]
    nlinarith
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ (24 * eta / (2 * Real.pi * (⌊eta⌋₊ : ℝ) * (rsC2Corner eta).im)) *
        Real.exp (-Real.pi * eta ^ 2 / 4) := hbound.trans_eq (by ring)
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le

theorem critical_outer_exponential {eta : ℝ} (he : 8 ≤ eta) :
    Real.exp (-Real.pi * eta ^ 2 / 4) ≤ 1 / 300 := by
  have hx : 48 ≤ Real.pi * eta ^ 2 / 4 := by
    have hsq : 64 ≤ eta ^ 2 := by nlinarith
    nlinarith [Real.pi_gt_three]
  have h := Real.quadratic_le_exp_of_nonneg (by linarith : 0 ≤ Real.pi * eta ^ 2 / 4)
  have hE : 300 ≤ Real.exp (Real.pi * eta ^ 2 / 4) := by nlinarith
  rw [show -Real.pi * eta ^ 2 / 4 = -(Real.pi * eta ^ 2 / 4) by ring,
    Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) hE

theorem critical_left_absolute {eta : ℝ} (he : 8 ≤ eta) :
    |sourceLeftNormalized eta| ≤ 1 / 100 := by
  have h := (hankel_normalized_re_bound (sourceTime_pos (by linarith)) _).trans
    (critical_left_integral_eight he)
  change |sourceLeftNormalized eta| ≤ _ at h
  exact h.trans ((mul_le_mul_of_nonneg_left (critical_outer_exponential he)
    (by norm_num : (0 : ℝ) ≤ 3)).trans_eq (by norm_num))

theorem critical_right_absolute {eta : ℝ} (he : 8 ≤ eta) :
    |sourceRightNormalized eta| ≤ 1 / 100 := by
  have he0 : 0 < eta := by linarith
  have hx : 30 ≤ sourceTime eta / 11 := by
    have h := sourceTime_lower he0.le
    nlinarith
  have h := Real.quadratic_le_exp_of_nonneg (by linarith : 0 ≤ sourceTime eta / 11)
  have hE : 200 ≤ Real.exp (sourceTime eta / 11) := by nlinarith
  have hq : Real.exp (-sourceTime eta / 11) ≤ 1 / 200 := by
    rw [neg_div, Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hE
  have hc : 11 / (2 * Real.pi) ≤ (2 : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    linarith [Real.pi_gt_three]
  have hp : eta ^ (-(3 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hb := Parent.RealNormalizationAudit.actual_normalized_right (by linarith : 1 ≤ eta)
  exact hb.trans ((mul_le_mul
    (mul_le_mul hc hp (Real.rpow_nonneg he0.le _) (by norm_num)) hq
      (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 2 * 1)).trans_eq (by norm_num))

#print axioms critical_left_integral_eight
#print axioms critical_left_absolute
#print axioms critical_right_absolute

end LiuWang.Proof.Campaign20260915.ZetaRealNormalization
