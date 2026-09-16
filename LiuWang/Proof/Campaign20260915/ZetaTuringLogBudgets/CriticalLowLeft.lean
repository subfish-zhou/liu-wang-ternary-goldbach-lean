import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.LowCriticalJn

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Set

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaRealNormalization
open LiuWang.Proof.Campaign20260915.ZetaC2LeftTail

theorem critical_left_norm_lower {eta r : ℝ} {m : ℕ}
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
  · have hneg : (rsC2LeftPoint eta m r).re ≤ -1 := by
      rw [(rsC2LeftPoint_coordinates eta r m).1]
      have hcoef : 0 ≤ (rsC2Corner eta).re + ((m : ℝ) + 1 / 2) := by positivity
      nlinarith [mul_nonneg (show 0 ≤ r - 1 / 2 by linarith) hcoef]
    have hnorm := (abs_le.mp (abs_re_le_norm (rsC2LeftPoint eta m r))).1
    linarith

theorem critical_left_pointwise {eta r : ℝ} {m : ℕ}
    (he : 8 ≤ eta) (hmL : eta - 1 ≤ m) (hmU : (m : ℝ) ≤ eta) (hr : 0 ≤ r) :
    ‖rsC2LeftIntegrand (criticalPoint (sourceTime eta)) eta m r‖ ≤
      (24 * eta * Real.exp (-Real.pi * eta ^ 2 / 4)) *
        Real.exp (-(2 * Real.pi * m * (rsC2Corner eta).im) * r) := by
  have he0 : 0 < eta := by linarith
  have ht : sourceTime eta = 2 * Real.pi * eta ^ 2 := by
    rw [sourceTime, mul_pow, rsSaddleScale_sq]
  have hn := critical_left_norm_lower he hmL hr
  have hlog : 0 ≤ (rsHankelLog (rsC2LeftPoint eta m r)).re := by
    rw [(rsHankelLog_coordinates_bound _).1]
    exact Real.log_nonneg hn
  have harg := left_log_im_lower (m := m) he0 hr
  have hphase := mul_le_mul_of_nonneg_left harg
    (show 0 ≤ 2 * Real.pi * eta ^ 2 by positivity)
  have hmphase : 2 * Real.pi * (m : ℝ) * (rsC2Corner eta).im ≤
      2 * Real.pi * eta * (rsC2Corner eta).im := by
    gcongr
    exact (rsC2Corner_upper he0).2.le
  have hcancel : -(2 * Real.pi * eta ^ 2) * (1 / (2 * Real.sqrt 2) + 1 / 8) +
      2 * Real.pi * eta * (rsC2Corner eta).im = -Real.pi * eta ^ 2 / 4 := by
    rw [(rsC2Corner_coordinates eta).2]
    ring
  have hnum : ‖rsHankelNumerator (criticalPoint (sourceTime eta)) m (rsC2LeftPoint eta m r)‖ ≤
      Real.exp (-Real.pi * eta ^ 2 / 4) *
        Real.exp (-(2 * Real.pi * m * (rsC2Corner eta).im) * r) := by
    rw [rsHankelNumerator, norm_exp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    simp only [sub_re, mul_re, sub_im, mul_im, one_re, one_im, sub_zero, ofReal_re,
      ofReal_im, I_re, I_im, mul_zero, mul_one, zero_mul, zero_sub, sub_neg_eq_add,
      zero_add, add_zero, natCast_re, natCast_im, re_ofNat, im_ofNat, criticalPoint, ht]
    rw [(rsC2LeftPoint_coordinates eta r m).2]
    nlinarith
  have hd := left_denominator_bound (by linarith : 1 ≤ eta) hmU r
  have hv := left_direction_norm (by linarith : 1 ≤ eta) hmU
  rw [rsC2LeftIntegrand, norm_mul, rsHankelKernel, norm_div]
  calc
    _ ≤ (3 * eta) * ((Real.exp (-Real.pi * eta ^ 2 / 4) *
        Real.exp (-(2 * Real.pi * m * (rsC2Corner eta).im) * r)) / (1 / 8)) := by
      apply mul_le_mul hv _ (by positivity) (by linarith)
      exact div_le_div₀ (by positivity) hnum (by norm_num) hd
    _ = _ := by ring

theorem critical_left_norm_integral {eta : ℝ} (he : 8 ≤ eta) :
    (∫ r : ℝ in Ioi 0, ‖rsC2LeftIntegrand (criticalPoint (sourceTime eta)) eta ⌊eta⌋₊ r‖) ≤
      3 * Real.exp (-Real.pi * eta ^ 2 / 4) := by
  have he0 : 0 < eta := by linarith
  have hmL : eta - 1 ≤ (⌊eta⌋₊ : ℝ) := by linarith [Nat.self_sub_floor_lt_one eta]
  have hmU := Nat.floor_le he0.le
  have hm := Nat.floor_pos.mpr (show 1 ≤ eta by linarith)
  have hrate : eta ^ 2 ≤ 2 * Real.pi * ⌊eta⌋₊ * (rsC2Corner eta).im := by
    have hm' : eta / 2 ≤ (⌊eta⌋₊ : ℝ) := by linarith
    have hb : eta / 3 ≤ (rsC2Corner eta).im := by
      linarith [(corner_im_bounds he0.le).1]
    calc
      _ ≤ 2 * Real.pi * (eta / 2) * (eta / 3) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr Real.pi_gt_three.le) (sq_nonneg eta)]
      _ ≤ _ := by gcongr
  have hrate0 := lt_of_lt_of_le (sq_pos_of_pos he0) hrate
  have hi := (rsC2Left_integrable hm
    (by norm_num [criticalPoint] : (criticalPoint (sourceTime eta)).re ≤ 1) he0).norm
  have hmajor := (integrableOn_exp_mul_Ioi (neg_neg_of_pos hrate0) 0).const_mul
    (24 * eta * Real.exp (-Real.pi * eta ^ 2 / 4))
  have hbound := integral_mono_ae hi hmajor
    (ae_restrict_mem measurableSet_Ioi |>.mono fun r hr =>
      critical_left_pointwise he hmL hmU (le_of_lt hr))
  rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hrate0)] at hbound
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq] at hbound
  have hcoef : 24 * eta / (2 * Real.pi * (⌊eta⌋₊ : ℝ) * (rsC2Corner eta).im) ≤ 3 := by
    rw [div_le_iff₀ hrate0]
    nlinarith
  calc
    _ ≤ (24 * eta / (2 * Real.pi * (⌊eta⌋₊ : ℝ) * (rsC2Corner eta).im)) *
        Real.exp (-Real.pi * eta ^ 2 / 4) := hbound.trans_eq (by ring)
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le

theorem critical_left_normalized_budget {eta : ℝ} (he : 8 ≤ eta) :
    |sourceLeftNormalized eta| ≤ 1 / 10 := by
  have he0 : 0 < eta := by linarith
  have h := (hankel_normalized_re_bound (sourceTime_pos he0)
    (∫ r : ℝ in Ioi 0, rsC2LeftIntegrand (criticalPoint (sourceTime eta)) eta ⌊eta⌋₊ r)).trans
      ((norm_integral_le_integral_norm _).trans (critical_left_norm_integral he))
  have hx : 30 ≤ Real.exp (Real.pi * eta ^ 2 / 4) := by
    have harg : 30 ≤ 1 + Real.pi * eta ^ 2 / 4 := by
      nlinarith [Real.pi_gt_three, sq_nonneg (eta - 8)]
    exact harg.trans (by linarith [Real.add_one_le_exp (Real.pi * eta ^ 2 / 4)])
  apply h.trans
  rw [show -Real.pi * eta ^ 2 / 4 = -(Real.pi * eta ^ 2 / 4) by ring,
    Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  linarith

#print axioms critical_left_norm_lower
#print axioms critical_left_pointwise
#print axioms critical_left_norm_integral
#print axioms critical_left_normalized_budget

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
