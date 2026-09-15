import LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.DenominatorBound

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaC2LeftTail
open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem left_numerator_bound {s : ℂ} {eta r : ℝ} {m : ℕ}
    (he : 10 ≤ eta) (hmL : eta - 1 ≤ m) (hmU : (m : ℝ) ≤ eta)
    (hs : s.re ≤ 1) (ht : s.im = 2 * Real.pi * eta ^ 2) (hr : 0 ≤ r) :
    ‖rsHankelNumerator s m (rsC2LeftPoint eta m r)‖ ≤
      Real.exp (-Real.pi * eta ^ 2 / 4) *
        Real.exp (-(2 * Real.pi * m * (rsC2Corner eta).im) * r) := by
  have he0 : 0 < eta := by linarith
  have hn := left_norm_ge_one he hmL hr
  have hreal : (s.re - 1) * (rsHankelLog (rsC2LeftPoint eta m r)).re ≤ 0 := by
    rw [(rsHankelLog_coordinates_bound _).1]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.log_nonneg hn)
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
  rw [rsHankelNumerator, norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp only [sub_re, mul_re, sub_im, mul_im, one_re, one_im, sub_zero, ofReal_re,
    ofReal_im, I_re, I_im, mul_zero, mul_one, zero_mul, zero_sub, sub_neg_eq_add,
    zero_add, add_zero, natCast_re, natCast_im, re_ofNat, im_ofNat, ht]
  rw [(rsC2LeftPoint_coordinates eta r m).2]
  nlinarith

theorem left_integrand_bound {s : ℂ} {eta r : ℝ} {m : ℕ}
    (he : 10 ≤ eta) (hmL : eta - 1 ≤ m) (hmU : (m : ℝ) ≤ eta)
    (hs : s.re ≤ 1) (ht : s.im = 2 * Real.pi * eta ^ 2) (hr : 0 ≤ r) :
    ‖rsC2LeftIntegrand s eta m r‖ ≤
      (24 * eta * Real.exp (-Real.pi * eta ^ 2 / 4)) *
        Real.exp (-(2 * Real.pi * m * (rsC2Corner eta).im) * r) := by
  have hn := left_numerator_bound he hmL hmU hs ht hr
  have hd := left_denominator_bound (by linarith : 1 ≤ eta) hmU r
  have hv := left_direction_norm (by linarith : 1 ≤ eta) hmU
  rw [rsC2LeftIntegrand, norm_mul, rsHankelKernel, norm_div]
  calc
    _ ≤ (3 * eta) * ((Real.exp (-Real.pi * eta ^ 2 / 4) *
        Real.exp (-(2 * Real.pi * m * (rsC2Corner eta).im) * r)) / (1 / 8)) := by
      apply mul_le_mul hv _ (by positivity) (by linarith)
      exact div_le_div₀ (by positivity) hn (by norm_num) hd
    _ = _ := by ring

theorem left_decay_rate {eta : ℝ} {m : ℕ}
    (he : 10 ≤ eta) (hm : eta - 1 ≤ m) :
    eta ^ 2 ≤ 2 * Real.pi * m * (rsC2Corner eta).im := by
  have he0 : 0 ≤ eta := by linarith
  have hm' : eta / 2 ≤ (m : ℝ) := by linarith
  have hb : eta / 3 ≤ (rsC2Corner eta).im := by
    linarith [(corner_im_bounds he0).1]
  calc
    _ ≤ 2 * Real.pi * (eta / 2) * (eta / 3) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr Real.pi_gt_three.le) (sq_nonneg eta)]
    _ ≤ _ := by gcongr

theorem left_integral_norm_budget {s : ℂ} {eta : ℝ} {m : ℕ}
    (he : 10 ≤ eta) (hmL : eta - 1 ≤ m) (hmU : (m : ℝ) ≤ eta)
    (hs : s.re ≤ 1) (ht : s.im = 2 * Real.pi * eta ^ 2) :
    (∫ r : ℝ in Ioi 0, ‖rsC2LeftIntegrand s eta m r‖) ≤
      3 * Real.exp (-Real.pi * eta ^ 2 / 4) := by
  have he0 : 0 < eta := by linarith
  have hm : 0 < m := by
    have hh : (0 : ℝ) < m := by linarith
    exact_mod_cast hh
  have hrate := left_decay_rate he hmL
  have hrate0 : 0 < 2 * Real.pi * (m : ℝ) * (rsC2Corner eta).im :=
    lt_of_lt_of_le (sq_pos_of_pos he0) hrate
  have hi := (rsC2Left_integrable hm hs he0).norm
  have hmajor := (integrableOn_exp_mul_Ioi (neg_neg_of_pos hrate0) 0).const_mul
    (24 * eta * Real.exp (-Real.pi * eta ^ 2 / 4))
  have hbound := integral_mono_ae hi hmajor
    (ae_restrict_mem measurableSet_Ioi |>.mono fun r hr =>
      left_integrand_bound he hmL hmU hs ht (le_of_lt hr))
  rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hrate0)] at hbound
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq] at hbound
  have hcoef : 24 * eta / (2 * Real.pi * (m : ℝ) * (rsC2Corner eta).im) ≤ 3 := by
    rw [div_le_iff₀ hrate0]
    nlinarith
  calc
    _ ≤ (24 * eta / (2 * Real.pi * (m : ℝ) * (rsC2Corner eta).im)) *
        Real.exp (-Real.pi * eta ^ 2 / 4) := by
      exact hbound.trans_eq (by ring)
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le

theorem left_integral_budget {s : ℂ} {eta : ℝ} {m : ℕ}
    (he : 10 ≤ eta) (hmL : eta - 1 ≤ m) (hmU : (m : ℝ) ≤ eta)
    (hs : s.re ≤ 1) (ht : s.im = 2 * Real.pi * eta ^ 2) :
    ‖∫ r : ℝ in Ioi 0, rsC2LeftIntegrand s eta m r‖ ≤
      3 * Real.exp (-Real.pi * eta ^ 2 / 4) :=
  (norm_integral_le_integral_norm _).trans (left_integral_norm_budget he hmL hmU hs ht)

end LiuWang.Proof.Campaign20260915.ZetaC2LeftTail
