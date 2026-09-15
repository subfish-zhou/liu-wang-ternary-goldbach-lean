import LiuWang.Proof.MultiZeroRepulsion.Continuation.GeneralT1Nondegenerate

/-! Simultaneous principal-product poles can be paid without the old constant loss per selected zero. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.MultiZeroRepulsion.Continuation

theorem t1_sigma_tau {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 51 / 50) :
    3 / 5 ≤ stechkinSigma sigma - 1 ∧ stechkinSigma sigma - 1 ≤ 16 / 25 := by
  have hh := stechkinSigma_bounds hs (show sigma ≤ 23 / 20 by linarith)
  have he := stechkinSigma_equation sigma
  constructor
  · linarith [hh.1]
  · nlinarith [hh.1]

theorem t1_pole_high_nonpos {sigma t : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 51 / 50)
    (ht : 1 / 4 ≤ |t|) : poleDifference sigma t ≤ 0 := by
  have hv := t1_sigma_tau hs hs1
  have hv0 : 0 < stechkinSigma sigma - 1 := by linarith [hv.1]
  have hu0 : 0 < sigma - 1 := by linarith
  have hkv : 33 / 125 ≤ stechkinK * (stechkinSigma sigma - 1) := by
    have hh := mul_le_mul stechkinK_ge hv.1 (by norm_num) stechkinK_mem.1
    norm_num at hh
    exact hh
  have ht2 : 1 / 16 ≤ t ^ 2 := by nlinarith [sq_abs t]
  have hv2 : (stechkinSigma sigma - 1) ^ 2 ≤ (16 / 25 : ℝ) ^ 2 := by nlinarith [hv.1, hv.2]
  have hprod := mul_le_mul (show sigma - 1 ≤ 1 / 50 by linarith) hv2
    (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 50)
  have hsmall := mul_le_mul_of_nonneg_right (show sigma - 1 ≤ 1 / 50 by linarith) (sq_nonneg t)
  have hlarge := mul_le_mul_of_nonneg_right hkv (sq_nonneg t)
  have hpositive : 0 ≤ stechkinK * (stechkinSigma sigma - 1) * (sigma - 1) ^ 2 := by positivity
  have he : poleDifference sigma t = realKernel (sigma - 1) t -
      stechkinK * realKernel (stechkinSigma sigma - 1) t := by
    simp [poleDifference, realKernel, one_div, Complex.inv_re, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im, pow_two]
  rw [he]
  apply sub_nonpos.mpr
  unfold realKernel
  rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith only [ht2, hprod, hsmall, hlarge, hpositive]

theorem t1_pole_low_saving {sigma t : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 51 / 50)
    (ht : |t| ≤ 1 / 4) :
    poleDifference sigma t ≤ realKernel (sigma - 1) t - 1 / 2 := by
  have hv := t1_sigma_tau hs hs1
  have hv0 : 0 < stechkinSigma sigma - 1 := by linarith [hv.1]
  have hkv : 33 / 125 ≤ stechkinK * (stechkinSigma sigma - 1) := by
    have hh := mul_le_mul stechkinK_ge hv.1 (by norm_num) stechkinK_mem.1
    norm_num at hh
    exact hh
  have ht2 : t ^ 2 ≤ 1 / 16 := by nlinarith [sq_abs t, abs_nonneg t]
  have hv2 : (stechkinSigma sigma - 1) ^ 2 ≤ (16 / 25 : ℝ) ^ 2 := by nlinarith [hv.1, hv.2]
  have hsave : 1 / 2 ≤ stechkinK * realKernel (stechkinSigma sigma - 1) t := by
    unfold realKernel
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith only [hkv, ht2, hv2]
  have he : poleDifference sigma t = realKernel (sigma - 1) t -
      stechkinK * realKernel (stechkinSigma sigma - 1) t := by
    simp [poleDifference, realKernel, one_div, Complex.inv_re, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im, pow_two]
  rw [he]
  linarith

theorem t1_realKernel_quadratic_loss {a u : ℝ} (ha : 9 / 10 ≤ a) :
    1 / a - (3 / 2) * u ^ 2 ≤ realKernel a u := by
  have ha0 : 0 < a := by linarith
  have ha2 : 81 / 100 ≤ a ^ 2 := by nlinarith
  have ha3 := mul_le_mul ha ha2 (by norm_num) ha0.le
  have hden : 2 / 3 ≤ a * (a ^ 2 + u ^ 2) := by
    nlinarith [mul_nonneg ha0.le (sq_nonneg u)]
  have hid : 1 / a - realKernel a u = u ^ 2 / (a * (a ^ 2 + u ^ 2)) := by
    unfold realKernel
    field_simp
    ring
  have hh := div_le_div_of_nonneg_left (sq_nonneg u) (by norm_num : (0 : ℝ) < 2 / 3) hden
  rw [← hid] at hh
  linarith

theorem t1_reflected_small_loss {sigma : ℝ} (hs : 1 < sigma) {rho : ℂ}
    (hr : 9 / 10 ≤ rho.re) (hr1 : rho.re < 1) (t : ℝ) :
    realKernel (sigma - rho.re) (t - rho.im) - (3 / 2) * (t - rho.im) ^ 2 ≤
      reflectedKernel sigma t rho := by
  have hge := stechkinSigma_ge hs
  have h1 := mul_le_mul_of_nonneg_left
    (realKernel_le_inverse (show 0 < stechkinSigma sigma - rho.re by linarith) (t - rho.im)) stechkinK_mem.1
  have h2 := mul_le_mul_of_nonneg_left
    (realKernel_le_inverse (show 0 < stechkinSigma sigma - 1 + rho.re by linarith) (t - rho.im)) stechkinK_mem.1
  have h3 := selected_reflected_scalar hs ⟨by linarith, hr1.le⟩
  have h4 := t1_realKernel_quadratic_loss (a := sigma - 1 + rho.re)
    (u := t - rho.im) (by linarith)
  unfold reflectedKernel
  rw [dampedKernel_eq_realKernel, dampedKernel_eq_realKernel]
  simp only [sub_re, one_re, conj_re, sub_im, one_im, conj_im, sub_neg_eq_add, zero_add]
  rw [show sigma - (1 - rho.re) = sigma - 1 + rho.re by ring,
    show stechkinSigma sigma - (1 - rho.re) = stechkinSigma sigma - 1 + rho.re by ring]
  linarith

theorem t1_two_kernels_pay_pole {sigma t u v : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 51 / 50)
    {rho tau : ℂ} (hr : 9 / 10 ≤ rho.re) (hr1 : rho.re < 1)
    (ht : 9 / 10 ≤ tau.re) (ht1 : tau.re < 1)
    (hgr : 1 - rho.re ≤ sigma - 1) (hgt : 1 - tau.re ≤ sigma - 1)
    (hphase1 : (t - rho.im) ^ 2 = v ^ 2) (hphase2 : (u - tau.im) ^ 2 = v ^ 2) :
    poleDifference sigma v ≤ reflectedKernel sigma t rho + reflectedKernel sigma u tau := by
  by_cases hv : 1 / 4 ≤ |v|
  · have hp := t1_pole_high_nonpos hs hs1 hv
    have h1 : 0 ≤ reflectedKernel sigma t rho :=
      dampedZeroKernel_pair_nonneg hs t ⟨by linarith, hr1.le⟩
    have h2 : 0 ≤ reflectedKernel sigma u tau :=
      dampedZeroKernel_pair_nonneg hs u ⟨by linarith, ht1.le⟩
    exact hp.trans (add_nonneg h1 h2)
  · have hv1 : |v| ≤ 1 / 4 := (lt_of_not_ge hv).le
    have hv2 : v ^ 2 ≤ 1 / 16 := by nlinarith [sq_abs v, abs_nonneg v]
    have hp := t1_pole_low_saving hs hs1 hv1
    have h1 := t1_reflected_small_loss hs hr hr1 t
    have h2 := t1_reflected_small_loss hs ht ht1 u
    have h3 := realKernel_half_pole (u := t - rho.im) (show 0 < sigma - 1 by linarith)
      (show sigma - 1 ≤ sigma - rho.re by linarith) (show sigma - rho.re ≤ 2 * (sigma - 1) by linarith)
    have h4 := realKernel_half_pole (u := u - tau.im) (show 0 < sigma - 1 by linarith)
      (show sigma - 1 ≤ sigma - tau.re by linarith) (show sigma - tau.re ≤ 2 * (sigma - 1) by linarith)
    have he1 : realKernel (sigma - 1) (t - rho.im) = realKernel (sigma - 1) v := by
      simp only [realKernel, hphase1]
    have he2 : realKernel (sigma - 1) (u - tau.im) = realKernel (sigma - 1) v := by
      simp only [realKernel, hphase2]
    rw [he1] at h3
    rw [he2] at h4
    rw [hphase1] at h1
    rw [hphase2] at h2
    linarith only [hp, h1, h2, h3, h4, hv2]

theorem t1_source_pole_domain {x : ℝ} (hx : 8000000000 ≤ x) :
    t1Sigma x ≤ 51 / 50 ∧ 9 / 10 ≤ 1 - (26213 / 100000) / Real.log x := by
  have hL := source_log_twenty_two hx
  have hL0 : 0 < Real.log x := by linarith
  have hs : (9 / 25 : ℝ) / Real.log x ≤ 1 / 50 := by
    apply (div_le_iff₀ hL0).mpr
    linarith
  have hb : (26213 / 100000 : ℝ) / Real.log x ≤ 1 / 10 := by
    apply (div_le_iff₀ hL0).mpr
    linarith
  dsimp [t1Sigma]
  constructor <;> linarith

end LiuWang.Proof.MultiZeroRepulsion.Continuation
