import LiuWang.Proof.Campaign20260915.ZetaJnCentral.TwelfthRadius

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem mediumRadius_data {eta : ℝ} (he : 11 ≤ eta) :
    twelfthRadius eta ≤ eta / 3 ∧ 21 / 10 ≤ twelfthCutoff eta ∧
    twelfthCutoff eta ≤ eta / 2 ∧ twelfthCutoff eta ^ 3 = 27 / 32 * eta := by
  have he0 : 0 < eta := by linarith
  have hR0 := twelfthRadius_pos he0
  have hu : twelfthRadius eta ≤ eta / 3 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) (by positivity)
    rw [twelfthRadius_cube he0]
    have hs : 54 ≤ eta ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hs he0.le]
  have hl : 14 / 5 ≤ twelfthRadius eta := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) hR0.le
    rw [twelfthRadius_cube he0]
    norm_num
    linarith
  refine ⟨hu, ?_, ?_, ?_⟩
  · unfold twelfthCutoff
    linarith
  · unfold twelfthCutoff
    linarith
  · rw [twelfthCutoff, mul_pow, twelfthRadius_cube he0]
    ring

theorem exp_thirty_three_fifths_le : Real.exp (33 / 5) ≤ 750 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (5 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 750)
  have hp : Real.exp (33 / 5) ^ 5 = Real.exp 1 ^ 33 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    norm_num
  rw [hp]
  exact (pow_le_pow_left₀ (Real.exp_pos _).le
    (show Real.exp 1 ≤ 68 / 25 by linarith [Real.exp_one_lt_d9]) 33).trans (by norm_num)

theorem mediumCircle_weight {lambda : ℝ} (hl : 0 < lambda) {z : ℂ}
    (hz : ‖z‖ ≤ lambda / 3) :
    ‖rsSaddleWeight (1 / 2) lambda z‖ ≤
      Real.exp (1 / 4 + 1 / 2 * lambda ^ 2 * (‖z‖ / lambda) ^ 3) := by
  have hu : ‖z / (lambda : ℂ)‖ ≤ 1 / 3 := by
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hl, div_le_iff₀ hl]
    linarith
  have hi : (1 - ‖z / (lambda : ℂ)‖)⁻¹ ≤ 3 / 2 := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
    linarith
  have hlog : ‖log (1 + z / (lambda : ℂ))‖ ≤ 1 / 2 := by
    have h := norm_log_sub_logTaylor_le 0 (z := z / (lambda : ℂ)) (by linarith)
    norm_num [logTaylor] at h
    have hm := mul_le_mul hu hi (inv_nonneg.mpr (by linarith)) (by norm_num : (0 : ℝ) ≤ 1 / 3)
    simp only [norm_div, norm_real, Real.norm_eq_abs] at hm
    nlinarith
  have ht := norm_log_sub_logTaylor_le 2 (z := z / (lambda : ℂ)) (by linarith)
  have hp : logTaylor 3 (z / (lambda : ℂ)) = z / lambda - (z / lambda) ^ 2 / 2 := by
    norm_num [logTaylor, Finset.sum_range_succ]
    ring
  rw [hp] at ht
  have hr : ‖log (1 + z / lambda) - z / lambda + (z / lambda) ^ 2 / 2‖ ≤
      1 / 2 * ‖z / (lambda : ℂ)‖ ^ 3 := by
    rw [show log (1 + z / lambda) - z / lambda + (z / lambda) ^ 2 / 2 =
      log (1 + z / lambda) - (z / lambda - (z / lambda) ^ 2 / 2) by ring]
    apply ht.trans
    norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
    nlinarith [mul_le_mul_of_nonneg_left hi
      (pow_nonneg (norm_nonneg (z / (lambda : ℂ))) 3)]
  have hm : (((1 / 2 - 1 : ℝ) : ℂ) * log (1 + z / lambda)).re ≤ 1 / 4 := by
    apply (re_le_norm _).trans
    rw [norm_mul, norm_real, Real.norm_eq_abs]
    norm_num
    linarith
  have hn := re_le_norm (I * (lambda : ℂ) ^ 2 *
    (log (1 + z / lambda) - z / lambda + (z / lambda) ^ 2 / 2))
  rw [norm_mul, norm_mul, norm_I, one_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hl] at hn
  have htail := hn.trans (mul_le_mul_of_nonneg_left hr (sq_nonneg lambda))
  rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hl] at htail
  rw [rsSaddleWeight, norm_exp, Real.exp_le_exp, rsSaddle_exponent_rewrite (1 / 2) hl.ne', add_re]
  linarith

theorem mediumCircle_coefficient {eta : ℝ} (he : 11 ≤ eta) (n : ℕ) :
    ‖rsSaddleCoefficient (1 / 2) (rsSaddleScale * eta) n * (rsSaddleScale : ℂ) ^ n‖ ≤
      750 / twelfthRadius eta ^ n := by
  have he0 : 0 < eta := by linarith
  have hs := rsSaddleScale_pos
  have hR := twelfthRadius_pos he0
  have hl := mul_pos hs he0
  have hu := (mediumRadius_data he).1
  have hd := rsSaddle_differentiable_closedBall (1 / 2) hl
    (show rsSaddleScale * twelfthRadius eta < rsSaddleScale * eta by nlinarith)
  have hc := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (mul_pos hs hR)
    (hd.mono Metric.closure_ball_subset_closedBall).diffContOnCl
    (C := (750 : ℝ)) (fun z hz => by
      have hzR : ‖z‖ = rsSaddleScale * twelfthRadius eta := by simpa using hz
      have hw := mediumCircle_weight hl (z := z) (by rw [hzR]; nlinarith)
      rw [hzR] at hw
      have hpow : (rsSaddleScale * eta) ^ 2 *
          ((rsSaddleScale * twelfthRadius eta) / (rsSaddleScale * eta)) ^ 3 = 4 * Real.pi := by
        rw [mul_div_mul_left _ _ hs.ne', div_pow, mul_pow, twelfthRadius_cube he0, rsSaddleScale_sq]
        field_simp
        norm_num
      rw [show 1 / 4 + 1 / 2 * (rsSaddleScale * eta) ^ 2 *
          ((rsSaddleScale * twelfthRadius eta) / (rsSaddleScale * eta)) ^ 3 =
            1 / 4 + 1 / 2 * ((rsSaddleScale * eta) ^ 2 *
              ((rsSaddleScale * twelfthRadius eta) / (rsSaddleScale * eta)) ^ 3) by ring, hpow] at hw
      exact hw.trans ((Real.exp_le_exp.mpr (by linarith [Real.pi_lt_d2])).trans exp_thirty_three_fifths_le))
  rw [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hs, rsSaddleCoefficient,
    norm_div, norm_natCast]
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have hRne := hR.ne'
  have hsne := hs.ne'
  have hco : ‖iteratedDeriv n (rsSaddleWeight (1 / 2) (rsSaddleScale * eta)) 0‖ /
      (n.factorial : ℝ) ≤ 750 / (rsSaddleScale * twelfthRadius eta) ^ n := by
    rw [div_le_iff₀ hf]
    exact hc.trans_eq (by ring)
  apply (mul_le_mul_of_nonneg_right hco (pow_nonneg hs.le n)).trans_eq
  rw [mul_pow]
  field_simp

theorem mediumCircle_remainder {eta : ℝ} (he : 11 ≤ eta) {z : ℂ}
    (hz : 4 / 3 * ‖z‖ ≤ twelfthRadius eta) (N : ℕ) :
    ‖rsSaddleRemainder (1 / 2) (rsSaddleScale * eta) N ((rsSaddleScale : ℂ) * z)‖ ≤
      3000 * (‖z‖ / twelfthRadius eta) ^ N := by
  have he0 : 0 < eta := by linarith
  have hR := twelfthRadius_pos he0
  have hs := rsSaddleScale_pos
  have hu := (mediumRadius_data he).1
  have hnorm : ‖(rsSaddleScale : ℂ) * z‖ = rsSaddleScale * ‖z‖ := by
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hs]
  have hsum := rsSaddle_hasSum (1 / 2) (mul_pos hs he0) (mul_pos hs hR)
    (show rsSaddleScale * twelfthRadius eta < rsSaddleScale * eta by nlinarith)
    (z := (rsSaddleScale : ℂ) * z) (by rw [hnorm]; nlinarith)
  have ht := (hasSum_nat_add_iff' N).mpr hsum
  have hr0 : 0 ≤ ‖z‖ / twelfthRadius eta := div_nonneg (norm_nonneg _) hR.le
  have hr : ‖z‖ / twelfthRadius eta ≤ 3 / 4 := by
    rw [div_le_iff₀ hR]
    linarith
  have hg := (hasSum_geometric_of_lt_one hr0 (by linarith)).mul_left
    (750 * (‖z‖ / twelfthRadius eta) ^ N)
  rw [← div_eq_mul_inv] at hg
  have hb : ‖rsSaddleRemainder (1 / 2) (rsSaddleScale * eta) N ((rsSaddleScale : ℂ) * z)‖ ≤
      750 * (‖z‖ / twelfthRadius eta) ^ N / (1 - ‖z‖ / twelfthRadius eta) := by
    apply ht.norm_le_of_bounded hg
    intro n
    rw [mul_pow, ← mul_assoc, norm_mul, norm_pow]
    apply (mul_le_mul_of_nonneg_right (mediumCircle_coefficient he (n + N)) (by positivity)).trans_eq
    rw [div_pow, pow_add]
    ring
  apply hb.trans
  rw [div_le_iff₀ (by linarith)]
  nlinarith [pow_nonneg hr0 N]

theorem jn_medium_central {eta : ℝ} {m : ℕ} (he : 11 ≤ eta)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) :
    ‖∫ y : ℝ in (-twelfthCutoff eta)..(twelfthCutoff eta),
      rsJnIntegrand (1 / 2) eta m 12 y‖ ≤ (75 / 2) / eta ^ 4 := by
  have he0 : 0 < eta := by linarith
  have hR := twelfthRadius_pos he0
  have hd0 : 0 < twelfthCutoff eta := by linarith [(mediumRadius_data he).2.1]
  have hb (y : ℝ) (hy : y ∈ Icc (-twelfthCutoff eta) (twelfthCutoff eta)) :
      ‖rsJnIntegrand (1 / 2) eta m 12 y‖ ≤
        ((375 / 2) / eta ^ 4) * exactGaussianWeight Real.pi 11 y := by
    by_cases hy0 : y = 0
    · subst y
      rw [jn_zero (1 / 2) eta m 11, norm_zero]
      unfold exactGaussianWeight
      positivity
    have hyd : |y| ≤ twelfthCutoff eta := abs_le.mpr hy
    have h := mediumCircle_remainder he (z := rsDescentPoint eta y - eta)
      (by rw [rsDescentPoint_distance]; unfold twelfthCutoff at hyd; linarith) 12
    rw [rsDescentPoint_distance] at h
    have hc : 3000 * (|y| / twelfthRadius eta) ^ 12 = ((375 / 2) / eta ^ 4) * |y| ^ 12 := by
      rw [div_pow, twelfthRadius_twelfth he0]
      ring
    rw [hc] at h
    rw [rsJnIntegrand, norm_mul, norm_mul, rsDescentDirection_norm, one_mul]
    apply (mul_le_mul_of_nonneg_left h (norm_nonneg _)).trans
    have hh := mul_le_mul_of_nonneg_left (gaussian_times_distance eta m hy0 hm0 hm1)
      (by positivity : 0 ≤ ((375 / 2) / eta ^ 4) * |y| ^ 11)
    convert hh using 1
    · ring
    · unfold exactGaussianWeight
      ring
  have h := norm_interval_exactGaussian 11 Real.pi_pos (by linarith)
    (by positivity : 0 ≤ (375 / 2) / eta ^ 4) hb
  apply h.trans
  exact (mul_le_mul_of_nonneg_left exactGaussianBudget_eleven (by positivity)).trans_eq (by ring)

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
