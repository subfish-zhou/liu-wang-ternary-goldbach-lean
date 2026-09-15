import LiuWang.Proof.Campaign20260915.ZetaValidation.SaddleKernelFactor

set_option autoImplicit false
noncomputable section
open Complex

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def rsSaddleRemainder (sigma lambda : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  rsSaddleWeight sigma lambda z -
    ∑ n ∈ Finset.range N, rsSaddleCoefficient sigma lambda n * z ^ n

def rsJnIntegrand (sigma eta : ℝ) (m N : ℕ) (y : ℝ) : ℂ :=
  rsDescentDirection * rsGaussianKernel eta m (rsDescentPoint eta y) *
    rsSaddleRemainder sigma (rsSaddleScale * eta) N
      (rsSaddleScale * (rsDescentPoint eta y - eta))

theorem rsSaddleRemainder_gaussian_bound (sigma : ℝ) {lambda : ℝ}
    (hl : 0 < lambda) {z : ℂ} (hz0 : 0 < ‖z‖) (hz : ‖z‖ ≤ lambda / 2) (N : ℕ) :
    ‖rsSaddleRemainder sigma lambda N z‖ ≤
      21 * Real.exp (|sigma - 1| * Real.log (5 / 2) + 14 / 29 * ‖z‖ ^ 2) *
        (20 / 21 : ℝ) ^ N := by
  have hR : 21 / 20 * ‖z‖ ≤ 3 / 5 * lambda := by linarith
  have h := rsSaddle_source_remainder_twenty_one sigma hl
    (by positivity : 0 < 21 / 20 * ‖z‖) hR le_rfl N
  have hq : ‖z‖ / (21 / 20 * ‖z‖) = 20 / 21 := by field_simp
  rw [hq, rsSourceMajorant] at h
  have he : 5 / 6 * lambda ^ 2 * ((21 / 20 * ‖z‖) / lambda) ^ 3 ≤
      14 / 29 * ‖z‖ ^ 2 := by
    have hid : 5 / 6 * lambda ^ 2 * ((21 / 20 * ‖z‖) / lambda) ^ 3 =
        (5 / 6 * (21 / 20 * ‖z‖) ^ 3) / lambda := by field_simp
    rw [hid, div_le_iff₀ hl]
    nlinarith [mul_le_mul_of_nonneg_right hz (sq_nonneg ‖z‖)]
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num))
    (by positivity))

theorem rsDescent_exponential_re (eta y : ℝ) :
    (2 * Real.pi * I * rsDescentPoint eta y).re = Real.sqrt 2 * Real.pi * y := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  simp only [rsDescentPoint, rsDescentDirection, mul_re, mul_im, add_re, add_im,
    sub_re, sub_im, one_re, one_im, I_re, I_im, ofReal_re, ofReal_im, div_ofReal_re,
    div_ofReal_im, re_ofNat, im_ofNat]
  norm_num only
  field_simp
  rw [h2]
  ring

theorem rsDescent_gaussian_re (eta y : ℝ) (m : ℕ) :
    (-Real.pi * I * (rsDescentPoint eta y - eta) ^ 2 +
      2 * Real.pi * I * (eta - (m : ℝ)) * (rsDescentPoint eta y - eta)).re =
      -Real.pi * y ^ 2 + Real.sqrt 2 * Real.pi * (eta - m) * y := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  simp only [rsDescentPoint, add_sub_cancel_left, rsDescentDirection, pow_two, mul_re,
    mul_im, add_re, sub_re, sub_im, one_re, one_im, I_re, I_im, ofReal_re,
    ofReal_im, div_ofReal_re, div_ofReal_im, neg_re, neg_im, re_ofNat, im_ofNat]
  norm_num only
  field_simp
  ring_nf
  have h3 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by rw [pow_succ, h2]
  simp only [h2, h3]
  ring

theorem rsDescent_denominator_lower (eta : ℝ) {d y : ℝ} (hy : d ≤ |y|) :
    1 - Real.exp (-Real.sqrt 2 * Real.pi * d) ≤
      ‖rsHankelDenominator (rsDescentPoint eta y)‖ := by
  have hp : 0 < Real.sqrt 2 * Real.pi := mul_pos (Real.sqrt_pos.mpr (by norm_num)) Real.pi_pos
  have h1 := norm_sub_norm_le (1 : ℂ) (exp (2 * Real.pi * I * rsDescentPoint eta y))
  have h2 := norm_sub_norm_le (exp (2 * Real.pi * I * rsDescentPoint eta y)) (1 : ℂ)
  rw [norm_one, norm_exp, rsDescent_exponential_re, norm_sub_rev] at h1
  rw [norm_one, norm_exp, rsDescent_exponential_re] at h2
  change 1 - Real.exp (Real.sqrt 2 * Real.pi * y) ≤
    ‖rsHankelDenominator (rsDescentPoint eta y)‖ at h1
  change Real.exp (Real.sqrt 2 * Real.pi * y) - 1 ≤
    ‖rsHankelDenominator (rsDescentPoint eta y)‖ at h2
  rcases le_total 0 y with hy0 | hy0
  · rw [abs_of_nonneg hy0] at hy
    have hm := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hy hp.le)
    have hx := Real.add_one_le_exp (Real.sqrt 2 * Real.pi * d)
    have hx' := Real.add_one_le_exp (-Real.sqrt 2 * Real.pi * d)
    linarith
  · rw [abs_of_nonpos hy0] at hy
    have hm : Real.exp (Real.sqrt 2 * Real.pi * y) ≤
        Real.exp (-Real.sqrt 2 * Real.pi * d) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    linarith

theorem rsJnIntegrand_bound (sigma : ℝ) {eta d y : ℝ} {m : ℕ}
    (he : 0 < eta) (hd : 0 < d) (hy : d ≤ |y|) (hye : |y| ≤ eta / 2)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) (N : ℕ) :
    ‖rsJnIntegrand sigma eta m N y‖ ≤
      (21 * Real.exp (|sigma - 1| * Real.log (5 / 2)) * (20 / 21 : ℝ) ^ N /
        (1 - Real.exp (-Real.sqrt 2 * Real.pi * d))) *
        Real.exp (-Real.pi / 29 * y ^ 2 + Real.sqrt 2 * Real.pi * |y|) := by
  have hd0 : 0 < 1 - Real.exp (-Real.sqrt 2 * Real.pi * d) := by
    have hp : 0 < Real.sqrt 2 * Real.pi * d := by positivity
    have hh := Real.exp_lt_one_iff.mpr (show -Real.sqrt 2 * Real.pi * d < 0 by nlinarith)
    linarith
  have hz : ‖(rsSaddleScale : ℂ) * (rsDescentPoint eta y - eta)‖ = rsSaddleScale * |y| := by
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos rsSaddleScale_pos,
      rsDescentPoint_distance]
  have hr := rsSaddleRemainder_gaussian_bound sigma (mul_pos rsSaddleScale_pos he)
    (z := (rsSaddleScale : ℂ) * (rsDescentPoint eta y - eta))
    (by rw [hz]; exact mul_pos rsSaddleScale_pos (lt_of_lt_of_le hd hy))
    (by rw [hz]; nlinarith [rsSaddleScale_pos]) N
  rw [hz, mul_pow, rsSaddleScale_sq, sq_abs] at hr
  have hg : ‖rsGaussianKernel eta m (rsDescentPoint eta y)‖ ≤
      Real.exp (-Real.pi * y ^ 2 + Real.sqrt 2 * Real.pi * (eta - m) * y) /
        (1 - Real.exp (-Real.sqrt 2 * Real.pi * d)) := by
    rw [rsGaussianKernel, norm_div, norm_exp, rsDescent_gaussian_re]
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le hd0 (rsDescent_denominator_lower eta hy)
  have hlin : (eta - m) * y ≤ |y| := by
    calc
      _ ≤ |(eta - m) * y| := le_abs_self _
      _ = (eta - m) * |y| := by rw [abs_mul, abs_of_nonneg hm0]
      _ ≤ 1 * |y| := mul_le_mul_of_nonneg_right hm1 (abs_nonneg _)
      _ = _ := one_mul _
  rw [rsJnIntegrand, norm_mul, norm_mul, rsDescentDirection_norm, one_mul]
  apply (mul_le_mul hg hr (norm_nonneg _) (by positivity)).trans
  have hnorm :
      Real.exp (-Real.pi * y ^ 2 + Real.sqrt 2 * Real.pi * (eta - m) * y) /
          (1 - Real.exp (-Real.sqrt 2 * Real.pi * d)) *
          (21 * Real.exp (|sigma - 1| * Real.log (5 / 2) + 14 / 29 * (2 * Real.pi * y ^ 2)) *
            (20 / 21 : ℝ) ^ N) =
      (21 * Real.exp (|sigma - 1| * Real.log (5 / 2)) * (20 / 21 : ℝ) ^ N /
          (1 - Real.exp (-Real.sqrt 2 * Real.pi * d))) *
        Real.exp (-Real.pi / 29 * y ^ 2 + Real.sqrt 2 * Real.pi * (eta - m) * y) := by
    rw [Real.exp_add (|sigma - 1| * Real.log (5 / 2)) (14 / 29 * (2 * Real.pi * y ^ 2))]
    have hcombine :
        Real.exp (-Real.pi * y ^ 2 + Real.sqrt 2 * Real.pi * (eta - m) * y) *
          Real.exp (14 / 29 * (2 * Real.pi * y ^ 2)) =
          Real.exp (-Real.pi / 29 * y ^ 2 + Real.sqrt 2 * Real.pi * (eta - m) * y) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← hcombine]
    ring
  rw [hnorm]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hlin (show 0 ≤ Real.sqrt 2 * Real.pi by positivity)]

end LiuWang.Proof.Campaign20260915.ZetaValidation
