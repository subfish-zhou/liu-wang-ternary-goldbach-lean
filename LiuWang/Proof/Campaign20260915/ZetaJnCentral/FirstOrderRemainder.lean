import LiuWang.Proof.Campaign20260915.ZetaJnCentral.FullLocalBudget

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem saddle_exponent_norm (sigma : ℝ) {lambda : ℝ} (hl : 0 < lambda)
    {z : ℂ} (hz : ‖z‖ ≤ lambda / 2) :
    ‖rsSaddleExponent sigma lambda z‖ ≤
      3 / 2 * |sigma - 1| * ‖z / (lambda : ℂ)‖ +
        2 / 3 * lambda ^ 2 * ‖z / (lambda : ℂ)‖ ^ 3 := by
  have hu : ‖z / (lambda : ℂ)‖ ≤ 1 / 2 := by
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hl, div_le_iff₀ hl]
    linarith
  have hlog := norm_log_one_add_half_le_self hu
  have htail := norm_log_sub_logTaylor_le 2 (z := z / (lambda : ℂ)) (by linarith)
  have hpoly : logTaylor 3 (z / (lambda : ℂ)) =
      z / lambda - (z / lambda) ^ 2 / 2 := by
    norm_num [logTaylor, Finset.sum_range_succ]
    ring
  rw [hpoly] at htail
  have ht : ‖log (1 + z / (lambda : ℂ)) - z / lambda + (z / lambda) ^ 2 / 2‖ ≤
      2 / 3 * ‖z / (lambda : ℂ)‖ ^ 3 := by
    rw [show log (1 + z / (lambda : ℂ)) - z / lambda + (z / lambda) ^ 2 / 2 =
      log (1 + z / lambda) - (z / lambda - (z / lambda) ^ 2 / 2) by ring]
    apply htail.trans
    norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
    have hi : (1 - ‖z / (lambda : ℂ)‖)⁻¹ ≤ 2 := by
      rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hi
      (pow_nonneg (norm_nonneg (z / (lambda : ℂ))) 3)]
  rw [rsSaddle_exponent_rewrite sigma hl.ne']
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul, norm_mul, norm_I, one_mul, norm_pow, norm_real,
    norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hl]
  nlinarith [mul_le_mul_of_nonneg_left hlog (abs_nonneg (sigma - 1)),
    mul_le_mul_of_nonneg_left ht (sq_nonneg lambda)]

def firstOrderPolynomial (sigma y : ℝ) : ℝ :=
  3 / 2 * |sigma - 1| + 4 * Real.pi / 3 * y ^ 2

theorem firstOrderPolynomial_nonneg (sigma y : ℝ) :
    0 ≤ firstOrderPolynomial sigma y := by
  unfold firstOrderPolynomial
  positivity

theorem descent_exponent_norm (sigma : ℝ) {eta y : ℝ}
    (he : 0 < eta) (hy : |y| ≤ eta / 2) :
    ‖rsSaddleExponent sigma (rsSaddleScale * eta)
      ((rsSaddleScale : ℂ) * (rsDescentPoint eta y - eta))‖ ≤
        |y| / eta * firstOrderPolynomial sigma y := by
  have hs := rsSaddleScale_pos
  have hz : ‖(rsSaddleScale : ℂ) * (rsDescentPoint eta y - eta)‖ =
      rsSaddleScale * |y| := by
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hs, rsDescentPoint_distance]
  have hq : ‖((rsSaddleScale : ℂ) * (rsDescentPoint eta y - eta)) /
      ((rsSaddleScale * eta : ℝ) : ℂ)‖ = |y| / eta := by
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos hs he), hz]
    field_simp
  have h := saddle_exponent_norm sigma (mul_pos hs he)
    (z := (rsSaddleScale : ℂ) * (rsDescentPoint eta y - eta))
    (by rw [hz]; nlinarith)
  rw [hq, mul_pow, rsSaddleScale_sq] at h
  apply h.trans_eq
  unfold firstOrderPolynomial
  rw [div_pow, pow_succ |y| 2, sq_abs]
  field_simp
  ring

theorem descent_exponent_envelope (sigma : ℝ) {eta y : ℝ}
    (he : 0 < eta) (hy : |y| ≤ eta / 2) :
    |y| / eta * firstOrderPolynomial sigma y ≤
      3 / 4 * |sigma - 1| + 2 * Real.pi / 3 * y ^ 2 := by
  have hq : |y| / eta ≤ 1 / 2 := (div_le_iff₀ he).mpr (by linarith)
  have h := mul_le_mul_of_nonneg_right hq (firstOrderPolynomial_nonneg sigma y)
  apply h.trans_eq
  unfold firstOrderPolynomial
  ring

theorem firstOrder_remainder (sigma : ℝ) {eta y : ℝ}
    (he : 0 < eta) (hy : |y| ≤ eta / 2) :
    ‖rsSaddleRemainder sigma (rsSaddleScale * eta) 1
      ((rsSaddleScale : ℂ) * (rsDescentPoint eta y - eta))‖ ≤
      (|y| / eta * firstOrderPolynomial sigma y) *
        Real.exp (3 / 4 * |sigma - 1| + 2 * Real.pi / 3 * y ^ 2) := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp
    (rsSaddleExponent sigma (rsSaddleScale * eta)
      ((rsSaddleScale : ℂ) * (rsDescentPoint eta y - eta))) 1
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one,
    div_one, pow_one] at h
  simpa only [rsSaddleRemainder, Finset.sum_range_one, rsSaddle_coefficient_zero,
    pow_zero, mul_one, rsSaddleWeight] using
    h.trans (mul_le_mul (descent_exponent_norm sigma he hy)
      (Real.exp_le_exp.mpr ((descent_exponent_norm sigma he hy).trans
        (descent_exponent_envelope sigma he hy))) (Real.exp_pos _).le
      (mul_nonneg (div_nonneg (abs_nonneg y) he.le) (firstOrderPolynomial_nonneg sigma y)))

theorem jn_one_pointwise (sigma : ℝ) {eta y : ℝ} {m : ℕ}
    (he : 0 < eta) (hy : |y| ≤ eta / 2)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) :
    ‖rsJnIntegrand sigma eta m 1 y‖ ≤
      (Real.exp (3 / 4 * |sigma - 1|) / eta) *
        (firstOrderPolynomial sigma y * (|y| + 1 / (Real.sqrt 2 * Real.pi)) *
          Real.exp (-Real.pi / 3 * y ^ 2)) := by
  by_cases hy0 : y = 0
  · subst y
    rw [jn_zero sigma eta m 0, norm_zero]
    exact mul_nonneg (by positivity) (mul_nonneg
      (mul_nonneg (firstOrderPolynomial_nonneg _ _) (by positivity)) (Real.exp_pos _).le)
  rw [rsJnIntegrand, norm_mul, norm_mul, rsDescentDirection_norm, one_mul]
  apply (mul_le_mul_of_nonneg_left (firstOrder_remainder sigma he hy) (norm_nonneg _)).trans
  calc
    _ = (firstOrderPolynomial sigma y / eta *
        Real.exp (3 / 4 * |sigma - 1| + 2 * Real.pi / 3 * y ^ 2)) *
        (‖rsGaussianKernel eta m (rsDescentPoint eta y)‖ * |y|) := by ring
    _ ≤ (firstOrderPolynomial sigma y / eta *
        Real.exp (3 / 4 * |sigma - 1| + 2 * Real.pi / 3 * y ^ 2)) *
        (Real.exp (-Real.pi * y ^ 2) * (|y| + 1 / (Real.sqrt 2 * Real.pi))) :=
      mul_le_mul_of_nonneg_left (gaussian_times_distance eta m hy0 hm0 hm1)
        (mul_nonneg (div_nonneg (firstOrderPolynomial_nonneg _ _) he.le) (Real.exp_pos _).le)
    _ = _ := by
      rw [Real.exp_add]
      have hx : Real.exp (2 * Real.pi / 3 * y ^ 2) * Real.exp (-Real.pi * y ^ 2) =
          Real.exp (-Real.pi / 3 * y ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [← hx]
      ring

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
