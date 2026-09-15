import LiuWang.Proof.Campaign20260915.ZetaMordell.SourceMainTerm
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Set
open scoped Real

namespace LiuWang.Proof.Campaign20260915.ZetaMordell
open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem exterior_denominator_pos {d : ℝ} (hd : 0 < d) :
    0 < 1 - Real.exp (-Real.sqrt 2 * Real.pi * d) := by
  apply sub_pos.mpr
  apply Real.exp_lt_one_iff.mpr
  have hp : 0 < Real.sqrt 2 * Real.pi * d := by positivity
  nlinarith

theorem exterior_denominator_half {d : ℝ} (hd : 1 / 2 ≤ d) :
    1 / 2 ≤ 1 - Real.exp (-Real.sqrt 2 * Real.pi * d) := by
  have hs : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hx : 1 ≤ Real.sqrt 2 * Real.pi * d := by
    have h1 := mul_le_mul_of_nonneg_right hs (by positivity : 0 ≤ Real.pi * d)
    nlinarith [Real.two_le_pi]
  have he : 2 ≤ Real.exp (Real.sqrt 2 * Real.pi * d) :=
    (by linarith : 2 ≤ Real.sqrt 2 * Real.pi * d + 1).trans (Real.add_one_le_exp _)
  have hi := (inv_le_comm₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 1 / 2)).mpr
    (by norm_num; exact he)
  rw [show -Real.sqrt 2 * Real.pi * d = -(Real.sqrt 2 * Real.pi * d) by ring, Real.exp_neg]
  linarith

theorem exterior_gaussian_bound (eta : ℝ) (m : ℕ) {d y : ℝ}
    (hd : 0 < d) (hy : d ≤ |y|) (h0 : 0 ≤ eta - m) (h1 : eta - m ≤ 1) :
    ‖rsGaussianKernel eta m (rsDescentPoint eta y)‖ ≤
      Real.exp (-Real.pi * y ^ 2) / (1 - Real.exp (-Real.sqrt 2 * Real.pi * d)) := by
  let c := Real.sqrt 2 * Real.pi
  have hc : 0 < c := by dsimp [c]; positivity
  have hD := exterior_denominator_pos hd
  have hn := hD.trans_le (rsDescent_denominator_lower eta hy)
  rw [rsGaussianKernel, norm_div, norm_exp, rsDescent_gaussian_re]
  apply (div_le_div_iff₀ hn hD).mpr
  rcases le_total 0 y with hp | hp
  · have hdy : d ≤ y := by simpa only [abs_of_nonneg hp] using hy
    have hh := norm_sub_norm_le (exp (2 * Real.pi * I * rsDescentPoint eta y)) (1 : ℂ)
    rw [norm_exp, rsDescent_exponential_re, norm_one] at hh
    change Real.exp (c * y) - 1 ≤ ‖rsHankelDenominator (rsDescentPoint eta y)‖ at hh
    have hmul : Real.exp (c * y) * (1 - Real.exp (-c * d)) ≤ Real.exp (c * y) - 1 := by
      have he : 1 ≤ Real.exp (c * y) * Real.exp (-c * d) := by
        rw [← Real.exp_add, Real.one_le_exp_iff]
        nlinarith
      nlinarith
    have hlin : c * (eta - m) * y ≤ c * y := by
      nlinarith [mul_le_mul_of_nonneg_right h1 (mul_nonneg hc.le hp)]
    calc
      _ = Real.exp (-Real.pi * y ^ 2) * Real.exp (c * (eta - m) * y) *
          (1 - Real.exp (-c * d)) := by
        rw [← Real.exp_add]
        dsimp [c]
        simp only [neg_mul]
      _ ≤ Real.exp (-Real.pi * y ^ 2) * Real.exp (c * y) *
          (1 - Real.exp (-c * d)) := by
        have hD' : 0 ≤ 1 - Real.exp (-c * d) := by simpa only [c, neg_mul] using hD.le
        apply mul_le_mul_of_nonneg_right _ hD'
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hlin) (Real.exp_pos _).le
      _ ≤ Real.exp (-Real.pi * y ^ 2) * ‖rsHankelDenominator (rsDescentPoint eta y)‖ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hmul.trans hh) (Real.exp_pos _).le
  · have hlin : Real.sqrt 2 * Real.pi * (eta - m) * y ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hc.le h0) hp
    have he : Real.exp (-Real.pi * y ^ 2 + Real.sqrt 2 * Real.pi * (eta - m) * y) ≤
        Real.exp (-Real.pi * y ^ 2) := Real.exp_le_exp.mpr (by linarith)
    exact (mul_le_mul_of_nonneg_right he hD.le).trans
      (mul_le_mul_of_nonneg_left (rsDescent_denominator_lower eta hy) (Real.exp_pos _).le)

theorem exterior_gaussian_bound_half (eta : ℝ) (m : ℕ) {y : ℝ}
    (hy : 1 / 2 ≤ |y|) (h0 : 0 ≤ eta - m) (h1 : eta - m ≤ 1) :
    ‖rsGaussianKernel eta m (rsDescentPoint eta y)‖ ≤ 2 * Real.exp (-Real.pi * y ^ 2) := by
  have h := exterior_gaussian_bound eta m (by norm_num : (0 : ℝ) < 1 / 2) hy h0 h1
  apply h.trans
  rw [div_le_iff₀ (exterior_denominator_pos (by norm_num : (0 : ℝ) < 1 / 2))]
  nlinarith [mul_le_mul_of_nonneg_left
    (exterior_denominator_half (le_refl (1 / 2 : ℝ))) (Real.exp_pos (-Real.pi * y ^ 2)).le]

theorem exterior_polynomial_measurable (sigma eta : ℝ) (m N : ℕ) :
    Measurable (rsLocalPolynomialIntegrand sigma eta m N) := by
  unfold rsLocalPolynomialIntegrand rsGaussianKernel rsHankelDenominator rsDescentPoint
  fun_prop

theorem exterior_polynomial_norm (sigma eta y : ℝ) (m N : ℕ) :
    ‖rsLocalPolynomialIntegrand sigma eta m N y‖ ≤
      ‖rsGaussianKernel eta m (rsDescentPoint eta y)‖ *
        ∑ n ∈ Finset.range N,
          ‖rsSaddleCoefficient sigma (rsSaddleScale * eta) n * (rsSaddleScale : ℂ) ^ n‖ * |y| ^ n := by
  unfold rsLocalPolynomialIntegrand
  rw [norm_mul, norm_mul, rsDescentDirection_norm, one_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n _
  rw [mul_pow, ← mul_assoc, norm_mul, norm_pow, rsDescentPoint_distance]

theorem exterior_power_gaussian (n : ℕ) (y : ℝ) :
    |y| ^ n * Real.exp (-Real.pi * y ^ 2) ≤
      (n.factorial : ℝ) * 3 * Real.exp (-Real.pi / 2 * y ^ 2) := by
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have hp := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp |y| (abs_nonneg y) n)
  have hx : |y| - Real.pi * y ^ 2 ≤ 1 - Real.pi / 2 * y ^ 2 := by
    nlinarith [sq_nonneg (|y| - 1), sq_abs y, Real.two_le_pi,
      mul_nonneg (show 0 ≤ Real.pi - 2 by linarith [Real.two_le_pi]) (sq_nonneg y)]
  calc
    _ ≤ (n.factorial : ℝ) * (Real.exp |y| * Real.exp (-Real.pi * y ^ 2)) := by
      nlinarith [mul_le_mul_of_nonneg_right hp (Real.exp_pos (-Real.pi * y ^ 2)).le]
    _ ≤ (n.factorial : ℝ) * Real.exp (1 + (-Real.pi / 2 * y ^ 2)) := by
      rw [← Real.exp_add]
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hf.le
      linarith
    _ ≤ _ := by
      rw [Real.exp_add]
      have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
      nlinarith [mul_le_mul_of_nonneg_right he
        (mul_nonneg hf.le (Real.exp_pos (-Real.pi / 2 * y ^ 2)).le)]

theorem exterior_polynomial_bound (sigma eta : ℝ) (m N : ℕ) {y : ℝ}
    (hy : 1 / 2 ≤ |y|) (h0 : 0 ≤ eta - m) (h1 : eta - m ≤ 1) :
    ‖rsLocalPolynomialIntegrand sigma eta m N y‖ ≤
      (6 * ∑ n ∈ Finset.range N,
        ‖rsSaddleCoefficient sigma (rsSaddleScale * eta) n * (rsSaddleScale : ℂ) ^ n‖ *
          (n.factorial : ℝ)) * Real.exp (-Real.pi / 2 * y ^ 2) := by
  apply (exterior_polynomial_norm sigma eta y m N).trans
  calc
    _ ≤ (2 * Real.exp (-Real.pi * y ^ 2)) *
        ∑ n ∈ Finset.range N,
          ‖rsSaddleCoefficient sigma (rsSaddleScale * eta) n * (rsSaddleScale : ℂ) ^ n‖ * |y| ^ n := by
      exact mul_le_mul_of_nonneg_right (exterior_gaussian_bound_half eta m hy h0 h1)
        (Finset.sum_nonneg (fun _ _ => by positivity))
    _ ≤ _ := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro n _
      have h := mul_le_mul_of_nonneg_left (exterior_power_gaussian n y)
        (by positivity : 0 ≤ 2 * ‖rsSaddleCoefficient sigma (rsSaddleScale * eta) n * (rsSaddleScale : ℂ) ^ n‖)
      nlinarith

end LiuWang.Proof.Campaign20260915.ZetaMordell
