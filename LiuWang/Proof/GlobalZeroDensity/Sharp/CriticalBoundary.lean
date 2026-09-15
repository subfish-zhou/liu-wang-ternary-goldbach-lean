import LiuWang.Proof.GlobalZeroDensity.Sharp.SievedMean
import LiuWang.Proof.GlobalZeroDensity.WeightedMean

/-! A sharp actual critical boundary for the regularized strip function. -/

set_option autoImplicit false

noncomputable section

open Complex

namespace LiuWang.Proof.GlobalZeroDensity.Sharp

theorem norm_cos_ge_exp_sharp (z : ℂ) (hz : |z.re| ≤ 1 / 100) :
    (99 / 200) * Real.exp |z.im| ≤ ‖Complex.cos z‖ := by
  have hcos : 99 / 100 ≤ Real.cos z.re := by
    have hs := pow_le_pow_left₀ (abs_nonneg z.re) hz 2
    rw [sq_abs] at hs
    have h := Real.one_sub_sq_div_two_le_cos (x := z.re)
    linarith
  have hcosh : Real.exp |z.im| / 2 ≤ Real.cosh z.im := by
    rw [Real.cosh_eq]
    rcases le_total 0 z.im with hi | hi
    · rw [abs_of_nonneg hi]
      linarith [Real.exp_pos (-z.im)]
    · rw [abs_of_nonpos hi]
      linarith [Real.exp_pos z.im]
  have hre : (Complex.cos z).re = Real.cos z.re * Real.cosh z.im := by
    rw [Complex.cos_eq]
    simp [Complex.cos_ofReal_re]
  have h := mul_le_mul hcos hcosh (by positivity) (by linarith : 0 ≤ Real.cos z.re)
  have hnorm := Complex.re_le_norm (Complex.cos z)
  rw [hre] at hnorm
  linarith

theorem norm_regularG_critical_sharp {y : ℝ} (hy : 10000 ≤ y) (t : ℝ) :
    ‖regularG y ((1 / 2 : ℂ) + t * Complex.I)‖ ≤
      (200 / 99) * ‖f y ((1 / 2 : ℂ) + t * Complex.I)‖ *
        Real.exp (- |t| / (2 * y)) := by
  let s : ℂ := (1 / 2 : ℂ) + t * Complex.I
  have hy0 : 0 < y := by linarith
  have hs : s ≠ 1 := by
    intro h; have := congrArg Complex.re h; norm_num [s] at this
  have hs0 : s ≠ 0 := by
    intro h; have := congrArg Complex.re h; norm_num [s] at this
  have hnorm : ‖s - 1‖ = ‖s‖ := critical_norm_sub_one t
  have hre : |(s / (2 * (y : ℂ))).re| ≤ 1 / 100 := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.div_ofReal_re]
    simp only [s, Complex.add_re, Complex.div_ofNat_re, Complex.one_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_self, add_zero]
    rw [abs_of_nonneg (by positivity)]
    apply (div_le_iff₀ (by positivity : 0 < 2 * y)).mpr
    linarith
  have hi : |(s / (2 * (y : ℂ))).im| = |t| / (2 * y) := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.div_ofReal_im]
    simp [s, abs_div, abs_of_pos hy0, abs_mul]
  have hcos := norm_cos_ge_exp_sharp (s / (2 * (y : ℂ))) hre
  rw [hi] at hcos
  change ‖regularG y s‖ ≤ _
  rw [regularG_eq_g hs, g, norm_mul, norm_div, norm_mul, hnorm]
  have hspos := norm_pos_iff.mpr hs0
  rw [div_mul_eq_div_div, div_self hspos.ne', one_div]
  have hinv : ‖Complex.cos (s / (2 * (y : ℂ)))‖⁻¹ ≤
      (200 / 99) * Real.exp (- |t| / (2 * y)) := by
    have h := one_div_le_one_div_of_le
      (by positivity : 0 < (99 / 200) * Real.exp (|t| / (2 * y))) hcos
    rw [← one_div]
    calc
      _ ≤ 1 / ((99 / 200) * Real.exp (|t| / (2 * y))) := h
      _ = _ := by
        rw [neg_div, Real.exp_neg]
        field_simp
  nlinarith [mul_le_mul_of_nonneg_right hinv (norm_nonneg (f y s))]

theorem F_critical_twenty_one {y : ℝ} (hy : 10000 ≤ y) (t : ℝ) :
    F y ((1 / 2 : ℂ) + t * Complex.I) ≤ 21 * y * (2 + |t|) := by
  have h := F_le_mollifier_sq y t
  have hq := mul_le_mul_of_nonneg_left (norm_Q_sq_le hy t)
    (show 0 ≤ (202 / 25) * (2 + |t|) by positivity)
  nlinarith [mul_nonneg (show 0 ≤ y by linarith) (abs_nonneg t)]

theorem regularG_critical_linear_envelope {y : ℝ} (hy : 10000 ≤ y) (t : ℝ) :
    ‖regularG y ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 ≤
      (861 / 10) * y * (2 + |t|) * Real.exp (- |t| / y) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_regularG_critical_sharp hy t) 2
  have he : Real.exp (- |t| / (2 * y)) ^ 2 = Real.exp (- |t| / y) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [mul_pow, mul_pow, he] at h
  have hf := mul_le_mul_of_nonneg_right (F_critical_twenty_one hy t)
    (Real.exp_pos (- |t| / y)).le
  simp only [F] at hf
  have hpos := mul_nonneg (sq_nonneg ‖f y ((1 / 2 : ℂ) + t * Complex.I)‖)
    (Real.exp_pos (- |t| / y)).le
  nlinarith

theorem exp_negative_one_le : Real.exp (-1) ≤ 3 / 8 := by
  have h : (8 / 3 : ℝ) ≤ Real.exp 1 :=
    le_of_lt ((by norm_num : (8 / 3 : ℝ) < 2.7182818283).trans Real.exp_one_gt_d9)
  rw [Real.exp_neg, ← one_div]
  apply (div_le_iff₀ (Real.exp_pos 1)).mpr
  linarith

theorem regularG_critical_max {y : ℝ} (hy : 10000 ≤ y) (t : ℝ) :
    ‖regularG y ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 ≤ 33 * y ^ 2 := by
  have hy0 : 0 < y := by linarith
  have h := regularG_critical_linear_envelope hy t
  have he : Real.exp (- |t| / y) ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (abs_nonneg t)) hy0.le)
  have hp := (Real.mul_exp_neg_le_exp_neg_one (|t| / y)).trans exp_negative_one_le
  have hp' := mul_le_mul_of_nonneg_left hp hy0.le
  have hcancel : y * (|t| / y * Real.exp (-(|t| / y))) =
      |t| * Real.exp (- |t| / y) := by
    rw [neg_div]
    field_simp
  rw [hcancel] at hp'
  have hbound : (2 + |t|) * Real.exp (- |t| / y) ≤ 2 + (3 / 8) * y := by
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hbound (show 0 ≤ (861 / 10) * y by positivity)
  have hys : 10000 * y ≤ y ^ 2 := by nlinarith
  nlinarith

theorem critical_boundary_3_37 {y : ℝ} (hy : 10000 * Real.log 6 ≤ y) (t : ℝ) :
    ‖regularG y ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 ≤ (3303 / 100) * y ^ 2 := by
  have h := regularG_critical_max (by linarith [log_six_ge_one] : 10000 ≤ y) t
  nlinarith [sq_nonneg y]

end LiuWang.Proof.GlobalZeroDensity.Sharp
