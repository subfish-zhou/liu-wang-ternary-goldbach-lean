import LiuWang.Proof.GlobalZeroDensity.Strip.Window

/-! Retain enough of the hyperbolic cosine weight to improve the full-line mean constant. -/

set_option autoImplicit false

noncomputable section

open Complex
open LiuWang.Proof.GlobalZeroDensity.Sharp

namespace LiuWang.Proof.GlobalZeroDensity.Strip

theorem cosh_sq_ge_exp (x : ℝ) : Real.exp (3 * x / 2) / 2 ≤ Real.cosh x ^ 2 := by
  let a := Real.exp (x / 2)
  have ha : 0 < a := Real.exp_pos _
  have hpoly : 2 * a ^ 7 ≤ (a ^ 4 + 1) ^ 2 := by
    have hsos : a ^ 4 - 2 * a ^ 3 + 27 / 16 =
        (a - 3 / 2) ^ 2 * (a ^ 2 + a + 3 / 4) := by ring
    have h0 := mul_nonneg (sq_nonneg (a - 3 / 2))
      (show 0 ≤ a ^ 2 + a + 3 / 4 by positivity)
    have hh : 0 ≤ a ^ 4 - 2 * a ^ 3 + 2 := by nlinarith
    have hh' := mul_nonneg (show 0 ≤ a ^ 4 by positivity) hh
    nlinarith
  have ha2 : a ^ 2 = Real.exp x := by
    dsimp [a]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have ha3 : a ^ 3 = Real.exp (3 * x / 2) := by
    dsimp [a]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hcos : 2 * Real.cosh x * a ^ 2 = a ^ 4 + 1 := by
    rw [show a ^ 4 = (a ^ 2) ^ 2 by ring, ha2, Real.cosh_eq, Real.exp_neg]
    field_simp
  have hcos2 := congrArg (fun z : ℝ => z ^ 2) hcos
  have hmain : a ^ 4 * (Real.exp (3 * x / 2) / 2) ≤ a ^ 4 * Real.cosh x ^ 2 := by
    rw [← ha3]
    nlinarith
  exact (mul_le_mul_iff_right₀ (show 0 < a ^ 4 by positivity)).mp hmain

theorem norm_cos_ge_cosh (z : ℂ) (hz : |z.re| ≤ 1 / 100) :
    (99 / 100) * Real.cosh z.im ≤ ‖Complex.cos z‖ := by
  have hs := pow_le_pow_left₀ (abs_nonneg z.re) hz 2
  rw [sq_abs] at hs
  have h := Real.one_sub_sq_div_two_le_cos (x := z.re)
  have hc : 99 / 100 ≤ Real.cos z.re := by linarith
  have hp := mul_le_mul_of_nonneg_right hc (Real.cosh_pos z.im).le
  have hre : (Complex.cos z).re = Real.cos z.re * Real.cosh z.im := by
    rw [Complex.cos_eq]
    simp [Complex.cos_ofReal_re]
  have hn := Complex.re_le_norm (Complex.cos z)
  rw [hre] at hn
  linarith

theorem regularG_weight {y : ℝ} (hy : 10000 ≤ y) {s : ℂ}
    (hs1 : s ≠ 1) (hs0 : 1 / 2 ≤ s.re) (hs4 : s.re ≤ 4) :
    ‖regularG y s‖ ^ 2 ≤
      (21 / 10) * F y s * Real.exp (- |s.im| / ((4 / 3) * y)) := by
  let z := s / (2 * (y : ℂ))
  have hsn : 0 < ‖s‖ := by have h := Complex.re_le_norm s; linarith
  have hz : |z.re| ≤ 1 / 100 := cosine_re_small hy (by linarith) hs4
  have hi : z.im = s.im / (2 * y) := by
    dsimp [z]
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.div_ofReal_im]
  have hc := pow_le_pow_left₀ (by positivity : 0 ≤ (99 / 100) * Real.cosh z.im)
    (norm_cos_ge_cosh z hz) 2
  have he := cosh_sq_ge_exp |z.im|
  rw [Real.cosh_abs] at he
  have hi' : |z.im| = |s.im| / (2 * y) := by
    rw [hi, abs_div, abs_of_nonneg (by positivity : 0 ≤ 2 * y)]
  rw [hi'] at he
  have hce : (9801 / 20000) * Real.exp (|s.im| / ((4 / 3) * y)) ≤ ‖Complex.cos z‖ ^ 2 := by
    have hex : 3 * (|s.im| / (2 * y)) / 2 = |s.im| / ((4 / 3) * y) := by field_simp; ring
    rw [hex] at he
    nlinarith
  have hinv : 1 / ‖Complex.cos z‖ ^ 2 ≤ (21 / 10) * Real.exp (-|s.im| / ((4 / 3) * y)) := by
    have h := one_div_le_one_div_of_le (by positivity) hce
    have heq : 1 / ((9801 / 20000) * Real.exp (|s.im| / ((4 / 3) * y))) =
        (20000 / 9801) * Real.exp (-|s.im| / ((4 / 3) * y)) := by
      rw [neg_div, Real.exp_neg]
      field_simp
    rw [heq] at h
    nlinarith [Real.exp_pos (-|s.im| / ((4 / 3) * y))]
  have hratio : ‖s - 1‖ ^ 2 / ‖s‖ ^ 2 ≤ 1 := by
    apply (div_le_one (pow_pos hsn 2)).mpr
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_sub_one_le hs0) 2
  have heq : ‖regularG y s‖ ^ 2 =
      (‖s - 1‖ ^ 2 / ‖s‖ ^ 2) * (F y s / ‖Complex.cos z‖ ^ 2) := by
    rw [regularG_eq_g hs1, g, norm_mul, norm_div, norm_mul, mul_pow, div_pow, mul_pow]
    dsimp [F, z]
    ring
  rw [heq]
  have hp := mul_le_mul_of_nonneg_left hinv (show 0 ≤ F y s from sq_nonneg _)
  have hr := mul_le_mul_of_nonneg_right hratio
    (show 0 ≤ F y s / ‖Complex.cos z‖ ^ 2 by unfold F; positivity)
  simp only [div_eq_mul_inv] at hr hp ⊢
  nlinarith

theorem regularG_critical_weight {y : ℝ} (hy : 10000 ≤ y) (t : ℝ) :
    ‖regularG y ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 ≤
      (21 / 10) * F y ((1 / 2 : ℂ) + t * Complex.I) *
        Real.exp (- |t| / ((4 / 3) * y)) := by
  have hs1 : (1 / 2 : ℂ) + t * Complex.I ≠ 1 := by
    intro h; have := congrArg Complex.re h; norm_num at this
  simpa using regularG_weight hy hs1 (by norm_num) (by norm_num)

end LiuWang.Proof.GlobalZeroDensity.Strip
