import LiuWang.Proof.GlobalZeroDensity.Sharp.Consumer

/-! The moving right boundary is paid by the actual Mobius tail. -/

set_option autoImplicit false

noncomputable section

open Complex
open LiuWang.Proof.GlobalZeroDensity.Sharp

namespace LiuWang.Proof.GlobalZeroDensity.Strip

def delta (y : ℝ) : ℝ := 2 / (3 * Real.log y)

theorem delta_bounds {y : ℝ} (hy : 10000 ≤ y) :
    0 < delta y ∧ delta y ≤ 2 / 27 := by
  have hl := log_ge_nine hy
  constructor
  · unfold delta; positivity
  · unfold delta
    apply (div_le_iff₀ (by positivity : 0 < 3 * Real.log y)).mpr
    linarith

theorem log_ceil_sub_one {y : ℝ} (hy : 10000 ≤ y) :
    (99 / 100) * Real.log y ≤ Real.log ((⌈y⌉₊ : ℝ) - 1) := by
  have hl := log_ge_nine hy
  have hc := Nat.le_ceil y
  have hx : 0 < (⌈y⌉₊ : ℝ) - 1 := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos (show 0 < y by linarith) hx)
  rw [Real.log_div (by linarith) hx.ne'] at hlog
  have hratio : y / ((⌈y⌉₊ : ℝ) - 1) ≤ 1001 / 1000 := by
    apply (div_le_iff₀ hx).mpr
    linarith
  linarith

theorem moving_tail_power {y : ℝ} (hy : 10000 ≤ y) :
    ((⌈y⌉₊ : ℝ) - 1) ^ (-delta y) ≤ 8 / 15 := by
  have hl := log_ge_nine hy
  have hc := Nat.le_ceil y
  have hx : 0 < (⌈y⌉₊ : ℝ) - 1 := by linarith
  have hlog := log_ceil_sub_one hy
  have hprod : 33 / 50 ≤ Real.log ((⌈y⌉₊ : ℝ) - 1) * delta y := by
    unfold delta
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (by positivity : 0 < 3 * Real.log y)).mpr
    linarith
  rw [Real.rpow_def_of_pos hx, mul_neg, Real.exp_neg, ← one_div]
  have he := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 33 / 50)
  have hmono := Real.exp_le_exp.mpr hprod
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  norm_num at he
  linarith

theorem norm_f_moving {y : ℝ} (hy : 10000 ≤ y) {s : ℂ}
    (hs : 1 + delta y ≤ s.re) :
    ‖f y s‖ ≤ (13 / 10) * (Real.log y) ^ 2 := by
  have hd := delta_bounds hy
  have hl := log_ge_nine hy
  have hs' : 1 < s.re := by linarith
  have h := norm_f_le_right hs' (by linarith : 1 < y)
  have hc := Nat.le_ceil y
  have hx : 1 ≤ (⌈y⌉₊ : ℝ) - 1 := by linarith
  have hpow : ((⌈y⌉₊ : ℝ) - 1) ^ (1 - s.re) ≤ 8 / 15 :=
    (Real.rpow_le_rpow_of_exponent_le hx (by linarith : 1 - s.re ≤ -delta y)).trans
      (moving_tail_power hy)
  have hinv : 1 / (s.re - 1) ≤ (3 / 2) * Real.log y := by
    have hh := one_div_le_one_div_of_le hd.1 (show delta y ≤ s.re - 1 by linarith)
    have he : 1 / delta y = (3 / 2) * Real.log y := by unfold delta; field_simp
    rwa [he] at hh
  have htail : ((⌈y⌉₊ : ℝ) - 1) ^ (1 - s.re) / (s.re - 1) ≤
      (8 / 15) * ((3 / 2) * Real.log y) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul hpow hinv (by positivity) (by norm_num)
  have hp := mul_le_mul (show 1 + 1 / (s.re - 1) ≤ 1 + (3 / 2) * Real.log y by linarith)
    htail (by positivity) (by positivity)
  nlinarith

theorem F_right_half {y : ℝ} (hy : 10000 ≤ y) {s : ℂ}
    (hs : 1 + delta y ≤ s.re) :
    F y s ≤ (169 / 100) * (Real.log y) ^ 4 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_f_moving hy hs) 2
  change ‖f y s‖ ^ 2 ≤ _
  nlinarith

theorem norm_sub_one_le {s : ℂ} (hs : 1 / 2 ≤ s.re) : ‖s - 1‖ ≤ ‖s‖ := by
  have hsq : ‖s - 1‖ ^ 2 ≤ ‖s‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
      Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
    nlinarith
  nlinarith [norm_nonneg s, norm_nonneg (s - 1)]

theorem cosine_re_small {y : ℝ} (hy : 10000 ≤ y) {s : ℂ}
    (hs0 : 0 ≤ s.re) (hs4 : s.re ≤ 4) :
    |(s / (2 * (y : ℂ))).re| ≤ 1 / 100 := by
  rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.div_ofReal_re,
    abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ (by positivity : 0 < 2 * y)).mpr
  linarith

theorem norm_cos_ge_constant (z : ℂ) (hz : |z.re| ≤ 1 / 100) :
    99 / 100 ≤ ‖Complex.cos z‖ := by
  have hsq := pow_le_pow_left₀ (abs_nonneg z.re) hz 2
  rw [sq_abs] at hsq
  have hcos := Real.one_sub_sq_div_two_le_cos (x := z.re)
  have hch : 1 ≤ Real.cosh z.im := by
    rw [Real.cosh_eq]
    have h1 := Real.add_one_le_exp z.im
    have h2 := Real.add_one_le_exp (-z.im)
    linarith
  have hre : (Complex.cos z).re = Real.cos z.re * Real.cosh z.im := by
    rw [Complex.cos_eq]
    simp [Complex.cos_ofReal_re]
  have h := Complex.re_le_norm (Complex.cos z)
  rw [hre] at h
  nlinarith [mul_nonneg (show 0 ≤ Real.cos z.re by linarith)
    (show 0 ≤ Real.cosh z.im - 1 by linarith)]

theorem norm_regularG_le_f {y : ℝ} (hy : 10000 ≤ y) {s : ℂ}
    (hs : s ≠ 1) (hs0 : 1 / 2 ≤ s.re) (hs4 : s.re ≤ 4) :
    ‖regularG y s‖ ≤ (100 / 99) * ‖f y s‖ := by
  have hc := norm_cos_ge_constant (s / (2 * (y : ℂ)))
    (cosine_re_small hy (by linarith) hs4)
  have hsp : 0 < ‖s‖ := by
    have hh := Complex.re_le_norm s
    linarith
  have hcp : 0 < ‖Complex.cos (s / (2 * (y : ℂ)))‖ := by linarith
  have hr : ‖s - 1‖ / (‖s‖ * ‖Complex.cos (s / (2 * (y : ℂ)))‖) ≤ 100 / 99 := by
    apply (div_le_iff₀ (mul_pos hsp hcp)).mpr
    have hp := mul_le_mul_of_nonneg_left hc hsp.le
    have hh := norm_sub_one_le hs0
    nlinarith
  rw [regularG_eq_g hs, g, norm_mul, norm_div, norm_mul]
  exact mul_le_mul_of_nonneg_right hr (norm_nonneg _)

theorem regularG_moving_sq {y : ℝ} (hy : 10000 ≤ y) {s : ℂ}
    (hs : s.re = 1 + delta y) :
    ‖regularG y s‖ ^ 2 ≤ (7 / 4) * (Real.log y) ^ 4 := by
  have hd := delta_bounds hy
  have hs1 : s ≠ 1 := by intro h; have := congrArg Complex.re h; simp [hs] at this; linarith
  have hf := norm_f_moving hy hs.ge
  have hg := norm_regularG_le_f hy hs1 (by linarith) (by linarith)
  have h : ‖regularG y s‖ ≤ (130 / 99) * Real.log y ^ 2 := by linarith
  have hp := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (Real.log y ^ 2)]

theorem F_right_lemma_3_3 {y : ℝ} (hy : 10000 * Real.log 6 ≤ y) {s : ℂ}
    (hs : 1 + delta y ≤ s.re) :
    F y s ≤ (174 / 100) * Real.log y ^ 4 := by
  have h := F_right_half (by linarith [log_six_ge_one] : 10000 ≤ y) hs
  nlinarith [sq_nonneg (Real.log y ^ 2)]

end LiuWang.Proof.GlobalZeroDensity.Strip
