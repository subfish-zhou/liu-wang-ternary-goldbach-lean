import LiuWang.Proof.ZeroRegionFamily.Sharp.DigammaShift
import LiuWang.Proof.LocalAnalyticBounds.DigammaRemainder

set_option autoImplicit false

noncomputable section

open Complex Finset
open LiuWang.Proof.LocalAnalyticBounds
open LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.Campaign20260915.GammaLow

theorem digamma_re_mono_real {a b y : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hy : y ^ 2 ≤ a ^ 2) :
    (digamma ((a : ℂ) + I * y)).re ≤ (digamma ((b : ℂ) + I * y)).re := by
  have hs := digamma_difference_hasSum ha (ha.trans_le hab) y
  have hterm (n : ℕ) :
      ((n : ℝ) + b) / (((n : ℝ) + b) ^ 2 + y ^ 2) -
        ((n : ℝ) + a) / (((n : ℝ) + a) ^ 2 + y ^ 2) ≤ 0 := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hna : 0 < (n : ℝ) + a := by linarith
    have hnb : 0 < (n : ℝ) + b := by linarith
    have hprod : y ^ 2 ≤ ((n : ℝ) + a) * ((n : ℝ) + b) := by
      nlinarith [mul_nonneg hn (show 0 ≤ a + b by linarith),
        mul_nonneg ha.le (sub_nonneg.mpr hab)]
    apply sub_nonpos.mpr
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hprod)]
  have hle :
      (∑' n : ℕ, (((n : ℝ) + b) / (((n : ℝ) + b) ^ 2 + y ^ 2) -
        ((n : ℝ) + a) / (((n : ℝ) + a) ^ 2 + y ^ 2))) ≤ 0 := tsum_nonpos hterm
  rw [hs.tsum_eq] at hle
  linarith

theorem digamma_re_mono_height_sq {a y v : ℝ} (ha : 0 < a)
    (hy : y ^ 2 ≤ v ^ 2) :
    (digamma ((a : ℂ) + I * y)).re ≤ (digamma ((a : ℂ) + I * v)).re := by
  have hp (u : ℝ) (n : ℕ) : (a : ℂ) + I * u ≠ -(n : ℂ) := by
    intro he
    have hr := congrArg Complex.re he
    simp [Complex.mul_re] at hr
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    linarith
  have hs (u : ℝ) := Complex.hasSum_re (Complex.hasSum_digamma (hp u))
  have hterm (n : ℕ) :
      (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + ((a : ℂ) + I * y))).re ≤
        (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + ((a : ℂ) + I * v))).re := by
    simp only [Complex.sub_re]
    apply sub_le_sub_left
    simp only [one_div, Complex.inv_re, Complex.normSq_apply, Complex.add_re,
      Complex.add_im, Complex.natCast_re, Complex.natCast_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, mul_zero, sub_zero, zero_add, add_zero]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hna : 0 < (n : ℝ) + a := by linarith
    apply div_le_div_of_nonneg_left hna.le
      (by nlinarith [sq_pos_of_pos hna, sq_nonneg y, sq_nonneg v])
    nlinarith
  have hle := (hs y).summable.tsum_le_tsum hterm (hs v).summable
  rw [(hs y).tsum_eq, (hs v).tsum_eq] at hle
  simp only [Complex.add_re, Complex.ofReal_re] at hle
  linarith

theorem digamma_upper_corner :
    (digamma ((63 / 40 : ℂ) + I * (1 / 2 : ℝ))).re ≤
      79 / 100 - Real.eulerMascheroniConstant := by
  have hnorm : ‖(63 / 40 : ℂ) + I * (1 / 2 : ℝ) - 1‖ ≤ (4 / 5 : ℝ) := by
    have hsq := Complex.sq_norm ((63 / 40 : ℂ) + I * (1 / 2 : ℝ) - 1)
    norm_num [Complex.normSq_apply] at hsq
    norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    nlinarith
  have hhead :
      (digammaApprox ((63 / 40 : ℂ) + I * (1 / 2 : ℝ)) 32).re ≤
        153 / 200 - Real.eulerMascheroniConstant := by
    norm_num [digammaApprox, sum_range_succ, Complex.inv_re, Complex.normSq_apply]
  have hh := (digamma_re_mem_approx_interval (a := 1) (by norm_num) le_rfl
    (z := (63 / 40 : ℂ) + I * (1 / 2 : ℝ)) (by norm_num)
    (N := 32) (by norm_num)).2
  norm_num only [Nat.cast_ofNat, one_mul] at hh
  linarith

theorem digamma_lower_corner :
    83 / 100 - Real.eulerMascheroniConstant ≤ (digamma (9 / 5 : ℂ)).re := by
  have hp (n : ℕ) : (9 / 5 : ℂ) ≠ -(n : ℂ) := by
    intro he
    have hr := congrArg Complex.re he
    norm_num at hr
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    linarith
  have hs := Complex.hasSum_re (Complex.hasSum_digamma hp)
  have hterm (n : ℕ) :
      0 ≤ (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + (9 / 5 : ℂ))).re := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hh := one_div_le_one_div_of_le
      (show 0 < (n : ℝ) + 1 by positivity)
      (show (n : ℝ) + 1 ≤ (n : ℝ) + 9 / 5 by linarith)
    simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_ofNat,
      ← Complex.ofReal_div, ← Complex.ofReal_add, ← Complex.ofReal_sub,
      Complex.ofReal_re] using sub_nonneg.mpr hh
  have hh := hs.summable.sum_le_tsum (range 32) (fun n _ => hterm n)
  rw [hs.tsum_eq] at hh
  norm_num [sum_range_succ] at hh
  linarith

theorem euler_lower : (27 / 50 : ℝ) ≤ Real.eulerMascheroniConstant := by
  have hh := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 15
  have hlog : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  norm_num [Real.eulerMascheroniSeq] at hh
  rw [hlog] at hh
  linarith [Real.log_two_lt_d9]

theorem digamma_upper_rectangle {a y : ℝ} (ha : 3 / 2 ≤ a)
    (ha1 : a ≤ 63 / 40) (hy : |y| ≤ 1 / 2) :
    (digamma ((a : ℂ) + I * y)).re ≤ 79 / 100 - Real.eulerMascheroniConstant := by
  have hy2 : y ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith [sq_abs y, abs_nonneg y]
  have hr := digamma_re_mono_real (by linarith : 0 < a) ha1
    (show y ^ 2 ≤ a ^ 2 by nlinarith)
  have ht := digamma_re_mono_height_sq (a := 63 / 40) (by norm_num) hy2
  have hc := digamma_upper_corner
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hr ht hc
  exact (hr.trans ht).trans hc

theorem digamma_lower_rectangle {b y : ℝ} (hb : 9 / 5 ≤ b) :
    83 / 100 - Real.eulerMascheroniConstant ≤ (digamma ((b : ℂ) + I * y)).re := by
  have hr := digamma_re_mono_real (a := 9 / 5) (y := 0) (by norm_num) hb (by norm_num)
  have ht := digamma_re_mono_height_sq (a := b) (y := 0) (v := y)
    (by linarith) (by simpa using sq_nonneg y)
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_zero,
    mul_zero, add_zero] at hr ht
  exact (digamma_lower_corner.trans hr).trans ht

#print axioms digamma_upper_rectangle
#print axioms digamma_lower_rectangle

end LiuWang.Proof.Campaign20260915.GammaLow
