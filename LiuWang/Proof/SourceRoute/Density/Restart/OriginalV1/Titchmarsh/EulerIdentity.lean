import PrimeNumberTheoremAnd.ZetaBounds

/-!
Titchmarsh (second edition), pp.49-50, (3.5.3). The existing Euler summation
and analytic continuation theorem has exactly the positive-integer cutoff
and the half-plane needed here. No critical-line estimate is imported.
-/

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set Finset

namespace LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.Titchmarsh

def remainder (N : ℕ) (s : ℂ) : ℂ :=
  ∫ x in Set.Ioi (N : ℝ), ((⌊x⌋ : ℂ) + 1 / 2 - x) / (x : ℂ) ^ (s + 1)

theorem remainder_integrable {N : ℕ} (hN : 0 < N) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ =>
      ((⌊x⌋ : ℂ) + 1 / 2 - x) / (x : ℂ) ^ (s + 1)) (Set.Ioi (N : ℝ)) := by
  simpa only [div_eq_mul_inv, Complex.cpow_neg] using integrableOn_of_Zeta0_fun hN hs

theorem equation_3_5_3 {N : ℕ} (hN : 0 < N) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s - (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) =
      s * remainder N s + (N : ℂ) ^ (1 - s) / (s - 1) -
        (1 / 2) * (N : ℂ) ^ (-s) := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have hsum : (∑ n ∈ range (N + 1), 1 / (n : ℂ) ^ s) =
      ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) := by
    rw [show Finset.Icc 1 N = (range (N + 1)).erase 0 by ext n; simp; omega,
      sum_erase_eq_sub (by simp)]
    simp [one_div, Complex.cpow_neg, Complex.zero_cpow hs0]
  rw [← Zeta0EqZeta hN hs hs1, riemannZeta0, hsum]
  rw [show 1 - s = -(s - 1) by ring, div_neg, neg_div, neg_neg]
  unfold remainder
  ring

theorem remainder_norm_le {N : ℕ} (hN : 0 < N) {s : ℂ} (hs : 0 < s.re) :
    ‖remainder N s‖ ≤ (N : ℝ) ^ (-s.re) / (2 * s.re) := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have he : -(s.re + 1) < -1 := by linarith
  have hi := (integrableOn_Ioi_rpow_of_lt he hN0).div_const 2
  calc
    ‖remainder N s‖ ≤ ∫ x in Set.Ioi (N : ℝ), x ^ (-(s.re + 1)) / 2 := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 < x := hN0.trans hx
      rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      have hn : ‖((⌊x⌋ : ℂ) + 1 / 2 - x)‖ = ‖(⌊x⌋ : ℝ) + 1 / 2 - x‖ := by
        rw [show ((⌊x⌋ : ℂ) + 1 / 2 - x) =
          (((⌊x⌋ : ℝ) + 1 / 2 - x : ℝ) : ℂ) by push_cast; rfl,
          Complex.norm_real]
      rw [hn, Complex.add_re, Complex.one_re]
      have hb := div_le_div_of_nonneg_right (ZetaSum_aux1_3 x)
        (Real.rpow_nonneg hx0.le (s.re + 1))
      calc
        _ ≤ (1 / 2) / x ^ (s.re + 1) := hb
        _ = _ := by rw [Real.rpow_neg hx0.le]; ring
    _ = (N : ℝ) ^ (-s.re) / (2 * s.re) := by
      rw [integral_div, integral_Ioi_rpow_of_lt he hN0,
        show -(s.re + 1) + 1 = -s.re by ring]
      ring

theorem equation_3_5_3_one {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = (s + 1) / (2 * (s - 1)) + s * remainder 1 s := by
  have h := equation_3_5_3 (N := 1) (by norm_num) hs hs1
  norm_num at h
  have hmain : (s + 1) / (2 * (s - 1)) = 1 / 2 + 1 / (s - 1) := by
    field_simp
    ring
  rw [hmain]
  linear_combination h

theorem zeta_norm_le_one_cutoff {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s‖ ≤ ‖s + 1‖ / (2 * ‖s - 1‖) + ‖s‖ / (2 * s.re) := by
  have hr := remainder_norm_le (N := 1) (by norm_num) hs
  norm_num at hr
  rw [equation_3_5_3_one hs hs1]
  have ht := norm_add_le ((s + 1) / (2 * (s - 1))) (s * remainder 1 s)
  rw [norm_div, norm_mul, norm_mul] at ht
  norm_num only [norm_ofNat] at ht
  have hm := mul_le_mul_of_nonneg_left hr (norm_nonneg s)
  simp only [div_eq_mul_inv, mul_inv_rev] at *
  norm_num at *
  linarith

theorem equation_3_39_first {sigma t : ℝ} (hs : 0 < sigma)
    (hs1 : (sigma : ℂ) + t * I ≠ 1) :
    ‖riemannZeta ((sigma : ℂ) + t * I)‖ ≤
      (1 / 2) * Real.sqrt (((sigma + 1) ^ 2 + t ^ 2) / ((sigma - 1) ^ 2 + t ^ 2)) +
        Real.sqrt (sigma ^ 2 + t ^ 2) / (2 * sigma) := by
  have h := zeta_norm_le_one_cutoff (s := (sigma : ℂ) + t * I) (by simpa) hs1
  have hn (a : ℝ) : ‖(a : ℂ) + t * I‖ = Real.sqrt (a ^ 2 + t ^ 2) := by
    rw [Complex.norm_def]
    congr 1
    simp [Complex.normSq_apply]
    ring
  have hp : (sigma : ℂ) + t * I + 1 = ((sigma + 1 : ℝ) : ℂ) + t * I := by push_cast; ring
  have hm : (sigma : ℂ) + t * I - 1 = ((sigma - 1 : ℝ) : ℂ) + t * I := by push_cast; ring
  rw [hp, hm, hn, hn, hn] at h
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, zero_mul, sub_self, add_zero] at h
  rw [Real.sqrt_div (by positivity)]
  simp only [div_eq_mul_inv, mul_inv_rev] at *
  linarith

end LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.Titchmarsh
