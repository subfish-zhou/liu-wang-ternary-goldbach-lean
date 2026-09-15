import LiuWang.Proof.GlobalZeroDensity.Sharp.Mollifier
import PrimeNumberTheoremAnd.ZetaBounds

/-! The centered Euler--Maclaurin remainder with an actual natural truncation. -/

set_option autoImplicit false

noncomputable section

open Finset Complex MeasureTheory Set

namespace LiuWang.Proof.GlobalZeroDensity.Sharp

theorem centered_remainder_bound {N : ℕ} (hN : 0 < N) {s : ℂ} (hs : s.re = 1 / 2) :
    ‖∫ x in Ioi (N : ℝ),
      ((⌊x⌋ : ℂ) + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ ≤
        (Real.sqrt (N : ℝ))⁻¹ := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hint : IntegrableOn (fun x : ℝ => x ^ (-(3 / 2 : ℝ)) / 2) (Ioi (N : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : -(3 / 2 : ℝ) < -1) hn).div_const 2
  calc
    _ ≤ ∫ x in Ioi (N : ℝ), x ^ (-(3 / 2 : ℝ)) / 2 := by
      apply norm_integral_le_of_norm_le hint
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 < x := hn.trans hx
      rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      have he : ‖((⌊x⌋ : ℂ) + 1 / 2 - x)‖ = ‖(⌊x⌋ : ℝ) + 1 / 2 - x‖ := by
        have he' : ((⌊x⌋ : ℂ) + 1 / 2 - x) =
            (((⌊x⌋ : ℝ) + 1 / 2 - x : ℝ) : ℂ) := by push_cast; rfl
        rw [he', Complex.norm_real]
      rw [he, Complex.add_re, Complex.one_re, hs]
      have hb := div_le_div_of_nonneg_right (ZetaSum_aux1_3 x)
        (Real.rpow_nonneg hx0.le (1 / 2 + 1))
      convert hb using 1
      · rfl
      · rw [show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num, Real.rpow_neg hx0.le]
        ring
    _ = _ := by
      rw [integral_div, integral_Ioi_rpow_of_lt (by norm_num : -(3 / 2 : ℝ) < -1) hn]
      norm_num
      rw [show -(1 / 2 : ℝ) = -(1 / 2) by rfl, Real.rpow_neg hn.le,
        ← Real.sqrt_eq_rpow]
      ring

theorem centered_remainder_integrable {N : ℕ} (hN : 0 < N) {s : ℂ}
    (hs : s.re = 1 / 2) :
    IntegrableOn (fun x : ℝ =>
      ((⌊x⌋ : ℂ) + 1 / 2 - x) / (x : ℂ) ^ (s + 1)) (Ioi (N : ℝ)) := by
  have h := integrableOn_of_Zeta0_fun hN (s := s) (by rw [hs]; norm_num)
  simpa only [div_eq_mul_inv, Complex.cpow_neg] using h

theorem zeta_centered_formula {N : ℕ} (hN : 0 < N) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s =
      (∑ n ∈ range N, 1 / (n : ℂ) ^ s) +
      (1 / 2) / (N : ℂ) ^ s + (N : ℂ) ^ (1 - s) / (s - 1) +
      s * ∫ x in Ioi (N : ℝ),
        ((⌊x⌋ : ℂ) + 1 / 2 - x) / (x : ℂ) ^ (s + 1) := by
  rw [← Zeta0EqZeta hN hs hs1, riemannZeta0, sum_range_succ, Complex.cpow_neg]
  have hd : 1 - s = -(s - 1) := by ring
  rw [hd, div_neg, neg_div, neg_neg]
  ring

theorem norm_zeta_centered_le {N : ℕ} (hN : 0 < N) (t : ℝ) :
    ‖riemannZeta ((1 / 2 : ℂ) + t * Complex.I)‖ ≤
      (∑ n ∈ range N, (Real.sqrt (n : ℝ))⁻¹) +
        (1 / 2) / Real.sqrt N +
        Real.sqrt N / ‖(1 / 2 : ℂ) + t * Complex.I - 1‖ +
        ‖(1 / 2 : ℂ) + t * Complex.I‖ / Real.sqrt N := by
  let s : ℂ := (1 / 2 : ℂ) + t * Complex.I
  have hs : s.re = 1 / 2 := by simp [s]
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.re h; norm_num [s] at this
  have hs0 : s ≠ 0 := by
    intro h; have := congrArg Complex.re h; norm_num [s] at this
  have hnorm : ‖(N : ℂ) ^ s‖ = Real.sqrt N := by
    rw [Complex.norm_natCast_cpow_of_pos hN, hs, ← Real.sqrt_eq_rpow]
  have hnorm' : ‖(N : ℂ) ^ (1 - s)‖ = Real.sqrt N := by
    rw [Complex.norm_natCast_cpow_of_pos hN]
    simp only [Complex.sub_re, Complex.one_re, hs]
    norm_num
    rw [← Real.sqrt_eq_rpow]
  have hsum : ‖∑ n ∈ range N, 1 / (n : ℂ) ^ s‖ ≤
      ∑ n ∈ range N, (Real.sqrt (n : ℝ))⁻¹ := by
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro n _
    by_cases hn : n = 0
    · subst n; simp [Complex.zero_cpow hs0]
    · rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
        hs, ← Real.sqrt_eq_rpow, one_div]
  change ‖riemannZeta s‖ ≤ _
  rw [zeta_centered_formula hN (by rw [hs]; norm_num) hs1]
  have h1 := norm_add_le
    ((∑ n ∈ range N, 1 / (n : ℂ) ^ s) + (1 / 2) / (N : ℂ) ^ s +
      (N : ℂ) ^ (1 - s) / (s - 1))
    (s * ∫ x in Ioi (N : ℝ), ((⌊x⌋ : ℂ) + 1 / 2 - x) / (x : ℂ) ^ (s + 1))
  have h2 := norm_add_le
    ((∑ n ∈ range N, 1 / (n : ℂ) ^ s) + (1 / 2) / (N : ℂ) ^ s)
    ((N : ℂ) ^ (1 - s) / (s - 1))
  have h3 := norm_add_le
    (∑ n ∈ range N, 1 / (n : ℂ) ^ s) ((1 / 2) / (N : ℂ) ^ s)
  have hr := mul_le_mul_of_nonneg_left (centered_remainder_bound hN hs) (norm_nonneg s)
  rw [norm_mul] at h1
  rw [norm_div, hnorm'] at h2
  rw [norm_div, hnorm] at h3
  norm_num only [norm_div, norm_one, norm_ofNat] at h3
  change _ ≤ _
  simp only [div_eq_mul_inv] at *
  linarith

end LiuWang.Proof.GlobalZeroDensity.Sharp
