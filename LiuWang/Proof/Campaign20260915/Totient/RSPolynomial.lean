import LiuWang.Proof.Campaign20260915.Totient.RSGamma

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Complex ArithmeticFunction
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ChebyshevBound.HighHeight
open scoped LSeries.notation

namespace LiuWang.Proof.Campaign20260915.Totient

theorem rs_unit_circle_nonneg {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ (322 + 546 * z + 329 * z ^ 2 + 130 * z ^ 3 + 25 * z ^ 4).re := by
  have hy : z.im ^ 2 = 1 - z.re ^ 2 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [hz] at h
    simp only [Complex.normSq_apply] at h
    nlinarith
  have heq : (322 + 546 * z + 329 * z ^ 2 + 130 * z ^ 3 + 25 * z ^ 4).re =
      2 * (1 + z.re) ^ 2 * (3 + 10 * z.re) ^ 2 := by
    norm_num [pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re]
    ring_nf
    rw [show z.im ^ 4 = (z.im ^ 2) ^ 2 by ring, hy]
    ring
  rw [heq]
  positivity

theorem rs_mangoldt_terms_nonneg (σ t : ℝ) (n : ℕ) :
    0 ≤
      322 * (LSeries.term (↗Λ) (σ : ℂ) n).re +
      546 * (LSeries.term (↗Λ) ((σ : ℂ) + I * (t : ℂ)) n).re +
      329 * (LSeries.term (↗Λ) ((σ : ℂ) + I * ((2 * t : ℝ) : ℂ)) n).re +
      130 * (LSeries.term (↗Λ) ((σ : ℂ) + I * ((3 * t : ℝ) : ℂ)) n).re +
      25 * (LSeries.term (↗Λ) ((σ : ℂ) + I * ((4 * t : ℝ) : ℂ)) n).re := by
  by_cases hn : n = 0
  · subst n; simp
  let z := (n : ℂ) ^ (-(I * (t : ℂ)))
  have hz : ‖z‖ = 1 := by
    dsimp [z]
    rw [← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn)]
    norm_num [Complex.mul_re]
  have hh := rs_unit_circle_nonneg hz
  have h0 := mangoldt_term_harmonic hn σ t 0
  have h1 := mangoldt_term_harmonic hn σ t 1
  have h2 := mangoldt_term_harmonic hn σ t 2
  have h3 := mangoldt_term_harmonic hn σ t 3
  have h4 := mangoldt_term_harmonic hn σ t 4
  norm_num only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, Complex.ofReal_zero,
    zero_mul, one_mul, mul_zero, add_zero, pow_zero, pow_one, mul_one] at h0 h1 h2 h3 h4
  rw [h0, h1, h2, h3, h4]
  have h := mul_nonneg
    (mul_nonneg (vonMangoldt_nonneg (n := n))
      (Real.rpow_nonneg (Nat.cast_nonneg n) (-σ))) hh
  dsimp [z] at h
  norm_num [Complex.add_re, Complex.mul_re, Complex.ofReal_mul] at h ⊢
  nlinarith only [h]

theorem rs_zeta_combination_nonneg {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤
      322 * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re +
      546 * (-deriv riemannZeta ((σ : ℂ) + I * (t : ℂ)) /
        riemannZeta ((σ : ℂ) + I * (t : ℂ))).re +
      329 * (-deriv riemannZeta ((σ : ℂ) + I * ((2 * t : ℝ) : ℂ)) /
        riemannZeta ((σ : ℂ) + I * ((2 * t : ℝ) : ℂ))).re +
      130 * (-deriv riemannZeta ((σ : ℂ) + I * ((3 * t : ℝ) : ℂ)) /
        riemannZeta ((σ : ℂ) + I * ((3 * t : ℝ) : ℂ))).re +
      25 * (-deriv riemannZeta ((σ : ℂ) + I * ((4 * t : ℝ) : ℂ)) /
        riemannZeta ((σ : ℂ) + I * ((4 * t : ℝ) : ℂ))).re := by
  have hs (u : ℝ) : HasSum
      (fun n => (LSeries.term (↗Λ) ((σ : ℂ) + I * (u : ℂ)) n).re)
      (-deriv riemannZeta ((σ : ℂ) + I * (u : ℂ)) /
        riemannZeta ((σ : ℂ) + I * (u : ℂ))).re := by
    have hre : 1 < ((σ : ℂ) + I * (u : ℂ)).re := by simpa using hσ
    have h := Complex.hasSum_re (LSeriesSummable_vonMangoldt hre).LSeriesHasSum
    rwa [LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre] at h
  have h := ((((hs 0).mul_left 322).add ((hs t).mul_left 546)).add
    ((hs (2 * t)).mul_left 329)).add ((hs (3 * t)).mul_left 130)
  have hsum := h.add ((hs (4 * t)).mul_left 25)
  simp only [Complex.ofReal_zero, mul_zero, add_zero] at hsum
  rw [← hsum.tsum_eq]
  exact tsum_nonneg (rs_mangoldt_terms_nonneg σ t)

private theorem vertical_high {σ u : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2)
    (hu : 1000 ≤ |u|) :
    (-deriv riemannZeta ((σ : ℂ) + I * (u : ℂ)) /
      riemannZeta ((σ : ℂ) + I * (u : ℂ))).re ≤
        σ - 1 + Real.log |u| / 2 - 1 / 4 := by
  have hz := zeta_without_zeros_le (s := (σ : ℂ) + I * (u : ℂ)) (by simpa using hσ)
  have ha := rs_archimedean_high (s := (σ : ℂ) + I * (u : ℂ))
    (by simpa using hσ.le) (by simpa using hσ2) (by simpa using hu)
  have hp := pole_re_le_delta hσ (show 1 ≤ |u| by linarith)
  rw [mul_comm (u : ℂ) I] at hp
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_re, one_mul, zero_add] at ha
  linarith

theorem rs_zero_core (p : RiemannXiDivisorZeroIndex)
    (ht : 1000 ≤ |(riemannXiDivisorZeroValue p).im|)
    {σ : ℝ} (hσ : 1 < σ) (hσhi : σ ≤ 1 + 1 / 40) :
    546 / (σ - (riemannXiDivisorZeroValue p).re) <
      322 / (σ - 1) + 515 * Real.log |(riemannXiDivisorZeroValue p).im| := by
  let t := (riemannXiDivisorZeroValue p).im
  have hσ2 : σ ≤ 2 := by linarith
  have hkt (k : ℕ) (hk : 1 ≤ k) : 1000 ≤ |(k : ℝ) * t| := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    change 1000 ≤ |t| at ht
    nlinarith
  have h0 := zeta_real_le_pole hσ hσ2
  have h1 := zeta_selected_zero_le (s := (σ : ℂ) + I * (t : ℂ))
    (by simpa using hσ) p
  have ha := rs_archimedean_high (s := (σ : ℂ) + I * (t : ℂ))
    (by simpa using hσ.le) (by simpa using hσ2) (by simpa using ht)
  have hp := pole_re_le_delta hσ (show 1 ≤ |t| by dsimp [t]; linarith)
  rw [mul_comm (t : ℂ) I] at hp
  have hk := selected_kernel_at_ordinate p σ
  rw [mul_comm (t : ℂ) I] at hk
  rw [hk] at h1
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_re, one_mul, zero_add] at ha
  have h2 := vertical_high hσ hσ2 (hkt 2 (by norm_num))
  have h3 := vertical_high hσ hσ2 (hkt 3 (by norm_num))
  have h4 := vertical_high hσ hσ2 (hkt 4 (by norm_num))
  have hlog (k : ℕ) (hk : 0 < k) :
      Real.log |(k : ℝ) * t| = Real.log (k : ℝ) + Real.log |t| := by
    rw [abs_mul, abs_of_pos (by exact_mod_cast hk),
      Real.log_mul (by exact_mod_cast hk.ne') (by dsimp [t]; positivity)]
  rw [hlog 2 (by norm_num)] at h2
  rw [hlog 3 (by norm_num)] at h3
  rw [hlog 4 (by norm_num)] at h4
  norm_num only [Nat.cast_ofNat] at h2 h3 h4
  rw [Real.log_four_eq] at h4
  have hpos := rs_zeta_combination_nonneg hσ t
  change 546 / (σ - (riemannXiDivisorZeroValue p).re) <
    322 / (σ - 1) + 515 * Real.log |t|
  simp only [div_eq_mul_inv] at h0 h1 h2 h3 h4 ha hp hpos ⊢
  linarith [Real.log_two_lt_d9, Real.log_three_lt_d9]

#print axioms rs_zero_core

end LiuWang.Proof.Campaign20260915.Totient
