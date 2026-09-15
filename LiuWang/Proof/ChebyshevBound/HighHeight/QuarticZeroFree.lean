import LiuWang.Proof.ChebyshevBound.HighHeight.QuarticPositivity

/-! # 常数 20、覆盖所有高度的实际 ζ 无零区。 -/

set_option autoImplicit false
noncomputable section

open Complex BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.ChebyshevBound.HighHeight

theorem vertical_logderiv_le {σ u : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2)
    (hu : 1 ≤ |u|) :
    (-deriv riemannZeta ((σ : ℂ) + I * (u : ℂ)) /
      riemannZeta ((σ : ℂ) + I * (u : ℂ))).re ≤
        σ - 1 + Real.log (|u| + 2) / 2 + 1 / 3 := by
  have hz := zeta_without_zeros_le (s := (σ : ℂ) + I * (u : ℂ)) (by simpa using hσ)
  have ha := archimedean_re_le (s := (σ : ℂ) + I * (u : ℂ))
    (by simpa using hσ.le) (by simpa using hσ2)
  have hp := pole_re_le_delta hσ hu
  rw [mul_comm (u : ℂ) I] at hp
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_re, one_mul, zero_add] at ha
  linarith

theorem log_harmonic_height_le {t : ℝ} {k : ℕ} (hk : 1 ≤ k) :
    Real.log (|(k : ℝ) * t| + 2) ≤ Real.log (|t| + 2) + (k - 1 : ℝ) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  calc
    _ ≤ Real.log ((k : ℝ) * (|t| + 2)) := by
      apply Real.log_le_log (by positivity)
      rw [abs_mul, abs_of_pos hk0]
      nlinarith
    _ = Real.log (k : ℝ) + Real.log (|t| + 2) :=
      Real.log_mul hk0.ne' (by positivity)
    _ ≤ _ := by linarith [Real.log_le_sub_one_of_pos hk0]

theorem quartic_zero_core (p : RiemannXiDivisorZeroIndex)
    {σ : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2) :
    56 / (σ - (riemannXiDivisorZeroValue p).re) ≤
      35 / (σ - 1) + 93 * (σ - 1) +
        (93 / 2 : ℝ) * Real.log (|(riemannXiDivisorZeroValue p).im| + 2) + 109 / 2 := by
  let t := (riemannXiDivisorZeroValue p).im
  have ht : 1 ≤ |t| := (xi_zero_height_gt_one p).le
  have hkt (k : ℕ) (hk : 1 ≤ k) : 1 ≤ |(k : ℝ) * t| := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have h0 := zeta_real_le_pole hσ hσ2
  have h1 := zeta_selected_zero_le (s := (σ : ℂ) + I * (t : ℂ))
    (by simpa using hσ) p
  have ha := archimedean_re_le (s := (σ : ℂ) + I * (t : ℂ))
    (by simpa using hσ.le) (by simpa using hσ2)
  have hp := pole_re_le_delta hσ ht
  rw [mul_comm (t : ℂ) I] at hp
  have hk := selected_kernel_at_ordinate p σ
  change (1 / (((σ : ℂ) + (t : ℂ) * I) - riemannXiDivisorZeroValue p)).re = _ at hk
  rw [mul_comm (t : ℂ) I] at hk
  rw [hk] at h1
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_re, one_mul, zero_add] at ha
  have h2 := vertical_logderiv_le hσ hσ2 (hkt 2 (by norm_num))
  have h3 := vertical_logderiv_le hσ hσ2 (hkt 3 (by norm_num))
  have h4 := vertical_logderiv_le hσ hσ2 (hkt 4 (by norm_num))
  have hl2 := log_harmonic_height_le (t := t) (k := 2) (by norm_num)
  have hl3 := log_harmonic_height_le (t := t) (k := 3) (by norm_num)
  have hl4 := log_harmonic_height_le (t := t) (k := 4) (by norm_num)
  norm_num only [Nat.cast_ofNat] at h2 h3 h4 hl2 hl3 hl4
  have hpos := zeta_quartic_nonneg hσ t
  change 56 / (σ - (riemannXiDivisorZeroValue p).re) ≤
    35 / (σ - 1) + 93 * (σ - 1) + (93 / 2 : ℝ) * Real.log (|t| + 2) + 109 / 2
  simp only [div_eq_mul_inv] at h0 h1 h2 h3 h4 ha hp hpos ⊢
  linarith

theorem xi_zero_gap_twenty (p : RiemannXiDivisorZeroIndex) :
    1 / (20 * (Real.log (|(riemannXiDivisorZeroValue p).im| + 2) + 2)) <
      1 - (riemannXiDivisorZeroValue p).re := by
  let L := Real.log (|(riemannXiDivisorZeroValue p).im| + 2) + 2
  have hlog : 1 ≤ Real.log (|(riemannXiDivisorZeroValue p).im| + 2) := by
    apply (Real.le_log_iff_exp_le (by positivity)).2
    have ht := xi_zero_height_gt_one p
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  have hL : 3 ≤ L := by dsimp [L]; linarith
  have hL0 : 0 < L := by linarith
  let δ : ℝ := 1 / (5 * L)
  let σ : ℝ := 1 + δ
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδupper : δ ≤ 1 / 15 := by
    dsimp [δ]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hσ : 1 < σ := by dsimp [σ]; linarith
  have hσ2 : σ ≤ 2 := by dsimp [σ]; linarith
  have hcore := quartic_zero_core p hσ hσ2
  have hδL : δ * L = 1 / 5 := by dsimp [δ]; field_simp
  have hdinv : 35 / δ = 175 * L := by dsimp [δ]; field_simp; ring
  have hden : 0 < σ - (riemannXiDivisorZeroValue p).re := by
    have := (riemannXiDivisorZeroValue_re_mem_Ioo p).2
    linarith
  have hbudget :
      35 / (σ - 1) + 93 * (σ - 1) +
        (93 / 2 : ℝ) * Real.log (|(riemannXiDivisorZeroValue p).im| + 2) + 109 / 2 ≤
          222 * L := by
    rw [show σ - 1 = δ by dsimp [σ]; ring, hdinv]
    have hLeq : Real.log (|(riemannXiDivisorZeroValue p).im| + 2) = L - 2 := by
      dsimp [L]; ring
    rw [hLeq]
    linarith
  have hmul := (div_le_iff₀ hden).1 (hcore.trans hbudget)
  change 1 / (20 * L) < 1 - (riemannXiDivisorZeroValue p).re
  by_contra! hgap
  have hgapL : (1 - (riemannXiDivisorZeroValue p).re) * L ≤ 1 / 20 := by
    have h := (le_div_iff₀ (by positivity : 0 < 20 * L)).1 hgap
    nlinarith
  have hnear : (σ - (riemannXiDivisorZeroValue p).re) * L ≤ 1 / 4 := by
    dsimp [σ]
    nlinarith
  nlinarith

theorem zeta_zero_free_twenty {s : ℂ}
    (hs : 1 - 1 / (20 * (Real.log (|s.im| + 2) + 2)) ≤ s.re) :
    riemannZeta s ≠ 0 := by
  have hlog : 0 ≤ Real.log (|s.im| + 2) := Real.log_nonneg (by linarith [abs_nonneg s.im])
  have hwidth : 1 / (20 * (Real.log (|s.im| + 2) + 2)) ≤ 1 / 40 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hs0 : 0 < s.re := by linarith
  intro hz
  obtain ⟨p, hp⟩ := exists_xi_index_of_zeta_zero hs0 hz
  have hgap := xi_zero_gap_twenty p
  rw [hp] at hgap
  linarith

end LiuWang.Proof.ChebyshevBound.HighHeight
