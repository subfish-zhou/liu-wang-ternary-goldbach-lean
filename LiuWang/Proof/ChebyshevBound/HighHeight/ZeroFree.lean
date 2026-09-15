import LiuWang.Proof.ChebyshevBound.HighHeight.LowZeros
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LogDerivativePositivity

/-!
# 全高度实际 ζ 零区

Euler 级数正性与单个 ξ 除子零点核结合。低高度由全体 ξ 正核支付，
高高度选定 σ=1+1/(6(log(|t|+2)+1))，得到明确常数 40。
-/

set_option autoImplicit false
noncomputable section

open Complex
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.ChebyshevBound.HighHeight

theorem zeta_three_four_one_nonneg {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤
      3 * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re +
      4 * (-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * I) /
        riemannZeta ((σ : ℂ) + (t : ℂ) * I)).re +
      (-deriv riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) /
        riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I)).re := by
  have h := logDerivative_combination_nonneg (N := 1)
    (1 : DirichletCharacter ℂ 1) hσ t
  simpa only [DirichletCharacter.LFunction_modOne_eq,
    Complex.ofReal_mul, Complex.ofReal_ofNat, mul_comm I (t : ℂ),
    mul_assoc] using h

theorem pole_re_le_delta {σ t : ℝ} (hσ : 1 < σ) (ht : 1 ≤ |t|) :
    (1 / (((σ : ℂ) + (t : ℂ) * I) - 1)).re ≤ σ - 1 := by
  have ht2 : 1 ≤ t ^ 2 := by
    simpa only [one_pow, sq_abs] using
      (sq_le_sq₀ zero_le_one (abs_nonneg t)).2 ht
  have hd : 1 ≤ (σ - 1) ^ 2 + t ^ 2 := by nlinarith [sq_nonneg (σ - 1)]
  have heq : (1 / (((σ : ℂ) + (t : ℂ) * I) - 1)).re =
      (σ - 1) / ((σ - 1) ^ 2 + t ^ 2) := by
    simp [Complex.inv_re, Complex.normSq_apply, pow_two]
  rw [heq]
  exact div_le_self (by linarith) hd

theorem selected_kernel_at_ordinate (p : RiemannXiDivisorZeroIndex) (σ : ℝ) :
    (1 / (((σ : ℂ) + ((riemannXiDivisorZeroValue p).im : ℂ) * I) -
      riemannXiDivisorZeroValue p)).re = 1 / (σ - (riemannXiDivisorZeroValue p).re) := by
  have heq : ((σ : ℂ) + ((riemannXiDivisorZeroValue p).im : ℂ) * I) -
      riemannXiDivisorZeroValue p = ((σ - (riemannXiDivisorZeroValue p).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [heq, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]

theorem zeta_zero_core_inequality (p : RiemannXiDivisorZeroIndex)
    {σ : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2) :
    4 / (σ - (riemannXiDivisorZeroValue p).re) ≤
      3 / (σ - 1) + 5 * (σ - 1) +
        (5 / 2 : ℝ) * Real.log (|(riemannXiDivisorZeroValue p).im| + 2) + 13 / 6 := by
  let t := (riemannXiDivisorZeroValue p).im
  have ht : 1 ≤ |t| := (xi_zero_height_gt_one p).le
  have ht2 : 1 ≤ |2 * t| := by rw [abs_mul]; norm_num; linarith
  have h0 := zeta_real_le_pole hσ hσ2
  have h1 := zeta_selected_zero_le (s := (σ : ℂ) + (t : ℂ) * I)
    (by simpa using hσ) p
  have h2 := zeta_without_zeros_le (s := (σ : ℂ) + ((2 * t : ℝ) : ℂ) * I)
    (by simpa using hσ)
  have ha1 := archimedean_re_le (s := (σ : ℂ) + (t : ℂ) * I)
    (by simpa using hσ.le) (by simpa using hσ2)
  have ha2 := archimedean_re_le (s := (σ : ℂ) + ((2 * t : ℝ) : ℂ) * I)
    (by simpa using hσ.le) (by simpa using hσ2)
  have hp1 := pole_re_le_delta hσ ht
  have hp2 := pole_re_le_delta hσ ht2
  have hk := selected_kernel_at_ordinate p σ
  change (1 / (((σ : ℂ) + (t : ℂ) * I) - riemannXiDivisorZeroValue p)).re = _ at hk
  rw [hk] at h1
  have hpos := zeta_three_four_one_nonneg hσ t
  have hlog : Real.log (|2 * t| + 2) ≤ Real.log (|t| + 2) + 1 := by
    calc
      _ ≤ Real.log (2 * (|t| + 2)) := by
        apply Real.log_le_log (by positivity)
        rw [abs_mul]
        norm_num
        linarith
      _ = Real.log 2 + Real.log (|t| + 2) := Real.log_mul (by norm_num) (by positivity)
      _ ≤ _ := by linarith [Real.log_two_lt_d9]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
    Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at ha1 ha2
  change 4 / (σ - (riemannXiDivisorZeroValue p).re) ≤
    3 / (σ - 1) + 5 * (σ - 1) + (5 / 2 : ℝ) * Real.log (|t| + 2) + 13 / 6
  simp only [div_eq_mul_inv] at h0 h1 h2 ha1 ha2 hp1 hp2 hpos ⊢
  linarith

theorem xi_zero_gap_explicit (p : RiemannXiDivisorZeroIndex) :
    1 / (40 * (Real.log (|(riemannXiDivisorZeroValue p).im| + 2) + 1)) <
      1 - (riemannXiDivisorZeroValue p).re := by
  let L := Real.log (|(riemannXiDivisorZeroValue p).im| + 2) + 1
  have hlog : 1 ≤ Real.log (|(riemannXiDivisorZeroValue p).im| + 2) := by
    apply (Real.le_log_iff_exp_le (by positivity)).2
    have ht := xi_zero_height_gt_one p
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  have hL : 2 ≤ L := by dsimp [L]; linarith
  have hL0 : 0 < L := by linarith
  let δ : ℝ := 1 / (6 * L)
  let σ : ℝ := 1 + δ
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδupper : δ ≤ 1 / 12 := by
    dsimp [δ]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hσ : 1 < σ := by dsimp [σ]; linarith
  have hσ2 : σ ≤ 2 := by dsimp [σ]; linarith
  have hcore := zeta_zero_core_inequality p hσ hσ2
  have hδL : δ * L = 1 / 6 := by dsimp [δ]; field_simp
  have hdinv : 3 / δ = 18 * L := by dsimp [δ]; field_simp; ring
  have hden : 0 < σ - (riemannXiDivisorZeroValue p).re := by
    have := (riemannXiDivisorZeroValue_re_mem_Ioo p).2
    linarith
  have hbudget :
      3 / (σ - 1) + 5 * (σ - 1) +
        (5 / 2 : ℝ) * Real.log (|(riemannXiDivisorZeroValue p).im| + 2) + 13 / 6 ≤
          (83 / 4 : ℝ) * L := by
    rw [show σ - 1 = δ by dsimp [σ]; ring, hdinv]
    have hLeq : Real.log (|(riemannXiDivisorZeroValue p).im| + 2) = L - 1 := by
      dsimp [L]; ring
    rw [hLeq]
    linarith
  have hmul := (div_le_iff₀ hden).1 (hcore.trans hbudget)
  change 1 / (40 * L) < 1 - (riemannXiDivisorZeroValue p).re
  by_contra! hgap
  have hgapL : (1 - (riemannXiDivisorZeroValue p).re) * L ≤ 1 / 40 := by
    have h := (le_div_iff₀ (by positivity : 0 < 40 * L)).1 hgap
    nlinarith
  have hnear : (σ - (riemannXiDivisorZeroValue p).re) * L ≤ 23 / 120 := by
    dsimp [σ]
    nlinarith
  nlinarith

theorem zeta_zero_free_explicit {s : ℂ}
    (hs : 1 - 1 / (40 * (Real.log (|s.im| + 2) + 1)) ≤ s.re) :
    riemannZeta s ≠ 0 := by
  have hlog : 0 ≤ Real.log (|s.im| + 2) := Real.log_nonneg (by linarith [abs_nonneg s.im])
  have hwidth : 1 / (40 * (Real.log (|s.im| + 2) + 1)) ≤ 1 / 40 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hs0 : 0 < s.re := by linarith
  intro hz
  obtain ⟨p, hp⟩ := exists_xi_index_of_zeta_zero hs0 hz
  have hgap := xi_zero_gap_explicit p
  rw [hp] at hgap
  linarith

end LiuWang.Proof.ChebyshevBound.HighHeight
