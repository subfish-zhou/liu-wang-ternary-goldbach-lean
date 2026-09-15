import LiuWang.Proof.ChebyshevBound.HighHeight.Gamma
import BombieriVinogradov.Helpers.ComplexAnalysis.DivisorZeroIndex

/-! # 由完整 ξ 正核总量排除中间低高度；不使用零点表或 RH。 -/

set_option autoImplicit false
noncomputable section

open Complex
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.ChebyshevBound.HighHeight

theorem xi_constant_lt_third :
    Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi) < 1 / 3 := by
  rw [Real.log_mul (by norm_num) Real.pi_ne_zero, Real.log_four_eq]
  linarith [Real.eulerMascheroniConstant_lt_two_thirds, log_two_ge_two_thirds,
    log_pi_ge_one]

theorem xiTerm_one_re (p : RiemannXiDivisorZeroIndex) :
    (xiTerm 1 p).re =
      (1 - (riemannXiDivisorZeroValue p).re) /
        ((1 - (riemannXiDivisorZeroValue p).re) ^ 2 +
          (riemannXiDivisorZeroValue p).im ^ 2) +
      (riemannXiDivisorZeroValue p).re /
        ((riemannXiDivisorZeroValue p).re ^ 2 +
          (riemannXiDivisorZeroValue p).im ^ 2) := by
  simp [xiTerm, Complex.inv_re, Complex.normSq_apply, pow_two]

theorem xiTerm_one_re_lower (p : RiemannXiDivisorZeroIndex) :
    1 / (1 + (riemannXiDivisorZeroValue p).im ^ 2) ≤ (xiTerm 1 p).re := by
  obtain ⟨hb0, hb1⟩ := riemannXiDivisorZeroValue_re_mem_Ioo p
  let β := (riemannXiDivisorZeroValue p).re
  let t := (riemannXiDivisorZeroValue p).im
  have ht : 0 ≤ t ^ 2 := sq_nonneg _
  have hβ : 0 < β := hb0
  have hβ1 : β < 1 := hb1
  have h1 : 0 < (1 - β) ^ 2 + t ^ 2 := by nlinarith
  have h2 : 0 < β ^ 2 + t ^ 2 := by nlinarith
  rw [xiTerm_one_re]
  change 1 / (1 + t ^ 2) ≤ (1 - β) / ((1 - β) ^ 2 + t ^ 2) + β / (β ^ 2 + t ^ 2)
  calc
    _ = (1 - β) / (1 + t ^ 2) + β / (1 + t ^ 2) := by ring
    _ ≤ _ := add_le_add
      (div_le_div_of_nonneg_left (by linarith) h1 (by nlinarith))
      (div_le_div_of_nonneg_left hβ.le h2 (by nlinarith))

theorem xi_zero_height_gt_one (p : RiemannXiDivisorZeroIndex) :
    1 < |(riemannXiDivisorZeroValue p).im| := by
  have hterm := xiTerm_re_le_sum (s := 1) (by norm_num) p
  rw [xiTerm_sum_one] at hterm
  norm_num only [Complex.sub_re, Complex.add_re, Complex.ofReal_re] at hterm
  have hlo := xiTerm_one_re_lower p
  by_contra! h
  have hs : (riemannXiDivisorZeroValue p).im ^ 2 ≤ 1 := by
    have := (sq_le_sq₀ (abs_nonneg _) zero_le_one).2 h
    simpa only [sq_abs, one_pow] using this
  have hhalf : (1 / 2 : ℝ) ≤ 1 / (1 + (riemannXiDivisorZeroValue p).im ^ 2) := by
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hc := xi_constant_lt_third
  norm_num at hterm
  linarith

theorem exists_xi_index_of_zeta_zero {s : ℂ} (hs : 0 < s.re)
    (hz : riemannZeta s = 0) :
    ∃ p : RiemannXiDivisorZeroIndex, riemannXiDivisorZeroValue p = s := by
  have hs0 : s ≠ 0 := by
    intro h
    simp [h] at hs
  have hs1 : s ≠ 1 := by
    intro h
    exact riemannZeta_one_ne_zero (h ▸ hz)
  have hgamma : Complex.Gamma (s / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simpa using half_pos hs)
  have hxi : Complex.riemannXi s = 0 := by
    rw [Complex.riemannXi_eq_mul_completedRiemannZeta hs0 hs1,
      completedRiemannZeta_eq_cpow_mul_Gamma_mul_riemannZeta hs0 hgamma, hz]
    simp
  exact BombieriVinogradov.exists_divisorZeroIndex₀_val_eq_of_apply_eq_zero
    Complex.differentiable_riemannXi
    ⟨0, by rw [Complex.riemannXi_zero]; norm_num⟩ hs0 hxi

theorem zeta_ne_zero_height_le_one {s : ℂ} (hs : 0 < s.re) (ht : |s.im| ≤ 1) :
    riemannZeta s ≠ 0 := by
  intro hz
  obtain ⟨p, hp⟩ := exists_xi_index_of_zeta_zero hs hz
  have h := xi_zero_height_gt_one p
  rw [hp] at h
  linarith

end LiuWang.Proof.ChebyshevBound.HighHeight
