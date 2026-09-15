import LiuWang.Proof.PrincipalPsi.Quantitative.LogDerivative
import LiuWang.Proof.LocalAnalyticBounds.LeftVertical.Integrand

/-! # 左线的实际粗多项式界：只消费无条件 xi 倒数平方总量 -/

set_option autoImplicit false
noncomputable section

open Complex
open scoped BigOperators
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ChebyshevBound.HighHeight
open LiuWang.Proof.LocalAnalyticBounds

namespace LiuWang.Proof.PrincipalPsi.Quantitative

theorem norm_logDeriv_xi_zero_le : ‖logDeriv riemannXi 0‖ ≤ 4 := by
  have he := congrArg norm neg_two_mul_logDeriv_riemannXi_zero_eq
  have hgamma : ‖(Real.eulerMascheroniConstant : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by
      linarith [Real.one_half_lt_eulerMascheroniConstant])]
    linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  have hlog : ‖(Real.log (4 * Real.pi) : ℂ)‖ ≤ 5 := by
    rw [Complex.norm_real, Real.norm_of_nonneg
      (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
    rw [Real.log_mul (by norm_num) Real.pi_ne_zero, Real.log_four_eq]
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2),
      Real.log_le_sub_one_of_pos Real.pi_pos, Real.pi_lt_four]
  have htri := (norm_sub_le ((Real.eulerMascheroniConstant : ℂ) + 2)
    (Real.log (4 * Real.pi) : ℂ)).trans (add_le_add (norm_add_le _ _) le_rfl)
  norm_num only [norm_mul, norm_neg, Complex.norm_ofNat] at he htri
  linarith

theorem norm_xiTerm_left_le {s : ℂ} (hs : s.re = -1 / 2)
    (p : RiemannXiDivisorZeroIndex) :
    ‖xiTerm s p‖ ≤ 3 * (|s.im| + 2) ^ 2 *
      (1 / (riemannXiDivisorZeroValue p).im ^ 2) := by
  let rho := riemannXiDivisorZeroValue p
  obtain ⟨hb0, _⟩ := riemannXiDivisorZeroValue_re_mem_Ioo p
  have hnorm : 1 / 2 ≤ ‖s - rho‖ := by
    have h := Complex.abs_re_le_norm (s - rho)
    rw [Complex.sub_re, hs, abs_of_neg (by dsimp [rho]; linarith)] at h
    dsimp [rho] at *
    linarith
  have hsn : s - rho ≠ 0 := norm_pos_iff.mp (by linarith)
  have hrn : rho ≠ 0 := riemannXiDivisorZeroValue_ne_zero p
  have hγ : 0 < rho.im ^ 2 := by
    have hh := xi_zero_height_gt_one p
    change 1 < |rho.im| at hh
    nlinarith [sq_abs rho.im]
  have hsq : rho.im ^ 2 ≤ ‖rho‖ ^ 2 := by
    have h := Complex.abs_im_le_norm rho
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr h
  have hsNorm : ‖s‖ ≤ |s.im| + 2 := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    norm_num [hs] at h
    linarith
  have htri : ‖rho‖ ≤ ‖s - rho‖ + ‖s‖ := by
    simpa only [norm_sub_rev] using norm_le_norm_sub_add rho s
  have hprod : ‖s‖ * ‖rho‖ ≤ 3 * (|s.im| + 2) ^ 2 * ‖s - rho‖ := by
    have h1 := mul_le_mul_of_nonneg_left htri (norm_nonneg s)
    have h2 : 1 ≤ 2 * ‖s - rho‖ := by linarith
    have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg ‖s‖)
    have h4 : ‖s‖ + 2 * ‖s‖ ^ 2 ≤ 3 * (|s.im| + 2) ^ 2 := by
      have hh : ‖s‖ ^ 2 ≤ (|s.im| + 2) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hsNorm _
      nlinarith [abs_nonneg s.im]
    nlinarith [mul_le_mul_of_nonneg_right h4 (norm_nonneg (s - rho))]
  have heq : xiTerm s p = s / ((s - rho) * rho) := by
    change 1 / (s - rho) + 1 / rho = s / ((s - rho) * rho)
    field_simp [hsn, hrn]
    ring
  rw [heq, norm_div, norm_mul]
  calc
    _ ≤ (3 * (|s.im| + 2) ^ 2) / ‖rho‖ ^ 2 := by
      apply (div_le_div_iff₀
        (mul_pos (norm_pos_iff.mpr hsn) (norm_pos_iff.mpr hrn))
        (sq_pos_of_pos (norm_pos_iff.mpr hrn))).mpr
      nlinarith [mul_le_mul_of_nonneg_right hprod (norm_nonneg rho)]
    _ ≤ (3 * (|s.im| + 2) ^ 2) / rho.im ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) hγ hsq
    _ = _ := by ring

theorem norm_logDeriv_zeta_left {s : ℂ} (hs : s.re = -1 / 2) :
    ‖logDeriv riemannZeta s‖ ≤ 20 * (|s.im| + 2) ^ 2 := by
  have hs1 : s ≠ 1 := by intro h; norm_num [h] at hs
  have haway : ∀ p : RiemannXiDivisorZeroIndex, s ≠ riemannXiDivisorZeroValue p := by
    intro p hp
    have h := (riemannXiDivisorZeroValue_re_mem_Ioo p).1
    rw [← hp, hs] at h
    norm_num at h
  have hsum := summable_riemannXi_logDerivTerms_divisorZeroIndex₀ haway
  have hzeroSum : ‖∑' p, xiTerm s p‖ ≤ 2 * (|s.im| + 2) ^ 2 := by
    calc
      _ ≤ ∑' p, ‖xiTerm s p‖ := norm_tsum_le_tsum_norm hsum.norm
      _ ≤ ∑' p : RiemannXiDivisorZeroIndex,
          3 * (|s.im| + 2) ^ 2 * (1 / (riemannXiDivisorZeroValue p).im ^ 2) :=
        hsum.norm.tsum_le_tsum (norm_xiTerm_left_le hs)
          (xi_height_inverse_square_summable.mul_left _)
      _ = 3 * (|s.im| + 2) ^ 2 *
          ∑' p : RiemannXiDivisorZeroIndex, 1 / (riemannXiDivisorZeroValue p).im ^ 2 :=
        tsum_mul_left
      _ ≤ _ := (mul_le_mul_of_nonneg_left xi_height_inverse_square_sum_le
        (by positivity : 0 ≤ 3 * (|s.im| + 2) ^ 2)).trans_eq (by ring)
  have hxi : ‖logDeriv riemannXi s‖ ≤ 4 + 2 * (|s.im| + 2) ^ 2 := by
    rw [xi_hadamard_logDeriv haway]
    exact (norm_add_le _ _).trans (add_le_add norm_logDeriv_xi_zero_le hzeroSum)
  have hpole : ‖1 / (s - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    apply (div_le_one (by
      have h := Complex.abs_re_le_norm (s - 1)
      norm_num [hs] at h
      linarith)).mpr
    have h := Complex.abs_re_le_norm (s - 1)
    norm_num [hs] at h
    linarith
  have hg := HorizontalEstimate.norm_digamma_le_explicit (z := s / 2 + 1)
    (by norm_num [hs]) (by norm_num [hs])
  have hγ : ‖digamma (s / 2 + 1)‖ ≤ 8 * (|s.im| + 1) + 13 := by
    have hlog := Real.log_le_sub_one_of_pos (show 0 < |(s / 2 + 1).im| + 2 by positivity)
    have him : |(s / 2 + 1).im| ≤ |s.im| := by simp [abs_div]
    linarith
  have hpi : ‖(Real.log Real.pi : ℂ)‖ ≤ 3 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
    linarith [Real.log_le_sub_one_of_pos Real.pi_pos, Real.pi_lt_four]
  have he := logDeriv_xi_eq_zeta (by linarith) hs1 (zeta_ne_zero_left hs)
  have hz : logDeriv riemannZeta s = logDeriv riemannXi s - 1 / (s - 1) +
      (Real.log Real.pi : ℂ) / 2 - (1 / 2 : ℂ) * digamma (s / 2 + 1) := by
    linear_combination -he
  rw [hz]
  have h :
      ‖logDeriv riemannXi s - 1 / (s - 1) + (Real.log Real.pi : ℂ) / 2 -
          (1 / 2 : ℂ) * digamma (s / 2 + 1)‖ ≤
        ‖logDeriv riemannXi s‖ + ‖1 / (s - 1)‖ + ‖(Real.log Real.pi : ℂ) / 2‖ +
          ‖(1 / 2 : ℂ) * digamma (s / 2 + 1)‖ :=
    (norm_sub_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
  simp only [norm_div, norm_mul] at h
  norm_num only [Complex.norm_ofNat, norm_one] at h
  rw [norm_div, norm_one] at hpole
  exact h.trans (by nlinarith [abs_nonneg s.im, sq_nonneg s.im])

theorem norm_zetaCenteredIntegrand_left {t : ℝ} (ht : 9 ≤ t) {s : ℂ}
    (hs : s.re = -1 / 2) :
    ‖zetaCenteredIntegrand t s‖ ≤ 60 * (|s.im| + 2) ^ 2 := by
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  rw [zetaCenteredIntegrand_eq hs0, norm_mul, norm_neg]
  have hk := LeftVertical.norm_real_centered_kernel_left_le ht hs
  have hk3 : ‖((t : ℂ) ^ s - (2.5 : ℂ) ^ s) / s‖ ≤ 3 := by
    apply hk.trans
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [abs_nonneg s.im]
  exact (mul_le_mul (norm_logDeriv_zeta_left hs) hk3 (norm_nonneg _)
    (by positivity)).trans_eq (by ring)

end LiuWang.Proof.PrincipalPsi.Quantitative
