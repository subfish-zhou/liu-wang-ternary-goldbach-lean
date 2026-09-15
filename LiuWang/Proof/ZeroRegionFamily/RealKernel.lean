import LiuWang.Proof.ChebyshevBound.HighHeight.Gamma
import LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate.CompensatedSum
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorLogDerivative
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LFunctionLogDerivativeNormBound
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.PairSubtypeTsum
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.ZeroKernelSubset

/-! # 实轴正核的显式付款：无未知常数、保真实解析重数 -/

set_option autoImplicit false
noncomputable section

open Complex
open scoped ComplexOrder
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ChebyshevBound.HighHeight

namespace LiuWang.Proof.ZeroRegionFamily

theorem norm_zeta_real_le_pole {sigma : ℝ} (hlo : 1 < sigma) (hhi : sigma ≤ 2) :
    ‖-deriv riemannZeta (sigma : ℂ) / riemannZeta (sigma : ℂ)‖ ≤ 1 / (sigma - 1) := by
  have hn : 0 ≤ -deriv riemannZeta (sigma : ℂ) / riemannZeta (sigma : ℂ) := by
    rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
      (by simpa using hlo)]
    apply tsum_nonneg
    intro n
    apply LSeries.term_nonneg
    exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg
  rw [← Complex.re_eq_norm.mpr hn]
  exact zeta_real_le_pole hlo hhi

theorem gamma_real_nonpos {q : ℕ} (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hlo : 1 < sigma) (hhi : sigma ≤ 2) :
    (logDeriv chi.gammaFactor (sigma : ℂ)).re ≤ 0 := by
  have hp (z : ℂ) (hz : 0 < z.re) : ∀ n : ℕ, z ≠ -(n : ℂ) := by
    intro n hn
    have hr := congrArg Complex.re hn
    simp at hr
    have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    linarith
  rcases chi.even_or_odd with he | ho
  · rw [logDeriv_gammaFactor_of_even he (by simpa using (show 0 < sigma by linarith))]
    have hd := digamma_real_le_one_sub_gamma (x := sigma / 2 + 1)
      (by linarith) (by linarith)
    have hr := Complex.digamma_apply_add_one ((sigma / 2 : ℝ) : ℂ)
      (hp _ (by simp; linarith))
    have hcast : ((sigma : ℂ) / 2 + 1) = ((sigma / 2 + 1 : ℝ) : ℂ) := by push_cast; rfl
    have hcast' : ((sigma / 2 : ℝ) : ℂ) = (sigma : ℂ) / 2 := by push_cast; rfl
    rw [hcast'] at hr
    rw [hcast] at hr
    have hre := congrArg Complex.re hr
    have hinv : 0 ≤ (((sigma : ℂ) / 2)⁻¹).re := by
      rw [Complex.inv_re]
      apply div_nonneg _ (Complex.normSq_nonneg _)
      simp
      linarith
    simp only [Complex.add_re] at hre
    have hgamma := Real.one_half_lt_eulerMascheroniConstant
    have hlog := log_pi_ge_one
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.neg_re, Complex.ofReal_re,
      Complex.mul_re, Complex.one_re, Complex.one_im, Complex.div_ofNat_im,
      zero_div, zero_mul, sub_zero]
    linarith
  · rw [logDeriv_gammaFactor_of_odd ho (by simpa using (show 0 < sigma by linarith))]
    have hd := digamma_real_le_one_sub_gamma (x := (sigma + 1) / 2)
      (by linarith) (by linarith)
    have hcast : ((sigma : ℂ) + 1) / 2 = (((sigma + 1) / 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [hcast]
    have hgamma := Real.one_half_lt_eulerMascheroniConstant
    have hlog := log_pi_ge_one
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.neg_re, Complex.ofReal_re,
      Complex.mul_re, Complex.one_re, Complex.one_im, Complex.div_ofNat_im,
      zero_div, zero_mul, sub_zero]
    linarith

theorem real_zero_kernel_sum_le {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hchi : chi ≠ 1) (hprim : chi.IsPrimitive)
    {sigma : ℝ} (hlo : 1 < sigma) (hhi : sigma ≤ 2) :
    (∑' p : SymmetricCompletedZeroIndex chi,
      (1 / ((sigma : ℂ) - Complex.Hadamard.divisorZeroIndex₀_val p)).re) ≤
        1 / (sigma - 1) + Real.log q / 2 := by
  obtain ⟨Bc, hc, _⟩ := existsUnique_symmetricCompletedLFunction_hadamardConstant hchi hprim
  obtain ⟨Bi, hi, _⟩ := existsUnique_symmetricCompletedLFunction_hadamardConstant
    (BombieriVinogradov.DirichletCharacter.inv_ne_one_of_ne_one hchi)
    (BombieriVinogradov.DirichletCharacter.IsPrimitive.inv hprim)
  have hid := neg_re_logDeriv_LFunction_eq_modulus_gamma_sub_zeroKernel hchi hprim hc hi
    (s := (sigma : ℂ)) (by simpa using hlo)
  have hn := norm_neg_logDeriv_LFunction_le_zeta_re chi (s := (sigma : ℂ)) (by simpa using hlo)
  have hz := norm_zeta_real_le_pole hlo hhi
  have hr := Complex.re_le_norm (logDeriv chi.LFunction (sigma : ℂ))
  have hg := gamma_real_nonpos chi hlo hhi
  have hn' : ‖logDeriv chi.LFunction (sigma : ℂ)‖ ≤ 1 / (sigma - 1) := by
    apply le_trans _ hz
    simpa [logDeriv_apply, norm_div, norm_neg] using hn
  linarith

theorem two_real_kernel_le {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hchi : chi ≠ 1) (hprim : chi.IsPrimitive)
    (p r : SymmetricCompletedZeroIndex chi) (hne : p ≠ r)
    {sigma : ℝ} (hlo : 1 < sigma) (hhi : sigma ≤ 2) :
    (1 / ((sigma : ℂ) - Complex.Hadamard.divisorZeroIndex₀_val p)).re +
      (1 / ((sigma : ℂ) - Complex.Hadamard.divisorZeroIndex₀_val r)).re ≤
        1 / (sigma - 1) + Real.log q / 2 := by
  classical
  apply le_trans _ (real_zero_kernel_sum_le hchi hprim hlo hhi)
  have hs := summable_symmetricCompletedLFunction_zeroKernel_re hchi hprim
    (s := (sigma : ℂ)) (by simpa using hlo)
  have hh := hs.sum_le_tsum ({p, r} : Finset (SymmetricCompletedZeroIndex chi)) (fun t _ => ?_)
  · simpa [hne] using hh
  · rw [one_div, Complex.inv_re]
    apply div_nonneg _ (Complex.normSq_nonneg _)
    have ht := (symmetricCompletedLFunction_divisorZeroIndex₀_re_mem_Ioo hchi hprim t).2
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith

end LiuWang.Proof.ZeroRegionFamily
