import LiuWang.Proof.ZeroRegionFamily.RealZeros
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LevelCorrectionLogDerivativeBound
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.PrincipalLevelCorrectionLogDerivativeBound
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LogDerivativePositivity
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.ComplexZeroOptimization
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.QuadraticConjugateZeroIndex
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.ConjugatePairKernel
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.QuadraticLowHeightOptimization

/-! # 显式复高度正核：保留模数、Gamma、极点及Euler修正的实际费用 -/

set_option autoImplicit false
noncomputable section

open Complex
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ChebyshevBound.HighHeight

namespace LiuWang.Proof.ZeroRegionFamily

theorem gamma_re_le {q : ℕ} (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hlo : 1 < s.re) (hhi : s.re ≤ 2) :
    (logDeriv chi.gammaFactor s).re ≤ Real.log (|s.im|+2)/2 + 1 := by
  have haux {z : ℂ} (hzlo : 0 < z.re) (hzhi : z.re ≤ 1)
      (hzheight : |z.im| ≤ |s.im|) :
      (Complex.digamma z).re ≤ Real.log (|s.im|+2)+2 := by
    have hd := digamma_re_le_log_add (z := z+1)
      (by simp; linarith) (by simp; linarith)
    have hshift := Complex.digamma_apply_add_one z (by
      intro n hn
      have hr := congrArg Complex.re hn
      simp at hr
      have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      linarith)
    have hinv : 0 ≤ (z⁻¹).re := by
      rw [Complex.inv_re]
      exact div_nonneg hzlo.le (Complex.normSq_nonneg _)
    have hl : Real.log (|(z+1).im|+2) ≤ Real.log (|s.im|+2) :=
      Real.log_le_log (by positivity) (by simpa using add_le_add_right hzheight 2)
    rw [hshift, Complex.add_re] at hd
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  rcases chi.even_or_odd with he | ho
  · rw [logDeriv_gammaFactor_of_even he (by linarith)]
    have hd := haux (z := s/2) (by simp; linarith) (by simp; linarith)
      (by simp [abs_div])
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.neg_re, Complex.ofReal_re,
      Complex.mul_re, Complex.one_re, Complex.one_im, Complex.div_ofNat_im,
      zero_div, zero_mul, sub_zero]
    linarith [log_pi_ge_one]
  · rw [logDeriv_gammaFactor_of_odd ho (by linarith)]
    have hd := digamma_re_le_log_add (z := (s+1)/2)
      (by simp; linarith) (by simp; linarith)
    have hl : Real.log (|((s+1)/2).im|+2) ≤ Real.log (|s.im|+2) := by
      apply Real.log_le_log (by positivity)
      simp only [Complex.div_ofNat_im, Complex.add_im, Complex.one_im, add_zero,
        abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith [abs_nonneg s.im]
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.neg_re, Complex.ofReal_re,
      Complex.mul_re, Complex.one_re, Complex.one_im, Complex.div_ofNat_im,
      zero_div, zero_mul, sub_zero]
    linarith [Real.one_half_lt_eulerMascheroniConstant, log_pi_ge_one]

theorem primitive_kernel_identity {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hchi : chi ≠ 1) (hprim : chi.IsPrimitive)
    {s : ℂ} (hs : 1 < s.re) :
    -(logDeriv chi.LFunction s).re +
      (∑' p : SymmetricCompletedZeroIndex chi,
        (1/(s-Complex.Hadamard.divisorZeroIndex₀_val p)).re) =
      Real.log q/2+(logDeriv chi.gammaFactor s).re := by
  obtain ⟨Bc, hc, _⟩ := existsUnique_symmetricCompletedLFunction_hadamardConstant hchi hprim
  obtain ⟨Bi, hi, _⟩ := existsUnique_symmetricCompletedLFunction_hadamardConstant
    (BombieriVinogradov.DirichletCharacter.inv_ne_one_of_ne_one hchi)
    (BombieriVinogradov.DirichletCharacter.IsPrimitive.inv hprim)
  linarith [neg_re_logDeriv_LFunction_eq_modulus_gamma_sub_zeroKernel hchi hprim hc hi hs]

theorem zero_kernel_nonneg {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hchi : chi ≠ 1) (hprim : chi.IsPrimitive)
    {s : ℂ} (hs : 1 < s.re) (p : SymmetricCompletedZeroIndex chi) :
    0 ≤ (1/(s-Complex.Hadamard.divisorZeroIndex₀_val p)).re := by
  rw [one_div, Complex.inv_re]
  apply div_nonneg _ (Complex.normSq_nonneg _)
  have hp := (symmetricCompletedLFunction_divisorZeroIndex₀_re_mem_Ioo hchi hprim p).2
  simp only [Complex.sub_re]
  linarith

theorem primitive_selected_kernel_le {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hchi : chi ≠ 1) (hprim : chi.IsPrimitive)
    (p : SymmetricCompletedZeroIndex chi)
    {s : ℂ} (hlo : 1 < s.re) (hhi : s.re ≤ 2) :
    -(logDeriv chi.LFunction s).re +
      (1/(s-Complex.Hadamard.divisorZeroIndex₀_val p)).re ≤
      Real.log q/2 + Real.log (|s.im|+2)/2 + 1 := by
  have hsum := summable_symmetricCompletedLFunction_zeroKernel_re hchi hprim hlo
  have hh := hsum.le_tsum p (fun r _ => zero_kernel_nonneg hchi hprim hlo r)
  have hid := primitive_kernel_identity hchi hprim hlo
  linarith [gamma_re_le chi hlo hhi]

theorem primitive_without_zeros_le {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hchi : chi ≠ 1) (hprim : chi.IsPrimitive)
    {s : ℂ} (hlo : 1 < s.re) (hhi : s.re ≤ 2) :
    -(logDeriv chi.LFunction s).re ≤ Real.log q/2 + Real.log (|s.im|+2)/2 + 1 := by
  have hz : 0 ≤ ∑' p : SymmetricCompletedZeroIndex chi,
      (1/(s-Complex.Hadamard.divisorZeroIndex₀_val p)).re :=
    tsum_nonneg (zero_kernel_nonneg hchi hprim hlo)
  linarith [primitive_kernel_identity hchi hprim hlo, gamma_re_le chi hlo hhi]

theorem nonprincipal_without_zeros_le {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hchi : chi ≠ 1)
    {s : ℂ} (hlo : 1 < s.re) (hhi : s.re ≤ 2) :
    -(logDeriv chi.LFunction s).re ≤ 3*Real.log q/2 + Real.log (|s.im|+2)/2 + 1 := by
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hpr := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hchi
  have hp := primitive_without_zeros_le hpr chi.primitiveCharacter_isPrimitive hlo hhi
  have hc := norm_logDeriv_LFunction_sub_primitive_le_log chi hchi hlo.le
  have hr := (neg_le_abs (logDeriv chi.LFunction s-logDeriv chi.primitiveCharacter.LFunction s).re).trans
    (Complex.abs_re_le_norm _)
  simp only [Complex.sub_re] at hr
  have hlog : Real.log chi.conductor ≤ Real.log q :=
    Real.log_le_log (by exact_mod_cast NeZero.pos chi.conductor)
    (by exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi)
  linarith

end LiuWang.Proof.ZeroRegionFamily
