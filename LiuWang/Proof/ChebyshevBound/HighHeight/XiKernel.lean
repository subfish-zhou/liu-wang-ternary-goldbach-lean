import Robin1984.NicolasLandau.XiLogDerivative
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.RiemannXiZeroSumPositivity
import Mathlib.Tactic

/-!
# 实际 ξ 除子零点核

索引保留解析重数。由 Hadamard 恒等式隔离任意一个实际零点；
在 s=1 使用函数方程，给出全部零点的正核总量恒等式。
-/

set_option autoImplicit false
noncomputable section

open Complex Set
open scoped BigOperators
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.ChebyshevBound.HighHeight

def xiTerm (s : ℂ) (p : RiemannXiDivisorZeroIndex) : ℂ :=
  1 / (s - riemannXiDivisorZeroValue p) + 1 / riemannXiDivisorZeroValue p

theorem xiTerm_summable {s : ℂ} (hs : 1 ≤ s.re) :
    Summable (xiTerm s) := by
  apply summable_riemannXi_logDerivTerms_divisorZeroIndex₀
  intro p hp
  change s = riemannXiDivisorZeroValue p at hp
  have h := (riemannXiDivisorZeroValue_re_mem_Ioo p).2
  rw [← hp] at h
  linarith

theorem xiTerm_re_nonneg {s : ℂ} (hs : 1 ≤ s.re) (p : RiemannXiDivisorZeroIndex) :
    0 ≤ (xiTerm s p).re := by
  obtain ⟨hr0, hr1⟩ := riemannXiDivisorZeroValue_re_mem_Ioo p
  simp only [xiTerm, Complex.add_re, one_div, Complex.inv_re, Complex.sub_re]
  exact add_nonneg (div_nonneg (by linarith) (Complex.normSq_nonneg _))
    (div_nonneg hr0.le (Complex.normSq_nonneg _))

theorem xiTerm_re_le_sum {s : ℂ} (hs : 1 ≤ s.re) (p : RiemannXiDivisorZeroIndex) :
    (xiTerm s p).re ≤ (∑' q, xiTerm s q).re := by
  rw [Complex.re_tsum (xiTerm_summable hs)]
  exact (Complex.reCLM.summable (xiTerm_summable hs)).le_tsum p (fun q _ => xiTerm_re_nonneg hs q)

theorem zeta_selected_zero_le {s : ℂ} (hs : 1 < s.re) (p : RiemannXiDivisorZeroIndex) :
    (-deriv riemannZeta s / riemannZeta s).re ≤
      -(logDeriv riemannXi 0).re + (1 / (s - 1)).re -
        Real.log Real.pi / 2 + (Complex.digamma (s / 2 + 1)).re / 2 -
        (1 / (s - riemannXiDivisorZeroValue p)).re := by
  have h := xiTerm_re_le_sum hs.le p
  have hp : 0 ≤ (1 / riemannXiDivisorZeroValue p).re := by
    rw [one_div, Complex.inv_re]
    exact div_nonneg (riemannXiDivisorZeroValue_re_mem_Ioo p).1.le
      (Complex.normSq_nonneg _)
  rw [Robin1984.neg_riemannZeta_logDeriv_eq_xiDivisor_tsum hs]
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re] at h ⊢
  norm_num only [Complex.mul_re, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_div, zero_mul, sub_zero] at *
  change (1 / (s - riemannXiDivisorZeroValue p)).re +
    (1 / riemannXiDivisorZeroValue p).re ≤ _ at h
  change _ ≤ -(logDeriv riemannXi 0).re + _ - _ + _ - _
  dsimp only [xiTerm] at h
  linarith

theorem zeta_without_zeros_le {s : ℂ} (hs : 1 < s.re) :
    (-deriv riemannZeta s / riemannZeta s).re ≤
      -(logDeriv riemannXi 0).re + (1 / (s - 1)).re -
        Real.log Real.pi / 2 + (Complex.digamma (s / 2 + 1)).re / 2 := by
  have h := riemannXi_logDerivTsum_re_nonneg hs
  rw [Robin1984.neg_riemannZeta_logDeriv_eq_xiDivisor_tsum hs]
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re]
  norm_num only [Complex.mul_re, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_div, zero_mul, sub_zero]
  linarith

theorem xiTerm_sum_one :
    (∑' p, xiTerm 1 p) =
      (Real.eulerMascheroniConstant : ℂ) + 2 - (Real.log (4 * Real.pi) : ℂ) := by
  obtain ⟨P, hP⟩ := riemannXi_hadamard_factorization_no_monomial
  have hAway : ∀ p : RiemannXiDivisorZeroIndex, (1 : ℂ) ≠ riemannXiDivisorZeroValue p := by
    intro p hp
    have h := (riemannXiDivisorZeroValue_re_mem_Ioo p).2
    rw [← hp] at h
    norm_num at h
  have h := logDeriv_riemannXi_eq_polynomial_derivative_add_tsum hP.2 hAway
  rw [Robin1984.riemannXi_hadamardPolynomialDerivative_eval_eq_logDeriv_zero hP.1 hP.2,
    Robin1984.logDeriv_riemannXi_one_eq_neg_zero] at h
  calc
    _ = (-2 : ℂ) * logDeriv riemannXi 0 := by
      dsimp only [xiTerm]
      linear_combination -h
    _ = _ := neg_two_mul_logDeriv_riemannXi_zero_eq

theorem xi_arch_constant :
    -(logDeriv riemannXi 0).re - Real.log Real.pi / 2 =
      1 + Real.eulerMascheroniConstant / 2 - Real.log 2 - Real.log Real.pi := by
  have h := congrArg Complex.re neg_two_mul_logDeriv_riemannXi_zero_eq
  norm_num [Complex.mul_re, Complex.neg_re,
    Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
    Complex.sub_re, zero_mul, sub_zero] at h
  rw [Real.log_mul (by norm_num) Real.pi_ne_zero, Real.log_four_eq] at h
  linarith

end LiuWang.Proof.ChebyshevBound.HighHeight
