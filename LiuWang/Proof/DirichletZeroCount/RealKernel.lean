import LiuWang.Proof.DirichletZeroCount.Transport
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.VonMangoldtLSeriesMonotone

/-!
# Explicit global counts from a moving real reference point

These are genuine unconditional count producers, but not the sharp
Riemann--von Mangoldt bounds in companion Theorems 5 and 6.
The parameterized version retains the gamma and Dirichlet-series budgets.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces
open LiuWang.Proof.ChebyshevBound.HighHeight
open LiuWang.Proof.LocalAnalyticBounds
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.DirichletZeroCount

theorem norm_zeta_real_logDeriv_le_one {s : ℝ} (hs : 2 ≤ s) :
    ‖-deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ)‖ ≤ 1 := by
  have hs1 : 1 < s := by linarith
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (s := (s : ℂ)) (by simpa using hs1)]
  calc
    _ ≤ vonMangoldtLSeriesNormSum s :=
      norm_tsum_le_tsum_norm
        (ArithmeticFunction.LSeriesSummable_vonMangoldt
          (s := (s : ℂ)) (by simpa using hs1)).norm
    _ ≤ vonMangoldtLSeriesNormSum 2 :=
      vonMangoldtLSeriesNormSum_antitone (by norm_num) hs
    _ ≤ 1 := by
      rw [vonMangoldtLSeriesNormSum_eq_neg_logDeriv_re (by norm_num)]
      have h := zeta_real_le_pole (σ := 2) (by norm_num) le_rfl
      norm_num at h ⊢
      exact h

theorem gamma_real_bound {q : ℕ} (chi : Character q) {s : ℝ} (hs : 3 ≤ s) :
    (logDeriv chi.gammaFactor (s : ℂ)).re ≤ Real.log s / 2 + 1 / 4 := by
  have hs0 : 0 < (s : ℂ).re := by simp; linarith
  have hgamma := Real.one_half_lt_eulerMascheroniConstant
  have hpi := log_pi_ge_one
  rcases chi.even_or_odd with he | ho
  · have hd := digamma_real_le_log (x := s / 2) (by linarith)
    push_cast at hd
    have hl := Real.log_le_log (by linarith : 0 < s / 2 + 1)
      (by linarith : s / 2 + 1 ≤ s)
    rw [logDeriv_gammaFactor_of_even he hs0]
    rw [show (s : ℂ) / 2 = ((s / 2 : ℝ) : ℂ) by push_cast; rfl]
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.neg_re, Complex.ofReal_re,
      Complex.mul_re]
    norm_num
    linarith
  · have hd := digamma_real_le_log (x := (s + 1) / 2) (by linarith)
    push_cast at hd
    have hl := Real.log_le_log (by linarith : 0 < (s + 1) / 2 + 1)
      (by linarith : (s + 1) / 2 + 1 ≤ s)
    rw [logDeriv_gammaFactor_of_odd ho hs0]
    rw [show ((s : ℂ) + 1) / 2 = (((s + 1) / 2 : ℝ) : ℂ) by push_cast; rfl]
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.neg_re, Complex.ofReal_re,
      Complex.mul_re]
    norm_num
    linarith

theorem real_reference_mass_le {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) {s : ℝ} (hs : 3 ≤ s) :
    (∑' p : CompletedZeroIndex chi, (1 / ((s : ℂ) - completedZeroValue p)).re) ≤
      Real.log q / 2 + Real.log s / 2 + 5 / 4 := by
  obtain ⟨B, hB, _⟩ := existsUnique_symmetricCompletedLFunction_hadamardConstant hchi hprim
  obtain ⟨Bi, hBi, _⟩ := existsUnique_symmetricCompletedLFunction_hadamardConstant
    (BombieriVinogradov.DirichletCharacter.inv_ne_one_of_ne_one hchi)
    (BombieriVinogradov.DirichletCharacter.IsPrimitive.inv hprim)
  have he := neg_re_logDeriv_LFunction_eq_modulus_gamma_sub_zeroKernel
    hchi hprim hB hBi (s := (s : ℂ)) (by simp; linarith)
  have hn := (norm_neg_logDeriv_LFunction_le_zeta_re chi
    (s := (s : ℂ)) (by simp; linarith)).trans
      (norm_zeta_real_logDeriv_le_one (by linarith : 2 ≤ s))
  have hr : (logDeriv chi.LFunction (s : ℂ)).re ≤ 1 := by
    apply (Complex.re_le_norm _).trans
    simpa [logDeriv_apply, norm_div, norm_neg] using hn
  have hg := gamma_real_bound chi hs
  change -(logDeriv chi.LFunction (s : ℂ)).re =
    Real.log q / 2 + (logDeriv chi.gammaFactor (s : ℂ)).re -
      ∑' p : CompletedZeroIndex chi, (1 / ((s : ℂ) - completedZeroValue p)).re at he
  linarith

theorem real_kernel_lower {s y : ℝ} {rho : ℂ}
    (hy : 0 ≤ y) (hs : y + 1 ≤ s)
    (hr : rho.re ∈ Set.Ioo 0 1) (ht : |rho.im| ≤ y) :
    1 / (s + y) ≤ (1 / ((s : ℂ) - rho)).re := by
  have hu : y ≤ s - rho.re := by linarith [hr.2]
  have hus : s - rho.re ≤ s := by linarith [hr.1]
  have hup : 0 < s - rho.re := by linarith [hr.2]
  have hsy : 0 < s + y := by linarith
  have ht2 : rho.im ^ 2 ≤ y ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hy).mpr ht
  have hden : 0 < (s - rho.re) ^ 2 + rho.im ^ 2 := by positivity
  have hprod : (s - rho.re) ^ 2 + rho.im ^ 2 ≤ (s - rho.re) * (s + y) := by
    have h1 := mul_le_mul_of_nonneg_left hus hup.le
    have h2 := mul_le_mul_of_nonneg_left hu hy
    nlinarith
  simp only [one_div, Complex.inv_re, Complex.normSq_apply, Complex.sub_re,
    Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_sub, neg_mul_neg]
  rw [← one_div]
  apply (div_le_div_iff₀ hsy (by simpa [pow_two] using hden)).mpr
  nlinarith

theorem count_primitive_real_parameter {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) (alpha : ℝ)
    {y s : ℝ} (hy : 0 ≤ y) (hs : 3 ≤ s) (hys : y + 1 ≤ s) :
    (count chi alpha y : ℝ) ≤
      (s + y) * (Real.log q / 2 + Real.log s / 2 + 5 / 4) := by
  let k : CompletedZeroIndex chi → ℝ :=
    fun p => (1 / ((s : ℂ) - completedZeroValue p)).re
  have hs1 : 1 < (s : ℂ).re := by simp; linarith
  have hsum := summable_symmetricCompletedLFunction_zeroKernel_re hchi hprim hs1
  have hn := symmetricCompletedLFunction_zeroKernel_re_nonneg hchi hprim hs1
  have hsy : 0 < s + y := by linarith
  rw [count_nonprincipal hchi]
  have hc : ((nonprincipalIndices chi alpha y).card : ℝ) / (s + y) ≤ ∑' p, k p := by
    calc
      _ = ∑ _p ∈ nonprincipalIndices chi alpha y, 1 / (s + y) := by simp [div_eq_mul_inv]
      _ ≤ ∑ p ∈ nonprincipalIndices chi alpha y, k p := by
        apply Finset.sum_le_sum
        intro p hp
        have hr := (mem_nonprincipalIndices.mp hp).1
        exact real_kernel_lower hy hys ⟨hr.1, hr.2.1⟩ hr.2.2
      _ ≤ _ := hsum.sum_le_tsum _ (fun p _ => hn p)
  have hm := real_reference_mass_le hchi hprim hs
  exact (div_le_iff₀ hsy).mp (hc.trans hm) |>.trans_eq (mul_comm _ _)

theorem count_primitive_linear {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) (alpha : ℝ)
    {y : ℝ} (hy : 0 ≤ y) :
    (count chi alpha y : ℝ) ≤
      (2 * y + 3) * (Real.log q / 2 + Real.log (y + 3) / 2 + 5 / 4) := by
  convert count_primitive_real_parameter hchi hprim alpha hy
    (s := y + 3) (by linarith) (by linarith) using 1
  ring

theorem count_conductor_linear {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (alpha : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    (count chi alpha y : ℝ) ≤
      (2 * y + 3) * (Real.log chi.conductor / 2 + Real.log (y + 3) / 2 + 5 / 4) := by
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  rw [count_eq_primitive chi hchi]
  exact count_primitive_linear
    (BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hchi)
    chi.primitiveCharacter_isPrimitive alpha hy

end LiuWang.Proof.DirichletZeroCount
