import LiuWang.Proof.Interfaces.Main
import BombieriVinogradov.Helpers.DirichletCharacter.PrimitiveInverseFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LFunctionLogDerivativeRealZeroSum
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LFunctionLogDerivativeRightHalfPlaneBound

/-!
# A multiplicity-counted closed local zero window

This derives a local count directly from the summable real zero kernel,
without any global zero-count estimate. The coefficient `5 / 2` is explicit;
the archimedean and reference-zeta terms remain visible. In particular this
is not yet the decimal estimate in companion (4.3).
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open LiuWang.Proof.Interfaces
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.LocalAnalyticBounds

def referencePoint (T : Real) : Complex := 2 + (T : Complex) * Complex.I

def closedZeroWindow {q : Nat} [NeZero q] (chi : Character q) (T : Real) :
    Set (CompletedZeroIndex chi) :=
  {p | |T - (completedZeroValue p).im| ≤ 1}

theorem two_fifths_le_reference_kernel {T : Real} {rho : Complex}
    (hrho : rho.re ∈ Set.Icc 0 1) (hgap : |T - rho.im| ≤ 1) :
    (2 : Real) / 5 ≤ (1 / (referencePoint T - rho)).re := by
  have hu1 : 1 ≤ 2 - rho.re := by linarith [hrho.2]
  have hu2 : 2 - rho.re ≤ 2 := by linarith [hrho.1]
  have hv : (T - rho.im) ^ 2 ≤ 1 := by
    have h : |T - rho.im| ≤ |(1 : Real)| := by simpa using hgap
    simpa using (sq_le_sq).mpr h
  have hden : 0 < (2 - rho.re) ^ 2 + (T - rho.im) ^ 2 := by
    nlinarith [sq_nonneg (T - rho.im)]
  have hquad : 2 * ((2 - rho.re) ^ 2 + (T - rho.im) ^ 2) ≤
      5 * (2 - rho.re) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu1) (sub_nonneg.mpr hu2)]
  rw [one_div, Complex.inv_re, Complex.normSq_apply]
  simp only [referencePoint, Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.sub_im, Complex.add_im]
  norm_num
  apply (le_div_iff₀ (by simpa [pow_two] using hden)).mpr
  nlinarith [hquad]

private theorem reference_kernel_summable {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) (T : Real) :
    Summable (fun p : CompletedZeroIndex chi =>
      (1 / (referencePoint T - completedZeroValue p)).re) := by
  exact summable_symmetricCompletedLFunction_zeroKernel_re hchi hPrimitive
    (by norm_num [referencePoint])

theorem finite_closedZeroWindow {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) (T : Real) :
    (closedZeroWindow chi T).Finite := by
  have he := (reference_kernel_summable hchi hPrimitive T).tendsto_cofinite_zero
    |>.eventually_lt_const (by norm_num : (0 : Real) < 2 / 5)
  have hf := Filter.eventually_cofinite.mp he
  apply hf.subset
  intro p hp
  exact not_lt_of_ge
    (two_fifths_le_reference_kernel
      ⟨(completedZeroValue_re_mem_Ioo hchi hPrimitive p).1.le,
        (completedZeroValue_re_mem_Ioo hchi hPrimitive p).2.le⟩ hp)

theorem ncard_closedZeroWindow_le_reference_kernel
    {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) (T : Real) :
    ((closedZeroWindow chi T).ncard : Real) ≤ (5 / 2 : Real) *
      ∑' p : CompletedZeroIndex chi,
        (1 / (referencePoint T - completedZeroValue p)).re := by
  have hf := finite_closedZeroWindow hchi hPrimitive T
  let k : CompletedZeroIndex chi → Real :=
    fun p => (1 / (referencePoint T - completedZeroValue p)).re
  have hk : ∀ p, 0 ≤ k p := fun p =>
    symmetricCompletedLFunction_zeroKernel_re_nonneg hchi hPrimitive
      (by norm_num [referencePoint]) p
  have hsum : ((closedZeroWindow chi T).ncard : Real) * (2 / 5) ≤
      ∑ p ∈ hf.toFinset, k p := by
    rw [Set.ncard_eq_toFinset_card _ hf]
    calc
      (hf.toFinset.card : Real) * (2 / 5) =
          ∑ _p ∈ hf.toFinset, (2 / 5 : Real) := by simp
      _ ≤ ∑ p ∈ hf.toFinset, k p := by
        apply Finset.sum_le_sum
        intro p hp
        exact two_fifths_le_reference_kernel
          ⟨(completedZeroValue_re_mem_Ioo hchi hPrimitive p).1.le,
            (completedZeroValue_re_mem_Ioo hchi hPrimitive p).2.le⟩
          (hf.mem_toFinset.mp hp)
  have hle : ∑ p ∈ hf.toFinset, k p ≤ ∑' p, k p :=
    (reference_kernel_summable hchi hPrimitive T).sum_le_tsum
      hf.toFinset (fun p _ => hk p)
  change ((closedZeroWindow chi T).ncard : Real) ≤ (5 / 2 : Real) * ∑' p, k p
  linarith

theorem ncard_closedZeroWindow_le_gamma_zeta
    {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) (T : Real) :
    ((closedZeroWindow chi T).ncard : Real) ≤ (5 / 2 : Real) *
      (Real.log q / 2 + (logDeriv chi.gammaFactor (referencePoint T)).re +
        ‖-deriv riemannZeta (2 : Complex) / riemannZeta (2 : Complex)‖) := by
  obtain ⟨B, hB, _⟩ :=
    existsUnique_symmetricCompletedLFunction_hadamardConstant hchi hPrimitive
  obtain ⟨Bi, hBi, _⟩ :=
    existsUnique_symmetricCompletedLFunction_hadamardConstant
      (BombieriVinogradov.DirichletCharacter.inv_ne_one_of_ne_one hchi)
      (BombieriVinogradov.DirichletCharacter.IsPrimitive.inv hPrimitive)
  have hid := neg_re_logDeriv_LFunction_eq_modulus_gamma_sub_zeroKernel
    hchi hPrimitive hB hBi (s := referencePoint T) (by norm_num [referencePoint])
  have hnorm := norm_neg_logDeriv_LFunction_le_zeta_re chi
    (s := referencePoint T) (by norm_num [referencePoint])
  have hre : (logDeriv chi.LFunction (referencePoint T)).re ≤
      ‖-deriv riemannZeta (2 : Complex) / riemannZeta (2 : Complex)‖ := by
    apply (Complex.re_le_norm _).trans
    simpa [logDeriv_apply, referencePoint, norm_div, norm_neg] using hnorm
  have hkernel :
      (∑' p : CompletedZeroIndex chi, (1 / (referencePoint T - completedZeroValue p)).re)
        ≤ Real.log q / 2 + (logDeriv chi.gammaFactor (referencePoint T)).re +
          ‖-deriv riemannZeta (2 : Complex) / riemannZeta (2 : Complex)‖ := by
    change -(logDeriv chi.LFunction (referencePoint T)).re =
      Real.log q / 2 + (logDeriv chi.gammaFactor (referencePoint T)).re -
        ∑' p : CompletedZeroIndex chi,
          (1 / (referencePoint T - completedZeroValue p)).re at hid
    linarith
  exact (ncard_closedZeroWindow_le_reference_kernel hchi hPrimitive T).trans
    (mul_le_mul_of_nonneg_left hkernel (by norm_num))

end LiuWang.Proof.LocalAnalyticBounds
