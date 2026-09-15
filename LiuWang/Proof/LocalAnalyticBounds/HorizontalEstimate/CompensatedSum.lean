import LiuWang.Proof.LocalAnalyticBounds.HeightHelpers.LocalHorizontalBounds
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroReciprocalDifferenceSummable
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.LogDerivativeDifference
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.LFunctionNonvanishing

/-!
# 用正参考核控制绝对可和的补偿零点差

只对 `1/(s-rho) - 1/(2+iH-rho)` 求范数和。保留原完成函数的
重数索引，由真实 Hadamard 生产者保证可和性；没有拆分裸倒数级数。
-/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate

theorem norm_reciprocal_difference_le_reference_kernel
    {s rho : Complex} {H B d : Real}
    (hB : 0 < B) (hsep : B⁻¹ ≤ |rho.im - H|)
    (him : s.im = H) (hd0 : 0 ≤ d) (hlo : 2 - d ≤ s.re) (hhi : s.re ≤ 2)
    (hrho : rho.re ∈ Set.Icc 0 1) :
    ‖1 / (s - rho) - 1 / (referencePoint H - rho)‖ ≤
      (d + d ^ 2 * B) * (1 / (referencePoint H - rho)).re := by
  let w := referencePoint H
  have hwre : w.re = 2 := by simp [w, referencePoint]
  have hwim : w.im = H := by simp [w, referencePoint]
  have hspos : 0 < ‖s - rho‖ := by
    have h := Complex.abs_im_le_norm (s - rho)
    simp only [Complex.sub_im, him] at h
    rw [abs_sub_comm] at h
    exact (inv_pos.mpr hB).trans_le (hsep.trans h)
  have hwpos : 0 < ‖w - rho‖ := by
    have h := Complex.re_le_norm (w - rho)
    simp only [Complex.sub_re, hwre] at h
    linarith [hrho.2]
  have hsn : s - rho ≠ 0 := norm_pos_iff.mp hspos
  have hwn : w - rho ≠ 0 := norm_pos_iff.mp hwpos
  have hinv := norm_inv_sub_le_of_separated_height hB hsep him
  rw [norm_inv, inv_le_iff_one_le_mul₀ hspos] at hinv
  have hws : w - s = ((2 - s.re : Real) : Complex) := by
    apply Complex.ext <;> simp [hwre, hwim, him]
  have hd : ‖w - s‖ ≤ d := by
    rw [hws, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have htri : ‖w - rho‖ ≤ ‖s - rho‖ + d := by
    calc
      ‖w - rho‖ = ‖(s - rho) + (w - s)‖ := by congr 1; ring
      _ ≤ ‖s - rho‖ + ‖w - s‖ := norm_add_le _ _
      _ ≤ ‖s - rho‖ + d := by linarith
  have hnum : ‖w - s‖ * ‖w - rho‖ ≤
      (d + d ^ 2 * B) * ‖s - rho‖ := by
    have h1 := mul_le_mul_of_nonneg_right hd (norm_nonneg (w - rho))
    have h2 := mul_le_mul_of_nonneg_left htri hd0
    have h3 := mul_le_mul_of_nonneg_left hinv (sq_nonneg d)
    nlinarith
  have hkernel :
      (1 / (w - rho)).re = (2 - rho.re) / ‖w - rho‖ ^ 2 := by
    rw [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq]
    simp only [Complex.sub_re, hwre]
  have hid : 1 / (s - rho) - 1 / (w - rho) =
      (w - s) / ((s - rho) * (w - rho)) := by
    field_simp
    ring
  change ‖1 / (s - rho) - 1 / (w - rho)‖ ≤
    (d + d ^ 2 * B) * (1 / (w - rho)).re
  rw [hid, norm_div, norm_mul, hkernel]
  have hK : 0 ≤ d + d ^ 2 * B := by positivity
  calc
    ‖w - s‖ / (‖s - rho‖ * ‖w - rho‖) ≤
        (d + d ^ 2 * B) / ‖w - rho‖ ^ 2 := by
      apply (div_le_div_iff₀ (mul_pos hspos hwpos) (sq_pos_of_pos hwpos)).mpr
      nlinarith [mul_le_mul_of_nonneg_right hnum hwpos.le]
    _ ≤ (d + d ^ 2 * B) * ((2 - rho.re) / ‖w - rho‖ ^ 2) := by
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      nlinarith [hrho.2]

theorem reference_kernel_sum_le_explicit
    {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) (H : Real) :
    (∑' p : CompletedZeroIndex chi, (1 / (referencePoint H - completedZeroValue p)).re)
      ≤ Real.log q / 2 + Real.log (|H| + 2) / 2 + 7 := by
  obtain ⟨Bc, hc, _⟩ := existsUnique_symmetricCompletedLFunction_hadamardConstant
    hchi hPrimitive
  obtain ⟨Bi, hi, _⟩ := existsUnique_symmetricCompletedLFunction_hadamardConstant
    (BombieriVinogradov.DirichletCharacter.inv_ne_one_of_ne_one hchi)
    (BombieriVinogradov.DirichletCharacter.IsPrimitive.inv hPrimitive)
  have he := neg_re_logDeriv_LFunction_eq_modulus_gamma_sub_zeroKernel
    hchi hPrimitive hc hi (s := referencePoint H) (by norm_num [referencePoint])
  have hn := norm_neg_logDeriv_LFunction_le_zeta_re chi
    (s := referencePoint H) (by norm_num [referencePoint])
  have hl : (logDeriv chi.LFunction (referencePoint H)).re ≤ 6 := by
    apply (Complex.re_le_norm _).trans
    apply le_trans _ norm_neg_logDeriv_zeta_two_le_six
    simpa [logDeriv_apply, referencePoint, norm_div, norm_neg] using hn
  have hg := logDeriv_gammaFactor_re_le_on_two chi
    (s := referencePoint H) (by simp [referencePoint])
  rw [show (referencePoint H).im = H by simp [referencePoint]] at hg
  change -(logDeriv chi.LFunction (referencePoint H)).re =
    Real.log q / 2 + (logDeriv chi.gammaFactor (referencePoint H)).re -
      ∑' p : CompletedZeroIndex chi,
        (1 / (referencePoint H - completedZeroValue p)).re at he
  linarith

theorem norm_tsum_reciprocal_difference_le
    {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {H B d : Real} (hB : 0 < B)
    (hsep : ∀ p : CompletedZeroIndex chi, B⁻¹ ≤ |(completedZeroValue p).im - H|)
    {s : Complex} (him : s.im = H)
    (hd0 : 0 ≤ d) (hlo : 2 - d ≤ s.re) (hhi : s.re ≤ 2) :
    ‖∑' p : CompletedZeroIndex chi,
      (1 / (s - completedZeroValue p) - 1 / (referencePoint H - completedZeroValue p))‖ ≤
      (d + d ^ 2 * B) *
        (Real.log q / 2 + Real.log (|H| + 2) / 2 + 7) := by
  have hsaway : ∀ p : CompletedZeroIndex chi, s ≠ completedZeroValue p := by
    intro p hp
    have h := hsep p
    rw [← hp, him, sub_self, abs_zero] at h
    exact (not_le_of_gt (inv_pos.mpr hB)) h
  have hwaway : ∀ p : CompletedZeroIndex chi,
      referencePoint H ≠ completedZeroValue p := by
    intro p hp
    have h := (completedZeroValue_re_mem_Ioo hchi hPrimitive p).2
    rw [← hp] at h
    norm_num [referencePoint] at h
  have hsum := summable_completedZero_reciprocalDifference hchi hPrimitive
    hsaway hwaway
  have hk := summable_symmetricCompletedLFunction_zeroKernel_re hchi hPrimitive
    (s := referencePoint H) (by norm_num [referencePoint])
  have hmajor := hk.mul_left (d + d ^ 2 * B)
  calc
    _ ≤ ∑' p : CompletedZeroIndex chi,
        ‖1 / (s - completedZeroValue p) - 1 / (referencePoint H - completedZeroValue p)‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' p : CompletedZeroIndex chi,
        (d + d ^ 2 * B) * (1 / (referencePoint H - completedZeroValue p)).re := by
      apply hsum.norm.tsum_le_tsum _ hmajor
      intro p
      exact norm_reciprocal_difference_le_reference_kernel hB (hsep p) him hd0 hlo hhi
        ⟨(completedZeroValue_re_mem_Ioo hchi hPrimitive p).1.le,
          (completedZeroValue_re_mem_Ioo hchi hPrimitive p).2.le⟩
    _ = (d + d ^ 2 * B) *
        ∑' p : CompletedZeroIndex chi,
          (1 / (referencePoint H - completedZeroValue p)).re := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (reference_kernel_sum_le_explicit hchi hPrimitive H) (by positivity)

end LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate
