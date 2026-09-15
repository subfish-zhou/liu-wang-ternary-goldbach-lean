import LiuWang.Proof.LocalAnalyticBounds.LeftVertical.LowKernel

/-!
# 保重数的低实部零点有限和

有限性与粗计数来自实部二的正可求和参考核，不使用全局零点计数。
索引是原 `CompletedZeroIndex` 的子集，故重数没有丢失。
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open LiuWang.Proof.Interfaces
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.LocalAnalyticBounds.LeftVertical

def lowZeroWindow {q : Nat} [NeZero q] (chi : Character q) (U : Real) :
    Set (CompletedZeroIndex chi) :=
  {p | (completedZeroValue p).re ∈ Set.Ioo 0 (1 / 2 : Real) ∧
    |(completedZeroValue p).im| ≤ U}

theorem inv_height_sq_add_four_le_reference_kernel {U : Real} {rho : Complex}
    (hrho : rho.re ∈ Set.Icc 0 1) (him : |rho.im| ≤ U) :
    1 / (U ^ 2 + 4) ≤ (1 / (referencePoint 0 - rho)).re := by
  have hU : 0 ≤ U := (abs_nonneg _).trans him
  have hv : rho.im ^ 2 ≤ U ^ 2 := (sq_le_sq).mpr (by simpa [abs_of_nonneg hU] using him)
  have hden : 0 < (2 - rho.re) ^ 2 + rho.im ^ 2 := by
    nlinarith [hrho.2, sq_nonneg rho.im]
  have hupper : (2 - rho.re) ^ 2 + rho.im ^ 2 ≤ U ^ 2 + 4 := by
    nlinarith [hrho.1, hrho.2, sq_nonneg rho.re]
  rw [show (1 : Complex) / (referencePoint 0 - rho) = (referencePoint 0 - rho)⁻¹ by simp,
    Complex.inv_re, Complex.normSq_apply]
  norm_num [referencePoint]
  rw [← one_div (U ^ 2 + 4)]
  apply (div_le_div_iff₀ (by positivity : 0 < U ^ 2 + 4) (by nlinarith)).mpr
  nlinarith [mul_nonneg (show 0 ≤ 1 - rho.re by linarith [hrho.2])
    (show 0 ≤ U ^ 2 + 4 by positivity)]

theorem finite_lowZeroWindow {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) (U : Real) :
    (lowZeroWindow chi U).Finite := by
  have hs := summable_symmetricCompletedLFunction_zeroKernel_re hchi hPrimitive
    (s := referencePoint 0) (by norm_num [referencePoint])
  have he := hs.tendsto_cofinite_zero |>.eventually_lt_const
    (by positivity : (0 : Real) < 1 / (U ^ 2 + 4))
  have hf := Filter.eventually_cofinite.mp he
  apply hf.subset
  intro p hp
  exact not_lt_of_ge (inv_height_sq_add_four_le_reference_kernel
    ⟨(completedZeroValue_re_mem_Ioo hchi hPrimitive p).1.le,
      (completedZeroValue_re_mem_Ioo hchi hPrimitive p).2.le⟩ hp.2)

def lowZeroFinset {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) (U : Real) :
    Finset (CompletedZeroIndex chi) :=
  (finite_lowZeroWindow hchi hPrimitive U).toFinset

theorem mem_lowZeroFinset {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (U : Real) (p : CompletedZeroIndex chi) :
    p ∈ lowZeroFinset hchi hPrimitive U ↔
      (completedZeroValue p).re ∈ Set.Ioo 0 (1 / 2 : Real) ∧
        |(completedZeroValue p).im| ≤ U :=
  (finite_lowZeroWindow hchi hPrimitive U).mem_toFinset

theorem card_lowZeroFinset_le {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) (U : Real) :
    ((lowZeroFinset hchi hPrimitive U).card : Real) ≤
      (U ^ 2 + 4) * (Real.log q / 2 + 15 / 2) := by
  let S := lowZeroFinset hchi hPrimitive U
  let k : CompletedZeroIndex chi → Real :=
    fun p => (1 / (referencePoint 0 - completedZeroValue p)).re
  have hk : ∀ p, 0 ≤ k p := fun p =>
    symmetricCompletedLFunction_zeroKernel_re_nonneg hchi hPrimitive
      (by norm_num [referencePoint]) p
  have hs := summable_symmetricCompletedLFunction_zeroKernel_re hchi hPrimitive
    (s := referencePoint 0) (by norm_num [referencePoint])
  have hsum : (S.card : Real) / (U ^ 2 + 4) ≤ ∑' p, k p := by
    calc
      _ = ∑ _p ∈ S, 1 / (U ^ 2 + 4) := by simp [div_eq_mul_inv]
      _ ≤ ∑ p ∈ S, k p := by
        apply Finset.sum_le_sum
        intro p hp
        exact inv_height_sq_add_four_le_reference_kernel
          ⟨(completedZeroValue_re_mem_Ioo hchi hPrimitive p).1.le,
            (completedZeroValue_re_mem_Ioo hchi hPrimitive p).2.le⟩
          ((mem_lowZeroFinset hchi hPrimitive U p).mp hp).2
      _ ≤ ∑' p, k p := hs.sum_le_tsum S (fun p _ => hk p)
  have hbound : (∑' p, k p) ≤ Real.log q / 2 + 15 / 2 := by
    have h := HorizontalEstimate.reference_kernel_sum_le_explicit hchi hPrimitive 0
    norm_num only [abs_zero, zero_add] at h
    have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    change (∑' p, k p) ≤ _ at h
    linarith
  have h := (div_le_iff₀ (by positivity : 0 < U ^ 2 + 4)).mp (hsum.trans hbound)
  simpa only [mul_comm] using h

theorem norm_lowZero_centered_sum_le {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {t : Real} (ht : 2.5 ≤ t) (U : Real) :
    ‖∑ p ∈ lowZeroFinset hchi hPrimitive U,
      (((t : Complex) ^ completedZeroValue p -
        (2.5 : Complex) ^ completedZeroValue p) / completedZeroValue p)‖ ≤
      2 * Real.sqrt t * (U ^ 2 + 4) * (Real.log q / 2 + 15 / 2) := by
  calc
    _ ≤ ∑ p ∈ lowZeroFinset hchi hPrimitive U,
        ‖((t : Complex) ^ completedZeroValue p -
          (2.5 : Complex) ^ completedZeroValue p) / completedZeroValue p‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ lowZeroFinset hchi hPrimitive U, 2 * Real.sqrt t := by
      apply Finset.sum_le_sum
      intro p hp
      have hr := ((mem_lowZeroFinset hchi hPrimitive U p).mp hp).1
      exact norm_real_centered_kernel_low_re_le ht hr.1 hr.2.le
    _ = 2 * Real.sqrt t * ((lowZeroFinset hchi hPrimitive U).card : Real) := by
      simp [mul_comm]
    _ ≤ 2 * Real.sqrt t * ((U ^ 2 + 4) * (Real.log q / 2 + 15 / 2)) :=
      mul_le_mul_of_nonneg_left (card_lowZeroFinset_le hchi hPrimitive U) (by positivity)
    _ = _ := by ring

end LiuWang.Proof.LocalAnalyticBounds.LeftVertical
