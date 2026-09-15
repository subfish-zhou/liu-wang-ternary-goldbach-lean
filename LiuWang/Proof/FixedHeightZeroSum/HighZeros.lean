import LiuWang.Proof.FixedHeightZeroSum.Budget

/-!
# 保留低实部差商整体的高实部化

低实部项直接复用积分差商粗界。仅高实部项去中心化；此处 `|rho| ≥ 1/2`。
全部闭窗的粗计数来自真实可求和参考核，不使用未证零点距离。
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.LocalAnalyticBounds
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.FixedHeightZeroSum

def fixedCenteredZeroSum {q : Nat} [NeZero q] (chi : Character q) (t T : Real) : Complex :=
  ∑ p ∈ fixedZeroIndices chi T,
    ((t : Complex) ^ completedZeroValue p - (2.5 : Complex) ^ completedZeroValue p) /
      completedZeroValue p

def highZeroSum {q : Nat} [NeZero q] (chi : Character q) (t T : Real) : Complex :=
  ∑ p ∈ highZeroIndices chi T,
    (t : Complex) ^ completedZeroValue p / completedZeroValue p

theorem card_fixedZeroIndices_le {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) (T : Real) :
    ((fixedZeroIndices chi T).card : Real) ≤
      (T ^ (2 : Nat) + 4) * (Real.log q / 2 + 15 / 2) := by
  let S := fixedZeroIndices chi T
  let k : CompletedZeroIndex chi → Real :=
    fun p => (1 / (referencePoint 0 - completedZeroValue p)).re
  have hk : ∀ p, 0 ≤ k p := fun p =>
    symmetricCompletedLFunction_zeroKernel_re_nonneg hchi hPrimitive
      (by norm_num [referencePoint]) p
  have hs := summable_symmetricCompletedLFunction_zeroKernel_re hchi hPrimitive
    (s := referencePoint 0) (by norm_num [referencePoint])
  have hsum : (S.card : Real) / (T ^ (2 : Nat) + 4) ≤ ∑' p, k p := by
    calc
      _ = ∑ _p ∈ S, 1 / (T ^ (2 : Nat) + 4) := by simp [div_eq_mul_inv]
      _ ≤ ∑ p ∈ S, k p := by
        apply Finset.sum_le_sum
        intro p hp
        exact LeftVertical.inv_height_sq_add_four_le_reference_kernel
          ⟨(completedZeroValue_re_mem_Ioo hchi hPrimitive p).1.le,
            (completedZeroValue_re_mem_Ioo hchi hPrimitive p).2.le⟩
          ((mem_fixedZeroIndices hchi hPrimitive T p).mp hp)
      _ ≤ ∑' p, k p := hs.sum_le_tsum S (fun p _ => hk p)
  have hbound : (∑' p, k p) ≤ Real.log q / 2 + 15 / 2 := by
    have h := HorizontalEstimate.reference_kernel_sum_le_explicit hchi hPrimitive 0
    norm_num only [abs_zero, zero_add] at h
    have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    change (∑' p, k p) ≤ _ at h
    linarith
  have h := (div_le_iff₀ (by positivity : 0 < T ^ (2 : Nat) + 4)).mp (hsum.trans hbound)
  simpa only [mul_comm] using h

theorem norm_high_center_kernel_le {rho : Complex}
    (hrlo : 1 / 2 ≤ rho.re) (hrhi : rho.re ≤ 1) :
    ‖(2.5 : Complex) ^ rho / rho‖ ≤ 5 := by
  have hn : 1 / 2 ≤ ‖rho‖ := hrlo.trans (Complex.re_le_norm rho)
  rw [norm_div]
  apply (div_le_iff₀ (by linarith : 0 < ‖rho‖)).mpr
  have hc : ‖(2.5 : Complex) ^ rho‖ ≤ 2.5 :=
    norm_real_cpow_le (by norm_num : (1 : Real) ≤ 2.5) hrhi
  linarith

theorem norm_high_center_sum_le {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) (T : Real) :
    ‖∑ p ∈ highZeroIndices chi T,
      (2.5 : Complex) ^ completedZeroValue p / completedZeroValue p‖ ≤
      5 * (T ^ (2 : Nat) + 4) * (Real.log q / 2 + 15 / 2) := by
  classical
  have hc : ((highZeroIndices chi T).card : Real) ≤
      ((fixedZeroIndices chi T).card : Real) := by
    exact_mod_cast Finset.card_le_card
      (show highZeroIndices chi T ⊆ fixedZeroIndices chi T from Finset.filter_subset _ _)
  calc
    _ ≤ ∑ p ∈ highZeroIndices chi T,
        ‖(2.5 : Complex) ^ completedZeroValue p / completedZeroValue p‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ highZeroIndices chi T, (5 : Real) := by
      apply Finset.sum_le_sum
      intro p hp
      exact norm_high_center_kernel_le
        ((mem_highZeroIndices hchi hPrimitive T p).mp hp).2
        (completedZeroValue_re_mem_Ioo hchi hPrimitive p).2.le
    _ = 5 * ((highZeroIndices chi T).card : Real) := by simp [mul_comm]
    _ ≤ 5 * ((T ^ (2 : Nat) + 4) * (Real.log q / 2 + 15 / 2)) :=
      mul_le_mul_of_nonneg_left (hc.trans (card_fixedZeroIndices_le hchi hPrimitive T))
        (by norm_num)
    _ = _ := by ring

theorem fixedCentered_sub_high_eq {q : Nat} [NeZero q] (chi : Character q) (t T : Real) :
    fixedCenteredZeroSum chi t T - highZeroSum chi t T =
      (∑ p ∈ lowZeroIndices chi T,
        ((t : Complex) ^ completedZeroValue p - (2.5 : Complex) ^ completedZeroValue p) /
          completedZeroValue p) -
      ∑ p ∈ highZeroIndices chi T,
        (2.5 : Complex) ^ completedZeroValue p / completedZeroValue p := by
  have hh :
      (∑ p ∈ highZeroIndices chi T,
        ((t : Complex) ^ completedZeroValue p - (2.5 : Complex) ^ completedZeroValue p) /
          completedZeroValue p) =
      highZeroSum chi t T -
        ∑ p ∈ highZeroIndices chi T,
          (2.5 : Complex) ^ completedZeroValue p / completedZeroValue p := by
    simp only [sub_div, Finset.sum_sub_distrib, highZeroSum]
  unfold fixedCenteredZeroSum
  rw [sum_fixed_eq_low_add_high, hh]
  abel

theorem norm_fixedCentered_sub_high_raw {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {t : Real} (ht : 2.5 ≤ t) (T : Real) :
    ‖fixedCenteredZeroSum chi t T - highZeroSum chi t T‖ ≤
      (2 * Real.sqrt t + 5) * (T ^ (2 : Nat) + 4) *
        (Real.log q / 2 + 15 / 2) := by
  rw [fixedCentered_sub_high_eq, lowZeroIndices_eq hchi hPrimitive]
  calc
    _ ≤ ‖∑ p ∈ LeftVertical.lowZeroFinset hchi hPrimitive T,
        ((t : Complex) ^ completedZeroValue p - (2.5 : Complex) ^ completedZeroValue p) /
          completedZeroValue p‖ +
      ‖∑ p ∈ highZeroIndices chi T,
        (2.5 : Complex) ^ completedZeroValue p / completedZeroValue p‖ := norm_sub_le _ _
    _ ≤ 2 * Real.sqrt t * (T ^ (2 : Nat) + 4) * (Real.log q / 2 + 15 / 2) +
        5 * (T ^ (2 : Nat) + 4) * (Real.log q / 2 + 15 / 2) :=
      add_le_add (LeftVertical.norm_lowZero_centered_sum_le hchi hPrimitive ht T)
        (norm_high_center_sum_le hchi hPrimitive T)
    _ = _ := by ring

theorem norm_fixedCentered_sub_high_source_le {N q : Nat} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : Real)) (hq : 3 ≤ q)
    (hqUpper : (q : Real) ≤ sourceP1 N) {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {t : Real} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : Real)) :
    ‖fixedCenteredZeroSum chi t (sourceT N) - highZeroSum chi t (sourceT N)‖ ≤
      0.000001 * t / sourceT N * sourceL N ^ (2 : Nat) := by
  obtain ⟨_, ht, _⟩ := HorizontalEstimate.source_horizontal_parameters hN htlo hthi
  exact (norm_fixedCentered_sub_high_raw hchi hPrimitive (by linarith) (sourceT N)).trans
    (low_and_center_cost_le_budget hN hq hqUpper htlo)

end LiuWang.Proof.FixedHeightZeroSum
