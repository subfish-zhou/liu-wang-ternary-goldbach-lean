import LiuWang.Proof.FixedHeightZeroSum.ZeroIndex
import LiuWang.Proof.NonSymmetricContour.Main
import LiuWang.Proof.LocalAnalyticBounds.SourceWindowBound

/-!
# 消去交集后的实际闭高度运输

新增与删除的标签只在 `T`、`-T` 的闭单位窗中计数。负中心直接使用
含绝对值的参考核上界，不假设同一复字符的上下零点对称。
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.LocalAnalyticBounds LiuWang.Proof.NonSymmetricContour
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.FixedHeightZeroSum

def changedZeroIndices {q : Nat} [NeZero q] (chi : Character q)
    (T Hplus Hminus : Real) : Finset (CompletedZeroIndex chi) := by
  classical
  exact (rectangleZeroIndices chi Hplus Hminus \ fixedZeroIndices chi T) ∪
    (fixedZeroIndices chi T \ rectangleZeroIndices chi Hplus Hminus)

theorem changedZeroIndices_mem_edge {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {T Hplus Hminus : Real} (hp : |Hplus - T| ≤ 1) (hm : |Hminus + T| ≤ 1)
    {p : CompletedZeroIndex chi} (h : p ∈ changedZeroIndices chi T Hplus Hminus) :
    p ∈ closedZeroWindow chi T ∨ p ∈ closedZeroWindow chi (-T) := by
  classical
  have hp' := abs_le.mp hp
  have hm' := abs_le.mp hm
  simp only [changedZeroIndices, Finset.mem_union, Finset.mem_sdiff,
    mem_rectangleZeroIndices hchi hPrimitive, mem_fixedZeroIndices hchi hPrimitive] at h
  change |T - (completedZeroValue p).im| ≤ 1 ∨
    |-T - (completedZeroValue p).im| ≤ 1
  rcases h with ⟨hr, hz⟩ | ⟨hz, hr⟩
  · have hnot := lt_of_not_ge hz
    rcases lt_abs.mp hnot with hy | hy
    · left
      apply abs_le.mpr
      constructor <;> linarith
    · right
      apply abs_le.mpr
      constructor <;> linarith
  · have hz' := abs_le.mp hz
    by_cases hy : (completedZeroValue p).im ≤ Hminus
    · right
      apply abs_le.mpr
      constructor <;> linarith
    · have hy' : Hplus ≤ (completedZeroValue p).im := by
        by_contra hh
        exact hr ⟨lt_of_not_ge hy, lt_of_not_ge hh⟩
      left
      apply abs_le.mpr
      constructor <;> linarith

theorem ncard_edge_window_le {q : Nat} [NeZero q]
    (hq : 3 ≤ q) {chi : Character q} (hchi : chi ≠ 1)
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {T H : Real} (hT : (2000 : Real) ^ (15 : Nat) ≤ T) (hH : |H| = T) :
    ((closedZeroWindow chi H).ncard : Real) ≤ 1.7769 * Real.log ((q : Real) * T) := by
  have hq0 : (0 : Real) < q := by exact_mod_cast (by omega : 0 < q)
  have hq1 : (1 : Real) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hT2 : 2 ≤ T := (by norm_num : (2 : Real) ≤ 2000 ^ (15 : Nat)).trans hT
  have hT0 : 0 < T := by linarith
  have hlogT := LeftVertical.source_height_log_ge_ninety hT
  have hshift : Real.log (T + 2) ≤ Real.log T + 1 := by
    have h := Real.log_le_log (by linarith : 0 < T + 2)
      (by linarith : T + 2 ≤ 2 * T)
    rw [Real.log_mul (by norm_num) hT0.ne'] at h
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)]
  have hc := ncard_closedZeroWindow_le_explicit hchi hPrimitive H
  rw [hH] at hc
  rw [Real.log_mul hq0.ne' hT0.ne']
  linarith [Real.log_nonneg hq1]

theorem card_changedZeroIndices_le {q : Nat} [NeZero q]
    (hq : 3 ≤ q) {chi : Character q} (hchi : chi ≠ 1)
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {T Hplus Hminus : Real} (hT : (2000 : Real) ^ (15 : Nat) ≤ T)
    (hp : |Hplus - T| ≤ 1) (hm : |Hminus + T| ≤ 1) :
    ((changedZeroIndices chi T Hplus Hminus).card : Real) ≤
      2 * 1.7769 * Real.log ((q : Real) * T) := by
  classical
  have hf := finite_closedZeroWindow hchi hPrimitive T
  have hg := finite_closedZeroWindow hchi hPrimitive (-T)
  have hs : changedZeroIndices chi T Hplus Hminus ⊆ hf.toFinset ∪ hg.toFinset := by
    intro p h
    simpa only [Finset.mem_union, hf.mem_toFinset, hg.mem_toFinset] using
      changedZeroIndices_mem_edge hchi hPrimitive hp hm h
  have hc := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have hc' : ((changedZeroIndices chi T Hplus Hminus).card : Real) ≤
      (hf.toFinset.card : Real) + (hg.toFinset.card : Real) := by exact_mod_cast hc
  have hT0 : 0 ≤ T := (by positivity : (0 : Real) ≤ 2000 ^ (15 : Nat)).trans hT
  have hpos := ncard_edge_window_le hq hchi hPrimitive hT (abs_of_nonneg hT0)
  have hneg := ncard_edge_window_le hq hchi hPrimitive hT
    (show |-T| = T by rw [abs_neg, abs_of_nonneg hT0])
  rw [Set.ncard_eq_toFinset_card _ hf] at hpos
  rw [Set.ncard_eq_toFinset_card _ hg] at hneg
  linarith

theorem norm_sum_sub_sum_le_changed {α : Type*} [DecidableEq α]
    (S Z : Finset α) (f : α → Complex) {B : Real}
    (hB : ∀ p ∈ (S \ Z) ∪ (Z \ S), ‖f p‖ ≤ B) :
    ‖(∑ p ∈ S, f p) - ∑ p ∈ Z, f p‖ ≤
      (((S \ Z) ∪ (Z \ S)).card : Real) * B := by
  have hd : Disjoint (S \ Z) (Z \ S) := by
    apply Finset.disjoint_left.mpr
    intro p hp hz
    exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_sdiff.mp hz).1
  calc
    _ = ‖(∑ p ∈ S \ Z, f p) - ∑ p ∈ Z \ S, f p‖ := by
      rw [Finset.sum_sdiff_sub_sum_sdiff]
    _ ≤ ‖∑ p ∈ S \ Z, f p‖ + ‖∑ p ∈ Z \ S, f p‖ := norm_sub_le _ _
    _ ≤ (∑ p ∈ S \ Z, ‖f p‖) + ∑ p ∈ Z \ S, ‖f p‖ :=
      add_le_add (norm_sum_le _ _) (norm_sum_le _ _)
    _ = ∑ p ∈ (S \ Z) ∪ (Z \ S), ‖f p‖ := (Finset.sum_union hd).symm
    _ ≤ ∑ _p ∈ (S \ Z) ∪ (Z \ S), B := Finset.sum_le_sum hB
    _ = _ := by simp

theorem edge_norm_ge {q : Nat} [NeZero q] {chi : Character q}
    {T : Real} {p : CompletedZeroIndex chi}
    (h : p ∈ closedZeroWindow chi T ∨ p ∈ closedZeroWindow chi (-T)) :
    T - 1 ≤ ‖completedZeroValue p‖ := by
  apply le_trans _ (Complex.abs_im_le_norm _)
  rcases h with h | h
  · change |T - (completedZeroValue p).im| ≤ 1 at h
    have hh := (abs_le.mp h).2
    linarith [le_abs_self (completedZeroValue p).im]
  · change |-T - (completedZeroValue p).im| ≤ 1 at h
    have hh := (abs_le.mp h).1
    linarith [neg_le_abs (completedZeroValue p).im]

theorem norm_real_cpow_le {x : Real} (hx : 1 ≤ x) {rho : Complex} (hr : rho.re ≤ 1) :
    ‖(x : Complex) ^ rho‖ ≤ x := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx hr

theorem norm_centered_kernel_edge_le {t T : Real} (ht : 1 ≤ t) (hT : 1 < T)
    {rho : Complex} (hr : rho.re ≤ 1) (hn : T - 1 ≤ ‖rho‖) :
    ‖((t : Complex) ^ rho - (2.5 : Complex) ^ rho) / rho‖ ≤ (t + 2.5) / (T - 1) := by
  have hc : ‖(2.5 : Complex) ^ rho‖ ≤ 2.5 :=
    norm_real_cpow_le (by norm_num : (1 : Real) ≤ 2.5) hr
  rw [norm_div]
  calc
    _ ≤ (t + 2.5) / ‖rho‖ :=
      div_le_div_of_nonneg_right ((norm_sub_le _ _).trans
        (add_le_add (norm_real_cpow_le ht hr) hc)) (norm_nonneg _)
    _ ≤ _ := div_le_div_of_nonneg_left (by linarith) (by linarith) hn

theorem norm_transport_centered_raw {q : Nat} [NeZero q]
    (hq : 3 ≤ q) {chi : Character q} (hchi : chi ≠ 1)
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {T Hplus Hminus t : Real} (hT : (2000 : Real) ^ (15 : Nat) ≤ T)
    (hp : |Hplus - T| ≤ 1) (hm : |Hminus + T| ≤ 1) (ht : 1 ≤ t) :
    ‖centeredZeroSum chi t Hplus Hminus -
      ∑ p ∈ fixedZeroIndices chi T,
        ((t : Complex) ^ completedZeroValue p - (2.5 : Complex) ^ completedZeroValue p) /
          completedZeroValue p‖ ≤
      (2 * 1.7769 * Real.log ((q : Real) * T)) * ((t + 2.5) / (T - 1)) := by
  classical
  have hT1 : 1 < T := lt_of_lt_of_le (by norm_num) hT
  apply (norm_sum_sub_sum_le_changed (rectangleZeroIndices chi Hplus Hminus)
    (fixedZeroIndices chi T) _ (fun p hp' => norm_centered_kernel_edge_le ht hT1
      (completedZeroValue_re_mem_Ioo hchi hPrimitive p).2.le
      (edge_norm_ge (changedZeroIndices_mem_edge hchi hPrimitive hp hm hp')))).trans
  exact mul_le_mul_of_nonneg_right (card_changedZeroIndices_le hq hchi hPrimitive hT hp hm)
    (by positivity)

theorem norm_transport_uncentered_raw {q : Nat} [NeZero q]
    (hq : 3 ≤ q) {chi : Character q} (hchi : chi ≠ 1)
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {T Hplus Hminus t : Real} (hT : (2000 : Real) ^ (15 : Nat) ≤ T)
    (hp : |Hplus - T| ≤ 1) (hm : |Hminus + T| ≤ 1) (ht : 1 ≤ t) :
    ‖(∑ p ∈ rectangleZeroIndices chi Hplus Hminus,
        (t : Complex) ^ completedZeroValue p / completedZeroValue p) -
      ∑ p ∈ fixedZeroIndices chi T,
        (t : Complex) ^ completedZeroValue p / completedZeroValue p‖ ≤
      (2 * 1.7769 * Real.log ((q : Real) * T)) * ((t + 2.5) / (T - 1)) := by
  classical
  have hT1 : 1 < T := lt_of_lt_of_le (by norm_num) hT
  apply (norm_sum_sub_sum_le_changed (rectangleZeroIndices chi Hplus Hminus)
    (fixedZeroIndices chi T) _ ?_).trans
  · exact mul_le_mul_of_nonneg_right
      (card_changedZeroIndices_le hq hchi hPrimitive hT hp hm) (by positivity)
  · intro p hp'
    have hn := edge_norm_ge (changedZeroIndices_mem_edge hchi hPrimitive hp hm hp')
    rw [norm_div]
    calc
      _ ≤ t / ‖completedZeroValue p‖ :=
        div_le_div_of_nonneg_right (norm_real_cpow_le ht
          (completedZeroValue_re_mem_Ioo hchi hPrimitive p).2.le) (norm_nonneg _)
      _ ≤ t / (T - 1) := div_le_div_of_nonneg_left (by linarith) (by linarith) hn
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (by linarith)

end LiuWang.Proof.FixedHeightZeroSum
