import LiuWang.Proof.PrincipalPsi.ClosedZeros
import LiuWang.Proof.FixedHeightZeroSum.HighZeros

/-!
# 主字符闭零点和的居中分账

低实部始终保留差商；仅高实部去中心化。界中的基数是已构造的真实
有限零点索引基数，并非计数假设；尚须另证有效计数才能数值支付。
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace LiuWang.Proof.PrincipalPsi

def closedCenteredZeroSum (q : ℕ) [NeZero q] (t T : ℝ) : ℂ :=
  ∑ p ∈ closedZeroIndices q T,
    ((t : ℂ) ^ principalZeroValue p - (2.5 : ℂ) ^ principalZeroValue p) /
      principalZeroValue p

theorem closedCentered_sub_high_eq (q : ℕ) [NeZero q] (t T : ℝ) :
    closedCenteredZeroSum q t T - highZeroSum q t T =
      (∑ p ∈ lowZeroIndices q T,
        ((t : ℂ) ^ principalZeroValue p - (2.5 : ℂ) ^ principalZeroValue p) /
          principalZeroValue p) -
      ∑ p ∈ highZeroIndices q T, (2.5 : ℂ) ^ principalZeroValue p / principalZeroValue p := by
  unfold closedCenteredZeroSum
  rw [sum_closed_eq_low_add_high]
  simp only [sub_div, Finset.sum_sub_distrib, highZeroSum]
  abel

theorem norm_low_centered_sum_le_card (q : ℕ) [NeZero q] {t : ℝ}
    (ht : 2.5 ≤ t) (T : ℝ) :
    ‖∑ p ∈ lowZeroIndices q T,
      ((t : ℂ) ^ principalZeroValue p - (2.5 : ℂ) ^ principalZeroValue p) /
        principalZeroValue p‖ ≤
      2 * Real.sqrt t * (lowZeroIndices q T).card := by
  classical
  calc
    _ ≤ ∑ p ∈ lowZeroIndices q T,
        ‖((t : ℂ) ^ principalZeroValue p - (2.5 : ℂ) ^ principalZeroValue p) /
          principalZeroValue p‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ lowZeroIndices q T, 2 * Real.sqrt t := by
      apply Finset.sum_le_sum
      intro p hp
      have hm := Finset.mem_filter.mp hp
      have hr := mem_closedZeroIndices.mp hm.1
      exact LocalAnalyticBounds.LeftVertical.norm_real_centered_kernel_low_re_le ht hr.1 hm.2.le
    _ = _ := by simp [mul_comm]

theorem norm_high_center_sum_le_card (q : ℕ) [NeZero q] (T : ℝ) :
    ‖∑ p ∈ highZeroIndices q T,
      (2.5 : ℂ) ^ principalZeroValue p / principalZeroValue p‖ ≤
      5 * (highZeroIndices q T).card := by
  calc
    _ ≤ ∑ p ∈ highZeroIndices q T,
        ‖(2.5 : ℂ) ^ principalZeroValue p / principalZeroValue p‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ highZeroIndices q T, (5 : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hm := mem_highZeroIndices.mp hp
      exact FixedHeightZeroSum.norm_high_center_kernel_le hm.2 hm.1.2.1.le
    _ = _ := by simp [mul_comm]

theorem norm_closedCentered_sub_high_le_card (q : ℕ) [NeZero q] {t : ℝ}
    (ht : 2.5 ≤ t) (T : ℝ) :
    ‖closedCenteredZeroSum q t T - highZeroSum q t T‖ ≤
      2 * Real.sqrt t * (lowZeroIndices q T).card + 5 * (highZeroIndices q T).card := by
  rw [closedCentered_sub_high_eq]
  exact (norm_sub_le _ _).trans
    (add_le_add (norm_low_centered_sum_le_card q ht T) (norm_high_center_sum_le_card q T))

end LiuWang.Proof.PrincipalPsi
