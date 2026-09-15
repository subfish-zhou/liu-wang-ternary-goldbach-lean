import LiuWang.Proof.LocalAnalyticBounds.ClosedZeroWindow
import LiuWang.Proof.LocalAnalyticBounds.HeightHelpers.SharpIntervalAvoidance

/-!
# 从闭窗口到全部重数索引

纵坐标像的基数只使用上界，不假设不同重数索引有不同纵坐标。
窗口外的距离由中心三角不等式和网格的端点余量控制。
-/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.LocalAnalyticBounds

theorem exists_height_away_from_completedZeros
    {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) (T : Real) :
    ∃ H : Real,
      |H - T| ≤ 1 - 1 / (((closedZeroWindow chi T).ncard : Real) + 1) ∧
      ∀ p : CompletedZeroIndex chi,
        1 / (((closedZeroWindow chi T).ncard : Real) + 1) ≤
          |(completedZeroValue p).im - H| := by
  classical
  have hf := finite_closedZeroWindow hchi hPrimitive T
  let s : Finset Real := hf.toFinset.image (fun p => (completedZeroValue p).im)
  have hcard : s.card ≤ (closedZeroWindow chi T).ncard := by
    rw [Set.ncard_eq_toFinset_card _ hf]
    exact Finset.card_image_le
  have hcast : (s.card : Real) ≤ ((closedZeroWindow chi T).ncard : Real) :=
    Nat.cast_le.mpr hcard
  have hradius : 1 / (((closedZeroWindow chi T).ncard : Real) + 1) ≤
      1 / ((s.card : Real) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  obtain ⟨H, hH, hsep⟩ := exists_sharp_interval_away_from_finset s T
  refine ⟨H, by linarith, fun p => ?_⟩
  by_cases hp : p ∈ closedZeroWindow chi T
  · exact hradius.trans (hsep _ (Finset.mem_image.mpr
      ⟨p, hf.mem_toFinset.mpr hp, rfl⟩))
  · have hout : 1 < |T - (completedZeroValue p).im| := lt_of_not_ge hp
    have htri := abs_sub_le T H (completedZeroValue p).im
    rw [abs_sub_comm T H, abs_sub_comm H (completedZeroValue p).im] at htri
    linarith

theorem exists_height_away_from_completedZeros_of_count_le
    {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (T B : Real) (hcount : ((closedZeroWindow chi T).ncard : Real) ≤ B - 1) :
    ∃ H : Real, |H - T| ≤ 1 ∧
      ∀ p : CompletedZeroIndex chi, B⁻¹ ≤ |(completedZeroValue p).im - H| := by
  have hradius : B⁻¹ ≤ 1 / (((closedZeroWindow chi T).ncard : Real) + 1) := by
    rw [← one_div]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  obtain ⟨H, hH, hsep⟩ := exists_height_away_from_completedZeros hchi hPrimitive T
  refine ⟨H, ?_, fun p => hradius.trans (hsep p)⟩
  have hr : 0 ≤ 1 / (((closedZeroWindow chi T).ncard : Real) + 1) := by positivity
  linarith

end LiuWang.Proof.LocalAnalyticBounds
