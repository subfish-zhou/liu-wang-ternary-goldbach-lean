import LiuWang.Proof.LocalAnalyticBounds.HeightHelpers.LocalHorizontalBounds

/-!
# 实际高度出口的消费者

这里从字符与源高度条件直接取得实际零点结论，不把计数界或分离性
列为前提；同时检查源阈值、独立上下高度的符号与局部非零性。
-/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.LocalAnalyticBounds

namespace LiuWang.Proof.LocalAnalyticBounds.HeightConsumer

theorem source_single_side
    {q : Nat} [NeZero q] (hq : 3 ≤ q) {chi : Character q}
    (hchi : chi ≠ 1) (hp : DirichletCharacter.IsPrimitive chi)
    {T : Real} (hT : (2000 : Real) ^ (15 : Nat) ≤ T) :
    ∃ H : Real, 0 < H ∧ |H - T| ≤ 1 ∧
      ∀ rho : Complex, 0 < rho.re → rho.re < 1 → chi.LFunction rho = 0 →
        (1.7769 * Real.log ((q : Real) * T))⁻¹ ≤ |rho.im - H| := by
  obtain ⟨H, hH, hsep⟩ := exists_source_height_LFunction hq hchi hp hT
  have hTr : (2 : Real) ≤ T :=
    (by norm_num : (2 : Real) ≤ 2000 ^ (15 : Nat)).trans hT
  exact ⟨H, by have := (abs_le.mp hH).1; linarith, hH, hsep⟩

theorem source_independent_sides
    {q : Nat} [NeZero q] (hq : 3 ≤ q) {chi : Character q}
    (hchi : chi ≠ 1) (hp : DirichletCharacter.IsPrimitive chi)
    {T : Real} (hT : (2000 : Real) ^ (15 : Nat) ≤ T) :
    ∃ Hplus Hminus : Real, 0 < Hplus ∧ Hminus < 0 ∧
      |Hplus - T| ≤ 1 ∧ |Hminus + T| ≤ 1 ∧
      ∀ rho : Complex, 0 < rho.re → rho.re < 1 → chi.LFunction rho = 0 →
        (1.7769 * Real.log ((q : Real) * T))⁻¹ ≤ |rho.im - Hplus| ∧
          (1.7769 * Real.log ((q : Real) * T))⁻¹ ≤ |rho.im - Hminus| := by
  obtain ⟨Hp, Hm, hp, hm, hsep⟩ := exists_source_rectangle_heights_LFunction hq hchi hp hT
  have hTr : (2 : Real) ≤ T :=
    (by norm_num : (2 : Real) ≤ 2000 ^ (15 : Nat)).trans hT
  refine ⟨Hp, Hm, ?_, ?_, hp, hm, hsep⟩
  · have := (abs_le.mp hp).1
    linarith
  · have := (abs_le.mp hm).2
    linarith

theorem source_threshold_indices
    {q : Nat} [NeZero q] (hq : 3 ≤ q) {chi : Character q}
    (hchi : chi ≠ 1) (hp : DirichletCharacter.IsPrimitive chi) :
    ∃ H : Real, |H - (2000 : Real) ^ (15 : Nat)| ≤ 1 ∧
      ∀ p : CompletedZeroIndex chi,
        (1.7769 * Real.log ((q : Real) * (2000 : Real) ^ (15 : Nat)))⁻¹ ≤
          |(completedZeroValue p).im - H| :=
  exists_source_height_index hq hchi hp le_rfl

theorem source_horizontal_nonvanishing
    {q : Nat} [NeZero q] (hq : 3 ≤ q) {chi : Character q}
    (hchi : chi ≠ 1) (hp : DirichletCharacter.IsPrimitive chi)
    {T : Real} (hT : (2000 : Real) ^ (15 : Nat) ≤ T) :
    ∃ Hplus Hminus : Real, |Hplus - T| ≤ 1 ∧ |Hminus + T| ≤ 1 ∧
      ∀ sigma : Real, 0 < sigma →
        chi.LFunction ((sigma : Complex) + (Hplus : Complex) * Complex.I) ≠ 0 ∧
        chi.LFunction ((sigma : Complex) + (Hminus : Complex) * Complex.I) ≠ 0 := by
  obtain ⟨Hp, Hm, hp, hm, hbounds⟩ := exists_source_rectangle_local_bounds hq hchi hp hT
  have hr := inv_pos.mpr (source_height_budget_pos hq hT)
  refine ⟨Hp, Hm, hp, hm, fun sigma hs => ?_⟩
  constructor
  · apply (hbounds Hp (by simp)).1
    · simpa using hs
    · simpa using hr
  · apply (hbounds Hm (by simp)).1
    · simpa using hs
    · simpa using hr

theorem empty_grid (T : Real) :
    ∃ H : Real, H = T ∧ ∀ x ∈ (∅ : Finset Real), (1 : Real) ≤ |x - H| := by
  obtain ⟨H, hH, _⟩ := exists_sharp_interval_away_from_finset ∅ T
  simp only [Finset.card_empty, Nat.cast_zero, zero_add, div_one, sub_self,
    abs_nonpos_iff, sub_eq_zero] at hH
  exact ⟨H, hH, by simp⟩

theorem repeated_ordinate_grid (T x : Real) :
    ∃ H : Real, |H - T| ≤ 1 / 2 ∧ 1 / 2 ≤ |x - H| := by
  classical
  obtain ⟨H, hH, hsep⟩ := exists_sharp_interval_away_from_finset {x, x} T
  norm_num at hH hsep
  exact ⟨H, hH, hsep⟩

end LiuWang.Proof.LocalAnalyticBounds.HeightConsumer
