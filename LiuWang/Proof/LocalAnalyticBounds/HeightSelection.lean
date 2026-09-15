import LiuWang.Proof.LocalAnalyticBounds.SourceWindowBound
import LiuWang.Proof.LocalAnalyticBounds.HeightHelpers.ClosedWindowSelection
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndexOfLFunctionZero

/-!
# 原文 (4.4) 的源常数高度选择

本原非主字符、`q ≥ 3`、`T ≥ 2000^15` 下，先对全部重数索引选择
高度，再通过同一字符的实际索引对应运输到 `LFunction` 零点。
负高度处重新使用依赖 `|T|` 的解析计数界，不使用共轭零点假设。
双侧出口是独立上下高度的非对称矩形，不声称共同的 `±H`。
-/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.LocalAnalyticBounds

theorem ncard_closedZeroWindow_neg_source_bound
    {q : Nat} [NeZero q] (hq : 3 ≤ q) {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {T : Real} (hT : (2000 : Real) ^ (15 : Nat) ≤ T) :
    ((closedZeroWindow chi (-T)).ncard : Real) ≤
      1.7769 * Real.log ((q : Real) * T) - 1 := by
  have hqpos : (0 : Real) < q := by exact_mod_cast (by omega : 0 < q)
  have hqone : (1 : Real) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hTtwo : 2 ≤ T := (by norm_num : (2 : Real) ≤ 2000 ^ (15 : Nat)).trans hT
  have hTpos : 0 < T := by linarith
  have hlogq := Real.log_nonneg hqone
  have hlogT : 40 ≤ Real.log T := by
    have hpow : (2 : Real) ^ (80 : Nat) ≤ T :=
      (by norm_num : (2 : Real) ^ (80 : Nat) ≤ 2000 ^ (15 : Nat)).trans hT
    have hl := Real.log_le_log (by positivity : (0 : Real) < 2 ^ (80 : Nat)) hpow
    rw [Real.log_pow] at hl
    have htwo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : Real) < 2)
    norm_num at hl htwo
    linarith
  have hshift : Real.log (T + 2) ≤ Real.log T + 1 := by
    have hm := Real.log_le_log (by linarith : 0 < T + 2)
      (by linarith : T + 2 ≤ 2 * T)
    rw [Real.log_mul (by norm_num) hTpos.ne'] at hm
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    linarith
  have hc := ncard_closedZeroWindow_le_explicit hchi hPrimitive (-T)
  rw [abs_neg, abs_of_pos hTpos] at hc
  rw [Real.log_mul hqpos.ne' hTpos.ne']
  linarith

theorem exists_source_height_index
    {q : Nat} [NeZero q] (hq : 3 ≤ q) {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {T : Real} (hT : (2000 : Real) ^ (15 : Nat) ≤ T) :
    ∃ H : Real, |H - T| ≤ 1 ∧
      ∀ p : CompletedZeroIndex chi,
        (1.7769 * Real.log ((q : Real) * T))⁻¹ ≤ |(completedZeroValue p).im - H| :=
  exists_height_away_from_completedZeros_of_count_le hchi hPrimitive T _
    (ncard_closedZeroWindow_source_bound hq hchi hPrimitive hT).2

theorem exists_source_lower_height_index
    {q : Nat} [NeZero q] (hq : 3 ≤ q) {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {T : Real} (hT : (2000 : Real) ^ (15 : Nat) ≤ T) :
    ∃ Hminus : Real, |Hminus + T| ≤ 1 ∧
      ∀ p : CompletedZeroIndex chi,
        (1.7769 * Real.log ((q : Real) * T))⁻¹ ≤
          |(completedZeroValue p).im - Hminus| := by
  simpa only [sub_neg_eq_add] using
    exists_height_away_from_completedZeros_of_count_le hchi hPrimitive (-T) _
      (ncard_closedZeroWindow_neg_source_bound hq hchi hPrimitive hT)

theorem exists_source_rectangle_heights_index
    {q : Nat} [NeZero q] (hq : 3 ≤ q) {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {T : Real} (hT : (2000 : Real) ^ (15 : Nat) ≤ T) :
    ∃ Hplus Hminus : Real, |Hplus - T| ≤ 1 ∧ |Hminus + T| ≤ 1 ∧
      ∀ p : CompletedZeroIndex chi,
        (1.7769 * Real.log ((q : Real) * T))⁻¹ ≤
            |(completedZeroValue p).im - Hplus| ∧
          (1.7769 * Real.log ((q : Real) * T))⁻¹ ≤
            |(completedZeroValue p).im - Hminus| := by
  obtain ⟨Hplus, hp, hsep⟩ := exists_source_height_index hq hchi hPrimitive hT
  obtain ⟨Hminus, hm, hsem⟩ := exists_source_lower_height_index hq hchi hPrimitive hT
  exact ⟨Hplus, Hminus, hp, hm, fun p => ⟨hsep p, hsem p⟩⟩

theorem exists_completedZeroIndex_value_eq_of_LFunction_zero
    {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {rho : Complex} (hre : 0 < rho.re) (hzero : chi.LFunction rho = 0) :
    ∃ p : CompletedZeroIndex chi, completedZeroValue p = rho :=
  BombieriVinogradov.SiegelWalfisz.exists_completedZeroIndex_of_LFunction_eq_zero
    hchi hPrimitive hre hzero

theorem LFunction_zero_separated_of_index
    {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {H r : Real}
    (hsep : ∀ p : CompletedZeroIndex chi, r ≤ |(completedZeroValue p).im - H|)
    {rho : Complex} (hre : 0 < rho.re) (hzero : chi.LFunction rho = 0) :
    r ≤ |rho.im - H| := by
  obtain ⟨p, hp⟩ := exists_completedZeroIndex_value_eq_of_LFunction_zero
    hchi hPrimitive hre hzero
  simpa only [hp] using hsep p

theorem exists_source_height_LFunction
    {q : Nat} [NeZero q] (hq : 3 ≤ q) {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {T : Real} (hT : (2000 : Real) ^ (15 : Nat) ≤ T) :
    ∃ H : Real, |H - T| ≤ 1 ∧
      ∀ rho : Complex, 0 < rho.re → rho.re < 1 → chi.LFunction rho = 0 →
        (1.7769 * Real.log ((q : Real) * T))⁻¹ ≤ |rho.im - H| := by
  obtain ⟨H, hH, hsep⟩ := exists_source_height_index hq hchi hPrimitive hT
  exact ⟨H, hH, fun _ hre _ hz =>
    LFunction_zero_separated_of_index hchi hPrimitive hsep hre hz⟩

theorem exists_source_lower_height_LFunction
    {q : Nat} [NeZero q] (hq : 3 ≤ q) {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {T : Real} (hT : (2000 : Real) ^ (15 : Nat) ≤ T) :
    ∃ Hminus : Real, |Hminus + T| ≤ 1 ∧
      ∀ rho : Complex, 0 < rho.re → rho.re < 1 → chi.LFunction rho = 0 →
        (1.7769 * Real.log ((q : Real) * T))⁻¹ ≤ |rho.im - Hminus| := by
  obtain ⟨H, hH, hsep⟩ := exists_source_lower_height_index hq hchi hPrimitive hT
  exact ⟨H, hH, fun _ hre _ hz =>
    LFunction_zero_separated_of_index hchi hPrimitive hsep hre hz⟩

theorem exists_source_rectangle_heights_LFunction
    {q : Nat} [NeZero q] (hq : 3 ≤ q) {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {T : Real} (hT : (2000 : Real) ^ (15 : Nat) ≤ T) :
    ∃ Hplus Hminus : Real, |Hplus - T| ≤ 1 ∧ |Hminus + T| ≤ 1 ∧
      ∀ rho : Complex, 0 < rho.re → rho.re < 1 → chi.LFunction rho = 0 →
        (1.7769 * Real.log ((q : Real) * T))⁻¹ ≤ |rho.im - Hplus| ∧
          (1.7769 * Real.log ((q : Real) * T))⁻¹ ≤ |rho.im - Hminus| := by
  obtain ⟨Hp, Hm, hp, hm, hsep⟩ :=
    exists_source_rectangle_heights_index hq hchi hPrimitive hT
  exact ⟨Hp, Hm, hp, hm, fun _ hre _ hz =>
    ⟨LFunction_zero_separated_of_index hchi hPrimitive (fun p => (hsep p).1) hre hz,
      LFunction_zero_separated_of_index hchi hPrimitive (fun p => (hsep p).2) hre hz⟩⟩

end LiuWang.Proof.LocalAnalyticBounds
