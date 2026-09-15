import LiuWang.Proof.FixedHeightZeroSum.Main

/-!
# 原域、实际积分、闭高度与重数索引的消费者

高度与三个有限集均在全称实端点之前选择。固定高窗包括 `Re rho = 1/2`
及 `|Im rho| = T`，不要求固定高度避开零点。
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.LocalAnalyticBounds LiuWang.Proof.NonSymmetricContour

namespace LiuWang.Proof.FixedHeightZeroSum.Consumer

theorem actual_fixed_height_high_zeros_all_real_endpoints
    {N q : Nat} [NeZero q] (hN : Real.exp 2000 ≤ (N : Real))
    (hq : 3 ≤ q) (hqUpper : (q : Real) ≤ (Real.log (N : Real)) ^ (6 : Nat))
    {chi : DirichletCharacter Complex q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) :
    let L : Real := Real.log (N : Real)
    let T : Real := L ^ (15 : Nat)
    let b : Real := 1 + 1 / L
    ∃ Hplus Hminus : Real, ∃ S ZT Zhigh : Finset (CompletedZeroIndex chi),
      |Hplus - T| ≤ 1 ∧ |Hminus + T| ≤ 1 ∧
      (∀ p : CompletedZeroIndex chi,
        (1.7769 * Real.log ((q : Real) * T))⁻¹ ≤ |(completedZeroValue p).im - Hplus| ∧
        (1.7769 * Real.log ((q : Real) * T))⁻¹ ≤ |(completedZeroValue p).im - Hminus|) ∧
      (∀ p : CompletedZeroIndex chi, p ∈ S ↔
        Hminus < (completedZeroValue p).im ∧ (completedZeroValue p).im < Hplus) ∧
      (∀ p : CompletedZeroIndex chi, p ∈ ZT ↔ |(completedZeroValue p).im| ≤ T) ∧
      (∀ p : CompletedZeroIndex chi, p ∈ Zhigh ↔
        |(completedZeroValue p).im| ≤ T ∧ 1 / 2 ≤ (completedZeroValue p).re) ∧
      ∀ t : Real, (N : Real) / 1000 ≤ t → t ≤ (N : Real) →
      let F : Complex → Complex := fun s =>
        (-logDeriv chi.LFunction s) * ((t : Complex) ^ s - (2.5 : Complex) ^ s) / s
      let ZS : Complex := ∑ p ∈ S,
        ((t : Complex) ^ completedZeroValue p - (2.5 : Complex) ^ completedZeroValue p) /
          completedZeroValue p
      let ZC : Complex := ∑ p ∈ ZT,
        ((t : Complex) ^ completedZeroValue p - (2.5 : Complex) ^ completedZeroValue p) /
          completedZeroValue p
      let ZH : Complex := ∑ p ∈ Zhigh,
        (t : Complex) ^ completedZeroValue p / completedZeroValue p
      RectangleBorderIntegrable F
        ((-1 / 2 : Complex) + (Hminus : Complex) * Complex.I)
        ((b : Complex) + (Hplus : Complex) * Complex.I) ∧
      ‖ZS - ZC‖ ≤ 0.00015 * t / T * L ^ (2 : Nat) ∧
      ‖ZC - ZH‖ ≤ 0.000001 * t / T * L ^ (2 : Nat) ∧
      ‖(1 / (2 * (Real.pi : Complex))) *
          (∫ u in Hminus..Hplus, F ((b : Complex) + (u : Complex) * Complex.I)) + ZH‖ ≤
        0.000171 * t / T * L ^ (2 : Nat) := by
  intro L T b
  obtain ⟨Hp, Hm, hh⟩ := exists_admissibleHeights hN hq hchi hPrimitive
  refine ⟨Hp, Hm, rectangleZeroIndices chi Hp Hm, fixedZeroIndices chi T,
    highZeroIndices chi T, hh.1, hh.2.1, hh.2.2,
    mem_rectangleZeroIndices hchi hPrimitive Hp Hm,
    mem_fixedZeroIndices hchi hPrimitive T,
    mem_highZeroIndices hchi hPrimitive T, ?_⟩
  intro t htlo hthi F ZS ZC ZH
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [F, b, L, sourceL, lowerLeft, upperRight, RectangleBorderIntegrable,
      HorizontalEstimate.horizontalIntegrand, Complex.ofReal_div,
      Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_ofNat] using
      (actual_source_rectangle_estimate hN hq hqUpper hchi hPrimitive hh htlo hthi).1
  · simpa only [ZS, ZC, L, T, sourceL, sourceT, centeredZeroSum, fixedCenteredZeroSum] using
      norm_transport_centered_source_le hN hq hqUpper hchi hPrimitive hh.1 hh.2.1 htlo hthi
  · simpa only [ZC, ZH, L, T, sourceL, sourceT, fixedCenteredZeroSum, highZeroSum] using
      norm_fixedCentered_sub_high_source_le hN hq hqUpper hchi hPrimitive htlo hthi
  · simpa only [F, ZH, b, L, T, sourceL, sourceT, actualRightVerticalIntegral, highZeroSum,
      Complex.ofReal_ofScientific] using
      actual_source_high_zero_estimate hN hq hqUpper hchi hPrimitive hh htlo hthi

end LiuWang.Proof.FixedHeightZeroSum.Consumer
