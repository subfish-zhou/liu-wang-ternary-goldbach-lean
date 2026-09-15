import LiuWang.Proof.NonSymmetricContour.Main

/-!
# 原域、原被积函数、先高度及索引后全实端点的消费者

原点预算包含在 `0.00002` 中；此结论只涉及右积分，不是 Perron 估计或 ψ 公式。
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.NonSymmetricContour.Consumer

theorem actual_centered_identity_all_real_endpoints
    {N q : Nat} [NeZero q] (hN : Real.exp 2000 ≤ (N : Real))
    (hq : 3 ≤ q) (hqUpper : (q : Real) ≤ (Real.log (N : Real)) ^ (6 : Nat))
    {chi : DirichletCharacter Complex q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) :
    let L : Real := Real.log (N : Real)
    let T : Real := L ^ (15 : Nat)
    let b : Real := 1 + 1 / L
    ∃ Hplus Hminus : Real, ∃ S : Finset (CompletedZeroIndex chi),
      |Hplus - T| ≤ 1 ∧ |Hminus + T| ≤ 1 ∧
      (∀ p : CompletedZeroIndex chi,
        (1.7769 * Real.log ((q : Real) * T))⁻¹ ≤ |(completedZeroValue p).im - Hplus| ∧
        (1.7769 * Real.log ((q : Real) * T))⁻¹ ≤ |(completedZeroValue p).im - Hminus|) ∧
      (∀ p : CompletedZeroIndex chi, p ∈ S ↔
        Hminus < (completedZeroValue p).im ∧ (completedZeroValue p).im < Hplus) ∧
      (∀ s ∈ RectangleBorder
          ((-1 / 2 : Complex) + (Hminus : Complex) * Complex.I)
          ((b : Complex) + (Hplus : Complex) * Complex.I),
        chi.LFunction s ≠ 0 ∧ s ≠ 0) ∧
      ∀ t : Real, (N : Real) / 1000 ≤ t → t ≤ (N : Real) →
      let F : Complex → Complex := fun s =>
        (-logDeriv chi.LFunction s) * ((t : Complex) ^ s - (2.5 : Complex) ^ s) / s
      let Z : Complex := ∑ p ∈ S,
        ((t : Complex) ^ completedZeroValue p - (2.5 : Complex) ^ completedZeroValue p) /
          completedZeroValue p
      let O : Complex := (lFunctionOriginMultiplicity chi : Complex) * (Real.log (t / 2.5) : Complex)
      RectangleBorderIntegrable F
        ((-1 / 2 : Complex) + (Hminus : Complex) * Complex.I)
        ((b : Complex) + (Hplus : Complex) * Complex.I) ∧
      ((1 / (2 * (Real.pi : Complex))) *
          (∫ u in Hminus..Hplus, F ((b : Complex) + (u : Complex) * Complex.I)) + Z + O =
        (1 / (2 * (Real.pi : Complex))) *
          (∫ u in Hminus..Hplus, F ((-1 / 2 : Complex) + (u : Complex) * Complex.I)) +
        (1 / (2 * (Real.pi : Complex) * Complex.I)) *
          (∫ σ in (-1 / 2 : Real)..b, F ((σ : Complex) + (Hplus : Complex) * Complex.I)) -
        (1 / (2 * (Real.pi : Complex) * Complex.I)) *
          (∫ σ in (-1 / 2 : Real)..b, F ((σ : Complex) + (Hminus : Complex) * Complex.I))) ∧
      (‖(1 / (2 * (Real.pi : Complex))) *
          (∫ u in Hminus..Hplus, F ((b : Complex) + (u : Complex) * Complex.I)) + Z + O‖ ≤
        0.0014 * t / T * (Real.log ((q : Real) * T)) ^ 2 +
          (1 / 100000 : Real) * t / T * L ^ (2 : Nat)) ∧
      (‖(1 / (2 * (Real.pi : Complex))) *
          (∫ u in Hminus..Hplus, F ((b : Complex) + (u : Complex) * Complex.I)) + Z‖ ≤
        0.00002 * t / T * L ^ (2 : Nat)) := by
  intro L T b
  obtain ⟨Hp, Hm, hh⟩ := exists_admissibleHeights hN hq hchi hPrimitive
  refine ⟨Hp, Hm, rectangleZeroIndices chi Hp Hm, hh.1, hh.2.1, hh.2.2,
    mem_rectangleZeroIndices hchi hPrimitive Hp Hm, ?_, ?_⟩
  · intro s hs
    have hb : 1 ≤ b := by
      have hi : 0 ≤ 1 / sourceL N := by have := sourceL_pos hN; positivity
      change 1 ≤ 1 + 1 / sourceL N
      linarith
    obtain ⟨hp0, hm0⟩ := admissibleHeights_signs hN hh
    exact ⟨admissibleHeights_border hN hq hchi hPrimitive hh s hs,
      fun hz => zero_not_mem_border hb hp0 hm0 (hz ▸ hs)⟩
  · intro t htlo hthi F Z O
    simpa only [F, Z, O, b, L, T, sourceL, sourceT, centeredZeroSum, RectangleBorderIntegrable,
      LocalAnalyticBounds.HorizontalEstimate.horizontalIntegrand,
      lowerLeft, upperRight, verticalIntegral, threeSides, horizontalIntegral,
      Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_ofNat] using
      actual_source_rectangle_estimate hN hq hqUpper hchi hPrimitive hh htlo hthi

end LiuWang.Proof.NonSymmetricContour.Consumer
