import LiuWang.Proof.FixedHeightZeroSum.HighZeros

/-!
# 实际右垂直积分与固定闭高度高实部零点和

分账为 `0.00002 + 0.00015 + 0.000001 = 0.000171`。
这是实际积分公式，不是 Perron 公式或完整的 psi 公式。
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.LocalAnalyticBounds LiuWang.Proof.NonSymmetricContour

namespace LiuWang.Proof.FixedHeightZeroSum

def actualRightVerticalIntegral {q : Nat} [NeZero q] (chi : Character q)
    (t c b Hminus Hplus : Real) : Complex :=
  (1 / (2 * (Real.pi : Complex))) *
    ∫ u in Hminus..Hplus,
      (-logDeriv chi.LFunction ((b : Complex) + (u : Complex) * Complex.I)) *
        ((t : Complex) ^ ((b : Complex) + (u : Complex) * Complex.I) -
          (c : Complex) ^ ((b : Complex) + (u : Complex) * Complex.I)) /
        ((b : Complex) + (u : Complex) * Complex.I)

theorem norm_transport_centered_source_le {N q : Nat} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : Real)) (hq : 3 ≤ q)
    (hqUpper : (q : Real) ≤ sourceP1 N) {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {Hplus Hminus : Real} (hp : |Hplus - sourceT N| ≤ 1) (hm : |Hminus + sourceT N| ≤ 1)
    {t : Real} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : Real)) :
    ‖centeredZeroSum chi t Hplus Hminus - fixedCenteredZeroSum chi t (sourceT N)‖ ≤
      0.00015 * t / sourceT N * sourceL N ^ (2 : Nat) := by
  obtain ⟨_, ht, _⟩ := HorizontalEstimate.source_horizontal_parameters hN htlo hthi
  exact (norm_transport_centered_raw hq hchi hPrimitive (sourceT_large hN) hp hm
    (by linarith : 1 ≤ t)).trans (transport_cost_le_budget hN hq hqUpper htlo)

theorem norm_transport_uncentered_source_le {N q : Nat} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : Real)) (hq : 3 ≤ q)
    (hqUpper : (q : Real) ≤ sourceP1 N) {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {Hplus Hminus : Real} (hp : |Hplus - sourceT N| ≤ 1) (hm : |Hminus + sourceT N| ≤ 1)
    {t : Real} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : Real)) :
    ‖(∑ p ∈ rectangleZeroIndices chi Hplus Hminus,
        (t : Complex) ^ completedZeroValue p / completedZeroValue p) -
      ∑ p ∈ fixedZeroIndices chi (sourceT N),
        (t : Complex) ^ completedZeroValue p / completedZeroValue p‖ ≤
      0.00015 * t / sourceT N * sourceL N ^ (2 : Nat) := by
  obtain ⟨_, ht, _⟩ := HorizontalEstimate.source_horizontal_parameters hN htlo hthi
  exact (norm_transport_uncentered_raw hq hchi hPrimitive (sourceT_large hN) hp hm
    (by linarith : 1 ≤ t)).trans (transport_cost_le_budget hN hq hqUpper htlo)

theorem actual_source_high_zero_estimate {N q : Nat} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : Real)) (hq : 3 ≤ q)
    (hqUpper : (q : Real) ≤ sourceP1 N) {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {Hplus Hminus : Real} (h : AdmissibleHeights N chi Hplus Hminus)
    {t : Real} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : Real)) :
    ‖actualRightVerticalIntegral chi t 2.5 (1 + 1 / sourceL N) Hminus Hplus +
        highZeroSum chi t (sourceT N)‖ ≤
      0.000171 * t / sourceT N * sourceL N ^ (2 : Nat) := by
  let R := actualRightVerticalIntegral chi t 2.5 (1 + 1 / sourceL N) Hminus Hplus
  let S := centeredZeroSum chi t Hplus Hminus
  let Z := fixedCenteredZeroSum chi t (sourceT N)
  let H := highZeroSum chi t (sourceT N)
  have hR : ‖R + S‖ ≤ 0.00002 * t / sourceT N * sourceL N ^ (2 : Nat) := by
    simpa only [R, S, actualRightVerticalIntegral, verticalIntegral,
      HorizontalEstimate.horizontalIntegrand, Complex.ofReal_ofScientific] using
      (actual_source_rectangle_estimate hN hq hqUpper hchi hPrimitive h htlo hthi).2.2.2
  have hB : ‖S - Z‖ ≤ 0.00015 * t / sourceT N * sourceL N ^ (2 : Nat) :=
    norm_transport_centered_source_le hN hq hqUpper hchi hPrimitive h.1 h.2.1 htlo hthi
  have hC : ‖Z - H‖ ≤ 0.000001 * t / sourceT N * sourceL N ^ (2 : Nat) :=
    norm_fixedCentered_sub_high_source_le hN hq hqUpper hchi hPrimitive htlo hthi
  change ‖R + H‖ ≤ _
  calc
    _ = ‖((R + S) - (S - Z)) - (Z - H)‖ := by congr 1; abel
    _ ≤ ‖(R + S) - (S - Z)‖ + ‖Z - H‖ := norm_sub_le _ _
    _ ≤ (‖R + S‖ + ‖S - Z‖) + ‖Z - H‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ (0.00002 * t / sourceT N * sourceL N ^ (2 : Nat) +
        0.00015 * t / sourceT N * sourceL N ^ (2 : Nat)) +
        0.000001 * t / sourceT N * sourceL N ^ (2 : Nat) :=
      add_le_add (add_le_add hR hB) hC
    _ = _ := by ring

theorem exists_actual_high_zero_estimate_all_real_endpoints
    {N q : Nat} [NeZero q] (hN : Real.exp 2000 ≤ (N : Real)) (hq : 3 ≤ q)
    (hqUpper : (q : Real) ≤ sourceP1 N) {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) :
    ∃ Hplus Hminus, AdmissibleHeights N chi Hplus Hminus ∧
      ∀ t : Real, sourceWindowLower N ≤ t → t ≤ (N : Real) →
        ‖actualRightVerticalIntegral chi t 2.5 (1 + 1 / sourceL N) Hminus Hplus +
            highZeroSum chi t (sourceT N)‖ ≤
          0.000171 * t / sourceT N * sourceL N ^ (2 : Nat) := by
  obtain ⟨Hp, Hm, hh⟩ := exists_admissibleHeights hN hq hchi hPrimitive
  exact ⟨Hp, Hm, hh, fun _ htlo hthi =>
    actual_source_high_zero_estimate hN hq hqUpper hchi hPrimitive hh htlo hthi⟩

end LiuWang.Proof.FixedHeightZeroSum
