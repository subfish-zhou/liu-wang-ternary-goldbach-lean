import LiuWang.Proof.LocalAnalyticBounds.LeftVertical.Integral
import LiuWang.Proof.LocalAnalyticBounds.LeftVertical.Budget

/-!
# 实际左垂直边：原 `1.632` 及 `10⁻⁵ t T⁻¹ L²` 预算

任意独立端点 `Hplus`、`Hminus` 均可；没有对称性或零点分离假设。
积分变量为 `du`，归一化为实数 `1 / (2π)`。
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.LocalAnalyticBounds.LeftVertical

theorem norm_left_integral_source_sharp_le
    {N q : Nat} [NeZero q] (hN : Real.exp 2000 ≤ (N : Real))
    (hq : 3 ≤ q) {chi : DirichletCharacter Complex q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {t Hplus Hminus : Real} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : Real))
    (hp : |Hplus - sourceT N| ≤ 1) (hm : |Hminus + sourceT N| ≤ 1) :
    ‖∫ u in Hminus..Hplus, HorizontalEstimate.horizontalIntegrand chi t
      ((-1 / 2 : Complex) + (u : Complex) * Complex.I)‖ / (2 * Real.pi) ≤
      1.632 * Real.log ((q : Real) * sourceT N) * Real.log (sourceT N) := by
  obtain ⟨hT, ht, _⟩ := HorizontalEstimate.source_horizontal_parameters hN htlo hthi
  have hT1 : 1 ≤ sourceT N :=
    (by norm_num : (1 : Real) ≤ 2000 ^ (15 : Nat)).trans hT
  have hi := norm_left_integral_le_explicit hchi hPrimitive (by linarith : 9 ≤ t) hT1 hp hm
  exact (div_le_div_of_nonneg_right hi (by positivity)).trans
    (normalized_explicit_bound_le_source hq hT)

theorem norm_left_integral_source_small_le
    {N q : Nat} [NeZero q] (hN : Real.exp 2000 ≤ (N : Real))
    (hq : 3 ≤ q) (hqUpper : (q : Real) ≤ sourceP1 N)
    {chi : DirichletCharacter Complex q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {t Hplus Hminus : Real} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : Real))
    (hp : |Hplus - sourceT N| ≤ 1) (hm : |Hminus + sourceT N| ≤ 1) :
    ‖∫ u in Hminus..Hplus, HorizontalEstimate.horizontalIntegrand chi t
      ((-1 / 2 : Complex) + (u : Complex) * Complex.I)‖ / (2 * Real.pi) ≤
      (1 / 100000 : Real) * t / sourceT N * sourceL N ^ (2 : Nat) :=
  (norm_left_integral_source_sharp_le hN hq hchi hPrimitive htlo hthi hp hm).trans
    (source_left_cost_le_small_budget hN hq hqUpper htlo)

theorem actual_left_vertical_estimate
    {N q : Nat} [NeZero q] (hN : Real.exp 2000 ≤ (N : Real))
    (hq : 3 ≤ q) (hqUpper : (q : Real) ≤ sourceP1 N)
    {chi : DirichletCharacter Complex q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {Hplus Hminus : Real}
    (hp : |Hplus - sourceT N| ≤ 1) (hm : |Hminus + sourceT N| ≤ 1)
    {t : Real} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : Real)) :
    (∀ u : Real,
      chi.LFunction ((-1 / 2 : Complex) + (u : Complex) * Complex.I) ≠ 0 ∧
      (-1 / 2 : Complex) + (u : Complex) * Complex.I ≠ 0) ∧
    Continuous (fun u : Real => HorizontalEstimate.horizontalIntegrand chi t
      ((-1 / 2 : Complex) + (u : Complex) * Complex.I)) ∧
    IntervalIntegrable (fun u : Real => HorizontalEstimate.horizontalIntegrand chi t
      ((-1 / 2 : Complex) + (u : Complex) * Complex.I)) volume Hminus Hplus ∧
    (‖∫ u in Hminus..Hplus, HorizontalEstimate.horizontalIntegrand chi t
      ((-1 / 2 : Complex) + (u : Complex) * Complex.I)‖ / (2 * Real.pi) ≤
      1.632 * Real.log ((q : Real) * sourceT N) * Real.log (sourceT N)) ∧
    (‖∫ u in Hminus..Hplus, HorizontalEstimate.horizontalIntegrand chi t
      ((-1 / 2 : Complex) + (u : Complex) * Complex.I)‖ / (2 * Real.pi) ≤
      (1 / 100000 : Real) * t / sourceT N * sourceL N ^ (2 : Nat)) := by
  have ht : 0 < t := (sourceT_pos hN).trans (sourceT_lt_real_endpoint hN htlo)
  refine ⟨?_, continuous_left_integrand hchi hPrimitive ht,
    intervalIntegrable_left_integrand hchi hPrimitive ht Hminus Hplus,
    norm_left_integral_source_sharp_le hN hq hchi hPrimitive htlo hthi hp hm,
    norm_left_integral_source_small_le hN hq hqUpper hchi hPrimitive htlo hthi hp hm⟩
  intro u
  refine ⟨BombieriVinogradov.SiegelWalfisz.LFunction_ne_zero_of_re_eq_neg_one_half
    hchi hPrimitive (by norm_num), ?_⟩
  intro h
  have hh := congrArg Complex.re h
  norm_num at hh

end LiuWang.Proof.LocalAnalyticBounds.LeftVertical
