import LiuWang.Proof.LocalAnalyticBounds.LeftVertical.Main

/-!
# 原域、字面原式、任意非对称高度的消费者

高度在全部实数 `t` 之前量化；既不新建平行被积函数，也不假设对数导数界。
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace LiuWang.Proof.LocalAnalyticBounds.LeftVertical.Consumer

theorem actual_source_left_vertical_budget
    {N q : Nat} [NeZero q] (hN : Real.exp 2000 ≤ (N : Real))
    (hq : 3 ≤ q) (hqUpper : (q : Real) ≤ (Real.log (N : Real)) ^ (6 : Nat))
    {chi : DirichletCharacter Complex q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) :
    let L : Real := Real.log (N : Real)
    let T : Real := L ^ (15 : Nat)
    ∀ Hplus Hminus : Real, |Hplus - T| ≤ 1 → |Hminus + T| ≤ 1 →
    ∀ t : Real, (N : Real) / 1000 ≤ t → t ≤ (N : Real) →
    let F : Complex → Complex := fun s =>
      (-logDeriv chi.LFunction s) * ((t : Complex) ^ s - (2.5 : Complex) ^ s) / s
    (∀ u : Real,
      chi.LFunction ((-1 / 2 : Complex) + (u : Complex) * Complex.I) ≠ 0 ∧
      (-1 / 2 : Complex) + (u : Complex) * Complex.I ≠ 0) ∧
    Continuous (fun u : Real => F ((-1 / 2 : Complex) + (u : Complex) * Complex.I)) ∧
    IntervalIntegrable (fun u : Real => F ((-1 / 2 : Complex) + (u : Complex) * Complex.I))
      volume Hminus Hplus ∧
    (‖∫ u in Hminus..Hplus, F ((-1 / 2 : Complex) + (u : Complex) * Complex.I)‖ /
      (2 * Real.pi) ≤ 1.632 * Real.log ((q : Real) * T) * Real.log T) ∧
    (‖∫ u in Hminus..Hplus, F ((-1 / 2 : Complex) + (u : Complex) * Complex.I)‖ /
      (2 * Real.pi) ≤ (1 / 100000 : Real) * t / T * L ^ (2 : Nat)) := by
  intro L T Hplus Hminus hp hm t htlo hthi
  exact actual_left_vertical_estimate hN hq hqUpper hchi hPrimitive hp hm htlo hthi

end LiuWang.Proof.LocalAnalyticBounds.LeftVertical.Consumer
