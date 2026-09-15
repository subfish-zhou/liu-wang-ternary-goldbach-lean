import LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate.Main

/-!
# 原始域与字面被积函数的同高度消费者

不预设任何对数导数或积分估计。拆开生产者的同一对见证，运输到实际
`LFunction` 零点，并在字面 `F` 上保留可积性与双边总界。
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate.Consumer

theorem actual_source_horizontal_budget
    {N q : Nat} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : Real))
    (hq : 3 ≤ q) (hqUpper : (q : Real) ≤ (Real.log (N : Real)) ^ (6 : Nat))
    {chi : DirichletCharacter Complex q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {t : Real} (htlo : (N : Real) / 1000 ≤ t) (hthi : t ≤ (N : Real)) :
    let T : Real := (Real.log (N : Real)) ^ (15 : Nat)
    let b : Real := 1 + 1 / Real.log (N : Real)
    let F : Complex → Complex := fun s =>
      (-logDeriv chi.LFunction s) * ((t : Complex) ^ s - (2.5 : Complex) ^ s) / s
    ∃ Hplus Hminus : Real,
      |Hplus - T| ≤ 1 ∧ |Hminus + T| ≤ 1 ∧
      (∀ p : CompletedZeroIndex chi,
        (1.7769 * Real.log ((q : Real) * T))⁻¹ ≤
          |(completedZeroValue p).im - Hplus| ∧
        (1.7769 * Real.log ((q : Real) * T))⁻¹ ≤
          |(completedZeroValue p).im - Hminus|) ∧
      (∀ rho : Complex, 0 < rho.re → chi.LFunction rho = 0 →
        (1.7769 * Real.log ((q : Real) * T))⁻¹ ≤ |rho.im - Hplus| ∧
        (1.7769 * Real.log ((q : Real) * T))⁻¹ ≤ |rho.im - Hminus|) ∧
      (∀ H ∈ ({Hplus, Hminus} : Set Real),
        (∀ σ ∈ Set.Icc (-(1 : Real) / 2) b,
          chi.LFunction ((σ : Complex) + (H : Complex) * Complex.I) ≠ 0 ∧
          ‖logDeriv chi.LFunction ((σ : Complex) + (H : Complex) * Complex.I)‖ ≤
            10 * (Real.log ((q : Real) * T)) ^ 2) ∧
        IntervalIntegrable (fun σ : Real => F ((σ : Complex) + (H : Complex) * Complex.I))
          volume (-(1 : Real) / 2) b) ∧
      (‖∫ σ in (-(1 : Real) / 2)..b, F ((σ : Complex) + (Hplus : Complex) * Complex.I)‖ +
        ‖∫ σ in (-(1 : Real) / 2)..b, F ((σ : Complex) + (Hminus : Complex) * Complex.I)‖) /
          (2 * Real.pi) ≤ 0.0014 * t / T * (Real.log ((q : Real) * T)) ^ 2 := by
  obtain ⟨Hp, Hm, hp, hm, hsep, hdata, hbudget⟩ :=
    exists_source_rectangle_horizontal_estimate hN hq hqUpper hchi hPrimitive htlo hthi
  refine ⟨Hp, Hm, hp, hm, hsep, ?_, ?_, hbudget⟩
  · intro rho hre hz
    exact ⟨LFunction_zero_separated_of_index hchi hPrimitive (fun p => (hsep p).1) hre hz,
      LFunction_zero_separated_of_index hchi hPrimitive (fun p => (hsep p).2) hre hz⟩
  · intro H hH
    exact ⟨(hdata H hH).1, (hdata H hH).2.1⟩

end LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate.Consumer
