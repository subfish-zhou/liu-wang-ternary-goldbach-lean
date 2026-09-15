import LiuWang.Proof.LocalAnalyticBounds.LeftVertical.LowBudget

/-!
# 低实部居中零点贡献的原域消费者

精确有限重数索引先于全部实数端点选定。保留 `2.5` 补偿项；
不声称已运输 Perron 留数、固定高度截断或例外零点去中心化。
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.LocalAnalyticBounds.LeftVertical.Consumer

theorem actual_source_low_zero_budget
    {N q : Nat} [NeZero q] (hN : Real.exp 2000 ≤ (N : Real))
    (hq : 3 ≤ q) (hqUpper : (q : Real) ≤ (Real.log (N : Real)) ^ (6 : Nat))
    {chi : DirichletCharacter Complex q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) :
    let L : Real := Real.log (N : Real)
    let T : Real := L ^ (15 : Nat)
    ∃ S : Finset (CompletedZeroIndex chi),
      (∀ p : CompletedZeroIndex chi, p ∈ S ↔
        0 < (completedZeroValue p).re ∧ (completedZeroValue p).re < (1 : Real) / 2 ∧
          |(completedZeroValue p).im| ≤ T + 1) ∧
      ((S.card : Real) ≤ ((T + 1) ^ 2 + 4) * (Real.log q / 2 + 15 / 2)) ∧
      ∀ t : Real, (N : Real) / 1000 ≤ t → t ≤ (N : Real) →
        (∀ p ∈ S,
          IntervalIntegrable (fun x : Real => (x : Complex) ^ (completedZeroValue p - 1))
            volume (2.5 : Real) t ∧
          (((t : Complex) ^ completedZeroValue p - (2.5 : Complex) ^ completedZeroValue p) /
            completedZeroValue p =
              ∫ x : Real in (2.5 : Real)..t, (x : Complex) ^ (completedZeroValue p - 1)) ∧
          ‖((t : Complex) ^ completedZeroValue p - (2.5 : Complex) ^ completedZeroValue p) /
            completedZeroValue p‖ ≤ 2 * Real.sqrt t) ∧
        ‖∑ p ∈ S,
          (((t : Complex) ^ completedZeroValue p - (2.5 : Complex) ^ completedZeroValue p) /
            completedZeroValue p)‖ ≤ (1 / 100000 : Real) * t / T * L ^ (2 : Nat) := by
  intro L T
  refine ⟨lowZeroFinset hchi hPrimitive (T + 1), ?_,
    card_lowZeroFinset_le hchi hPrimitive (T + 1), ?_⟩
  · intro p
    simpa only [Set.mem_Ioo, and_assoc] using mem_lowZeroFinset hchi hPrimitive (T + 1) p
  · intro t htlo hthi
    obtain ⟨_, ht, _⟩ := HorizontalEstimate.source_horizontal_parameters hN htlo hthi
    refine ⟨?_, norm_lowZero_centered_sum_source_le hN hq hqUpper hchi hPrimitive htlo hthi⟩
    intro p hp
    have hr := ((mem_lowZeroFinset hchi hPrimitive (T + 1) p).mp hp).1
    refine ⟨intervalIntegral.intervalIntegrable_cpow' ?_,
      real_centered_kernel_eq_integral hr.1,
      norm_real_centered_kernel_low_re_le (by linarith : 2.5 ≤ t) hr.1 hr.2.le⟩
    simp only [Complex.sub_re, Complex.one_re]
    linarith [hr.1]

end LiuWang.Proof.LocalAnalyticBounds.LeftVertical.Consumer
