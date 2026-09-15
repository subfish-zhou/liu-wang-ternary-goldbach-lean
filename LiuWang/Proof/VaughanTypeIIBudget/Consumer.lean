import LiuWang.Proof.VaughanTypeIIBudget.Main
import LiuWang.Proof.ParameterComparisons.VaughanRange

/-!
实际指数和的条件接口：唯一未付桥是逐真实二进块的实际行界。
既约逼近和第一类估计使用同一 N、α、a、q、θ；不假定最终 S4 或 S 的估计。
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.VaughanTypeIIBudget

open Interfaces Parameters VaughanTypeII Finset
open scoped BigOperators

theorem conditional_actual_typeII_le {N q : ℕ} {α : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) (hqU : (q : ℝ) ≤ sourceQ N)
    (hrows : ∀ j < dyadicCount N,
      rowMax N (dyadicScale N j) α ≤ scalarRowBudget N (dyadicScale N j) q) :
    ‖VaughanTypeI.sourceS4 N α‖ ≤
      0.1526 * termA N q + 2.5179 * termB N + 0.0872 * termC N q := by
  apply (actual_typeII_bound hN α).trans
  apply le_trans (b := scalarDyadicBudget N q) ?_ (scalarDyadicBudget_le_strong hN hqL hqU)
  unfold scalarDyadicBudget kappa
  apply mul_le_mul_of_nonneg_left
  · exact sum_le_sum fun j hj => Real.sqrt_le_sqrt (hrows j (mem_range.mp hj))
  · have hlog := (log_Y_bounds hN).1
    positivity

/-- 条件的实际 Vaughan 三项强界；行界仍是明确未付输入。 -/
theorem conditional_sourceS_le_strong {N a q : ℕ} {α θ : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) (hqU : (q : ℝ) ≤ sourceQ N)
    (hi : sourceIndex a q) (hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2)
    (hrows : ∀ j < dyadicCount N,
      rowMax N (dyadicScale N j) α ≤ scalarRowBudget N (dyadicScale N j) q) :
    ‖S N α‖ ≤ 0.1939 * termA N q + 3.318 * termB N + 0.0883 * termC N q := by
  have hI : ‖S N α - VaughanTypeI.sourceS4 N α‖ ≤
      0.0413 * termA N q + 0.8001 * termB N + 0.0011 * termC N q := by
    simpa only [termA, termB, termC, neg_div, mul_assoc] using
      VaughanTypeI.norm_sourceS_sub_actualS4_le hN hqL hqU hi hθ hα
  have hII := conditional_actual_typeII_le hN hqL hqU hrows
  have htriangle : ‖S N α‖ ≤
      ‖S N α - VaughanTypeI.sourceS4 N α‖ + ‖VaughanTypeI.sourceS4 N α‖ := by
    simpa only [sub_add_cancel] using
      norm_add_le (S N α - VaughanTypeI.sourceS4 N α) (VaughanTypeI.sourceS4 N α)
  linarith

/-- 原三项系数的条件实际消费者。 -/
theorem conditional_sourceS_le_vaughan {N a q : ℕ} {α θ : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) (hqU : (q : ℝ) ≤ sourceQ N)
    (hi : sourceIndex a q) (hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2)
    (hrows : ∀ j < dyadicCount N,
      rowMax N (dyadicScale N j) α ≤ scalarRowBudget N (dyadicScale N j) q) :
    ‖S N α‖ ≤
      (0.28 : ℝ) * (N : ℝ) * (q : ℝ) ^ ((-1 : ℝ) / 2) * sourceL N ^ (2 : ℕ) +
      4 * (N : ℝ) ^ ((4 : ℝ) / 5) * sourceL N ^ ((7 : ℝ) / 5) +
      (0.09 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2) * (q : ℝ) ^ ((1 : ℝ) / 2) *
        sourceL N ^ ((5 : ℝ) / 2) := by
  have ht := terms_nonneg hN q
  apply (conditional_sourceS_le_strong hN hqL hqU hi hθ hα hrows).trans
  calc
    _ ≤ 0.28 * termA N q + 4 * termB N + 0.09 * termC N q := by
      exact add_le_add
        (add_le_add (mul_le_mul_of_nonneg_right (by norm_num) ht.1)
          (mul_le_mul_of_nonneg_right (by norm_num) ht.2.1))
        (mul_le_mul_of_nonneg_right (by norm_num) ht.2.2)
    _ = _ := by unfold termA termB termC; ring

/-- 复用已验全区间预算，保留 0.294 的余量。 -/
theorem conditional_sourceS_le_margin {N a q : ℕ} {α θ : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) (hqU : (q : ℝ) ≤ sourceQ N)
    (hi : sourceIndex a q) (hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2)
    (hrows : ∀ j < dyadicCount N,
      rowMax N (dyadicScale N j) α ≤ scalarRowBudget N (dyadicScale N j) q) :
    ‖S N α‖ ≤ (0.294 : ℝ) * (N : ℝ) / sourceL N :=
  (conditional_sourceS_le_vaughan hN hqL hqU hi hθ hα hrows).trans
    (ParameterComparisons.vaughan_scalar_range_margin hN hqL hqU)

/-- 只有父级接入实际行生产者后，才能去掉 hrows。 -/
theorem conditional_sourceS_le_three_tenths {N a q : ℕ} {α θ : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) (hqU : (q : ℝ) ≤ sourceQ N)
    (hi : sourceIndex a q) (hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2)
    (hrows : ∀ j < dyadicCount N,
      rowMax N (dyadicScale N j) α ≤ scalarRowBudget N (dyadicScale N j) q) :
    ‖S N α‖ ≤ (0.3 : ℝ) * (N : ℝ) / sourceL N :=
  (conditional_sourceS_le_vaughan hN hqL hqU hi hθ hα hrows).trans
    (ParameterComparisons.vaughan_scalar_range_nat hN hqL hqU)

end LiuWang.Proof.VaughanTypeIIBudget
