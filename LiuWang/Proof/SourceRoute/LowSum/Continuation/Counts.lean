import LiuWang.Proof.SourceRoute.LowSum.SourceRows
import LiuWang.Proof.NearOneDensity.Continuation.CountInterface

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.WeightedLowZeros LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.DirichletZeroCount LiuWang.Proof.NearOneDensity
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation

theorem lowScale_effective {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    100000000000 ≤ lowScale N := by
  have hL := sourceL_ge_3100 hN
  have hc := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3100) hL 3
  change 100000000000 ≤ 3.36 * sourceL N ^ 3
  linarith

theorem omega_eq_lowScale_div (N q : ℕ) :
    omegaCutoff N q = lowScale N / q := rfl

theorem low_height_ge {N q : ℕ} [NeZero q] (hq : (q : ℝ) ≤ sourceP N) :
    3.36 ≤ omegaCutoff N q :=
  omegaCutoff_ge (NeZero.pos q) hq

theorem low_height_product {N q : ℕ} [NeZero q] (hq : (q : ℝ) ≤ sourceP N) :
    (q : ℝ) * max 1 (omegaCutoff N q) = lowScale N := by
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  rw [max_eq_right (by linarith [low_height_ge hq]), omega_eq_lowScale_div]
  exact mul_div_cancel₀ _ hq0

def densityRow : ℕ → DensityRow
  | 0 => .r0478 | 1 => .r0475 | 2 => .r047 | 3 => .r046 | 4 => .r045
  | 5 => .r042 | 6 => .r039 | 7 => .r036 | _ => .r033

theorem densityRow_correspondence {i : ℕ} (hi : i < 9) :
    rowLambda (densityRow i) = breakpoint i ∧ rowBound (densityRow i) = rowCount i := by
  interval_cases i <;>
    norm_num [densityRow, rowLambda, rowBound, rowMultiplicity, rowSelectedBound, breakpoint, rowCount]

theorem familyCount_low_row (r : DensityRow) {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {alpha : ℝ} (ha : cap N (rowLambda r) ≤ alpha) :
    familyCount q alpha (omegaCutoff N q) ≤ rowBound r :=
  NearOneDensity.Continuation.familyCount_row_tail r
    (lowScale_effective hN) (low_height_product hq).le ha

theorem family_nine_rows {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {i : ℕ} (hi : i < 9) :
    familyCount q (cap N (breakpoint i)) (omegaCutoff N q) ≤ rowCount i := by
  obtain ⟨hl, hb⟩ := densityRow_correspondence hi
  rw [← hl, ← hb]
  exact familyCount_low_row _ hN hq le_rfl

theorem complete_nine_rows {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {i : ℕ} (hi : i < 9) :
    (∑ chi : Character q,
      ∑ rho ∈ (CompleteExpansion.zeroValues chi (omegaCutoff N q)).filter
        (fun rho => cap N (breakpoint i) ≤ rho.re),
          zeroMultiplicity chi rho) ≤ rowCount i := by
  obtain ⟨hl, hb⟩ := densityRow_correspondence hi
  rw [← hl, ← hb]
  exact NearOneDensity.Continuation.complete_tail_count_row _
    (lowScale_effective hN) (low_height_product hq).le le_rfl

theorem retained_nine_rows {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (d : PrimitiveQuadraticDatum) (e : ℂ) {i : ℕ} (hi : i < 9) :
    retainedCount q (cap N (breakpoint i)) (omegaCutoff N q) d e ≤ rowCount i := by
  apply le_trans _ (complete_nine_rows hN hq hi)
  unfold retainedCount
  apply Finset.sum_le_sum
  intro chi _
  exact Finset.sum_le_sum_of_subset
    (Finset.filter_subset_filter _ (Finset.filter_subset _ _))

theorem countingFunction_retained {q : ℕ} [NeZero q]
    (y alpha : ℝ) (d : PrimitiveQuadraticDatum) (e : ℂ) :
    countingFunction (fun chi : Character q => retainedValues chi y d e)
      zeroMultiplicity alpha = (retainedCount q alpha y d e : ℝ) := by
  simp only [countingFunction, retainedCount, Nat.cast_sum]

theorem subset_nine_rows {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (Z : Character q → Finset ℂ)
    (hZ : ∀ chi, Z chi ⊆ CompleteExpansion.zeroValues chi (omegaCutoff N q))
    {i : ℕ} (hi : i < 9) :
    countingFunction Z zeroMultiplicity (cap N (breakpoint i)) ≤ rowCount i := by
  have hhalf : 1 / 2 ≤ cap N (breakpoint i) := by
    linarith [cap_ge_098 hN (row_parameters hi).2.2]
  apply (countingFunction_le_full hhalf Z hZ).trans
  exact_mod_cast family_nine_rows hN hq hi

theorem family_count_033 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    familyCount q (cap N 0.33) (omegaCutoff N q) ≤ 13 := by
  simpa only [breakpoint, rowCount] using
    (family_nine_rows hN hq (i := 8) (by norm_num))

end LiuWang.Proof.SourceRoute.LowSum.Continuation
