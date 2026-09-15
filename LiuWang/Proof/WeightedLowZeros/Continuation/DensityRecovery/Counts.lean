import LiuWang.Proof.NearOneDensity.Continuation.CountInterface
import LiuWang.Proof.WeightedLowZeros.Continuation.DensityNumerics

/-! # Accepted effective density rows on the literal low-height ordinary zeros -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.NearOneDensity
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.WeightedLowZeros.Continuation.DensityRecovery

theorem lowScale_effective {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    100000000000 ≤ lowScale N := by
  have hL := sourceL_ge_3100 hN
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3100) hL 3
  change 100000000000 ≤ 3.36 * sourceL N ^ 3
  norm_num at hp
  linarith

theorem low_height_product {N q : ℕ} [NeZero q] (hq : (q : ℝ) ≤ sourceP N) :
    (q : ℝ) * max 1 (omegaCutoff N q) = lowScale N := by
  have hy : 1 ≤ omegaCutoff N q := by linarith [omegaCutoff_ge (NeZero.pos q) hq]
  rw [max_eq_right hy]
  unfold omegaCutoff lowScale
  exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (NeZero.ne q))

theorem familyCount_low_row (r : DensityRow) {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {alpha : ℝ} (ha : cap N (rowLambda r) ≤ alpha) :
    familyCount q alpha (omegaCutoff N q) ≤ rowBound r :=
  NearOneDensity.Continuation.familyCount_row_tail r (lowScale_effective hN)
    (low_height_product hq).le ha

theorem familyCount_bulk_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    familyCount q (bulkCap N) (omegaCutoff N q) ≤ 14000 := by
  simpa only [rowBound, rowMultiplicity, rowSelectedBound, Nat.reduceMul] using
    familyCount_low_row .r0478 hN hq (alpha := bulkCap N) le_rfl

theorem familyCount_033_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    familyCount q (cap N 0.33) (omegaCutoff N q) ≤ 13 := by
  simpa only [rowBound, rowMultiplicity, rowSelectedBound, Nat.reduceMul] using
    familyCount_low_row .r033 hN hq (alpha := cap N 0.33) le_rfl

theorem cutCount_low_row (r : DensityRow) {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (Z : Character q → Finset ℂ)
    (hZ : ∀ chi, Z chi ⊆ CompleteExpansion.zeroValues chi (omegaCutoff N q))
    {alpha : ℝ} (ha : cap N (rowLambda r) ≤ alpha) :
    cutCount q Z alpha ≤ rowBound r := by
  apply (cutCount_mono Z (fun chi => CompleteExpansion.zeroValues chi (omegaCutoff N q))
    hZ alpha).trans
  exact NearOneDensity.Continuation.complete_tail_count_row r (lowScale_effective hN)
    (low_height_product hq).le ha

theorem retainedCount_low_row (r : DensityRow) {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (d : PrimitiveQuadraticDatum) (e : ℂ)
    {alpha : ℝ} (ha : cap N (rowLambda r) ≤ alpha) :
    retainedCount q alpha (omegaCutoff N q) d e ≤ rowBound r :=
  cutCount_low_row r hN hq (fun chi => retainedValues chi (omegaCutoff N q) d e)
    (fun _ => Finset.filter_subset _ _) ha

theorem retainedCount_bulk_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (d : PrimitiveQuadraticDatum) (e : ℂ) :
    retainedCount q (bulkCap N) (omegaCutoff N q) d e ≤ 14000 := by
  simpa only [rowBound, rowMultiplicity, rowSelectedBound, Nat.reduceMul] using
    retainedCount_low_row .r0478 hN hq d e (alpha := bulkCap N) le_rfl

theorem retainedCount_033_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (d : PrimitiveQuadraticDatum) (e : ℂ) :
    retainedCount q (cap N 0.33) (omegaCutoff N q) d e ≤ 13 := by
  simpa only [rowBound, rowMultiplicity, rowSelectedBound, Nat.reduceMul] using
    retainedCount_low_row .r033 hN hq d e (alpha := cap N 0.33) le_rfl

end LiuWang.Proof.WeightedLowZeros.Continuation.DensityRecovery
