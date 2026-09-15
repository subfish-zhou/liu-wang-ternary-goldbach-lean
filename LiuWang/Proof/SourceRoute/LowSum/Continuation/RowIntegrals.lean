import LiuWang.Proof.SourceRoute.LowSum.Continuation.Counts

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.WeightedLowZeros LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.DirichletZeroCount
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation

theorem full_integral_eq {N q : ℕ} [NeZero q] (y : ℝ) {a b : ℝ}
    (ha : 1 / 2 ≤ a) (hab : a ≤ b) :
    (∫ alpha in a..b, kernel N alpha *
      countingFunction (fun chi : Character q => CompleteExpansion.zeroValues chi y)
        zeroMultiplicity alpha) =
      ∫ alpha in a..b, kernel N alpha * (familyCount q alpha y : ℝ) := by
  apply intervalIntegral.integral_congr
  intro alpha halpha
  rw [Set.uIcc_of_le hab] at halpha
  dsimp only
  rw [countingFunction_full y (ha.trans halpha.1)]

theorem subset_first_eight_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (Z : Character q → Finset ℂ)
    (hZ : ∀ chi, Z chi ⊆ CompleteExpansion.zeroValues chi (omegaCutoff N q)) :
    (∫ alpha in cap N 0.478..cap N 0.33,
      kernel N alpha * countingFunction Z zeroMultiplicity alpha) ≤ 3e-13 / sourceL N :=
  original_first_eight hN Z zeroMultiplicity
    (fun _ hi => subset_nine_rows hN hq Z hZ (by omega))

theorem subset_first_nine_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (Z : Character q → Finset ℂ)
    (hZ : ∀ chi, Z chi ⊆ CompleteExpansion.zeroValues chi (omegaCutoff N q)) :
    (∫ alpha in cap N 0.478..cap N 0.32,
      kernel N alpha * countingFunction Z zeroMultiplicity alpha) ≤ 6e-13 / sourceL N :=
  original_first_nine hN Z zeroMultiplicity (fun _ hi => subset_nine_rows hN hq Z hZ hi)

theorem family_first_eight_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (∫ alpha in cap N 0.478..cap N 0.33,
      kernel N alpha * (familyCount q alpha (omegaCutoff N q) : ℝ)) ≤ 3e-13 / sourceL N := by
  have h := subset_first_eight_paid hN hq
    (fun chi : Character q => CompleteExpansion.zeroValues chi (omegaCutoff N q)) (fun _ _ hr => hr)
  rw [full_integral_eq _ (by linarith [cap_ge_098 hN (by norm_num : (0.478 : ℝ) ≤ 0.478)])
    (cap_order hN (by norm_num))] at h
  exact h

theorem family_first_nine_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (∫ alpha in cap N 0.478..cap N 0.32,
      kernel N alpha * (familyCount q alpha (omegaCutoff N q) : ℝ)) ≤ 6e-13 / sourceL N := by
  have h := subset_first_nine_paid hN hq
    (fun chi : Character q => CompleteExpansion.zeroValues chi (omegaCutoff N q)) (fun _ _ hr => hr)
  rw [full_integral_eq _ (by linarith [cap_ge_098 hN (by norm_num : (0.478 : ℝ) ≤ 0.478)])
    (cap_order hN (by norm_num))] at h
  exact h

theorem retained_first_eight_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (d : PrimitiveQuadraticDatum) (e : ℂ) :
    (∫ alpha in cap N 0.478..cap N 0.33,
      kernel N alpha * (retainedCount q alpha (omegaCutoff N q) d e : ℝ)) ≤ 3e-13 / sourceL N := by
  simpa only [countingFunction_retained] using
    subset_first_eight_paid hN hq
      (fun chi : Character q => retainedValues chi (omegaCutoff N q) d e)
      (fun _ => Finset.filter_subset _ _)

theorem retained_first_nine_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (d : PrimitiveQuadraticDatum) (e : ℂ) :
    (∫ alpha in cap N 0.478..cap N 0.32,
      kernel N alpha * (retainedCount q alpha (omegaCutoff N q) d e : ℝ)) ≤ 6e-13 / sourceL N := by
  simpa only [countingFunction_retained] using
    subset_first_nine_paid hN hq
      (fun chi : Character q => retainedValues chi (omegaCutoff N q) d e)
      (fun _ => Finset.filter_subset _ _)

theorem retained_213_of_zero {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (d : PrimitiveQuadraticDatum) (e : ℂ)
    (hz : retainedCount q (cap N 0.32) (omegaCutoff N q) d e = 0) :
    (∫ alpha in bulkCap N..1,
      kernel N alpha * (retainedCount q alpha (omegaCutoff N q) d e : ℝ)) ≤ 6e-13 / sourceL N := by
  have h := original_213_from_counts hN
    (fun chi : Character q => retainedValues chi (omegaCutoff N q) d e) zeroMultiplicity
    (fun i hi => subset_nine_rows hN hq _ (fun _ => Finset.filter_subset _ _) hi)
    (by rw [countingFunction_retained, hz, Nat.cast_zero])
  simpa only [countingFunction_retained] using h

end LiuWang.Proof.SourceRoute.LowSum.Continuation
