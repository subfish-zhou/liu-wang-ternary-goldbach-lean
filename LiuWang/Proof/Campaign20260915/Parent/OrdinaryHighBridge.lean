import LiuWang.Proof.Campaign20260915.Parent.HighConsumers
import LiuWang.Proof.Campaign20260915.MajorArc.OrdinaryConsumer
import LiuWang.Proof.Campaign20260915.MajorArc.ThirdHead
import LiuWang.Proof.Campaign20260915.MajorArc.RootAssembly

set_option autoImplicit false
noncomputable section
open MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.SingularSeries
open LiuWang.Proof.SourceRoute.MajorOrdinary

namespace LiuWang.Proof.Campaign20260915.Parent.OrdinaryHighBridge

open LiuWang.Proof.MultiZeroRepulsion
open LiuWang.Proof.Campaign20260915.MajorArc LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1
open LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536

/-- The ordinary consumer's strict lower endpoint is contained in the proved closed band. -/
theorem ordinary_high_le_closed_high {N q : ℕ} [NeZero q] :
    highWeightSum N q ≤ WeightedHighZeros.highSum N q := by
  classical
  unfold highWeightSum WeightedHighZeros.highSum WeightedHighZeros.bandSum
  apply Finset.sum_le_sum
  intro chi _
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro rho hr
    obtain ⟨hz, hpos, hlt, ht, hhalf⟩ :=
      CompleteExpansion.mem_zeroValues.mp (Finset.mem_filter.mp hr).1
    exact mem_bandValues.mpr ⟨hz, ⟨hpos, hlt, ht⟩, hhalf,
      (Finset.mem_filter.mp hr).2.le⟩
  · intro rho _ _
    exact mul_nonneg (Nat.cast_nonneg _)
      (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (abs_nonneg _))

theorem threeOddPrimes_of_low_counts_and_minor {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N)
    (hlow : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      lowWeightSum N q ≤ 0.0194 / sourceL N)
    (hT1 : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N →
      ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N),
        strictFamilyCount q (1 - 0.26213 / Real.log ((q : ℝ) * y)) y ≤ 4)
    (hT7 : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N →
      ∀ alpha y : ℝ, 1 / 2 ≤ alpha → alpha < 1 →
        max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
        (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hreal : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N →
      ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N),
        ∀ (chi : Character q) (rho : ℂ), rho ∈ DirichletZeroCount.zeroValues chi 0 y →
          1 - (1 / c1) / Real.log ((q : ℝ) * y) < rho.re → rho.im = 0)
    (hsecond :
      ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
        (0.4012 * (N : ℝ) / sourceL N) *
          ∫ alpha in M2 N, ‖S N alpha‖ ^ 2)
    (hthird :
      ‖∫ alpha in M3 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
        (0.5033 * (N : ℝ) / sourceL N) *
          ∫ alpha in M3 N, ‖S N alpha‖ ^ 2) :
    LiuWang.IsThreeOddPrimeSum N := by
  apply threeOddPrimes_of_low_high_and_minor hN hodd hlow _ hsecond hthird
  intro q inst hq
  have hq' : (q : ℝ) ≤ sourceP N :=
    ((mem_denominators (sourceP_pos (exp_2000_le_of_exp_3100_le hN)).le q).mp hq).2
  exact (ordinary_high_le_closed_high (N := N) (q := q)).trans
    (HighSums.highSum_original_of_T1_T7_near_one_real hN hq'
      (hT1 q hq') (hT7 q hq') (hreal q hq'))

#print axioms ordinary_high_le_closed_high
#print axioms threeOddPrimes_of_low_counts_and_minor

end LiuWang.Proof.Campaign20260915.Parent.OrdinaryHighBridge
