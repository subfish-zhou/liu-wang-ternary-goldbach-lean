import LiuWang.Proof.Campaign20260915.OriginalRegion.BoundaryPayment
import LiuWang.Proof.Campaign20260915.Parent.OriginalRegionConsumers

/-! Remove the actual ordinary low-sum input by an exhaustive strict-source split. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.MajorArcApproximation LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.SourceRoute.MajorException.Continuation
open LiuWang.Proof.Campaign20260915.MajorArc
open LiuWang.Proof.DirichletZeroCount LiuWang.Proof.MultiZeroRepulsion
open LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1
open LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536
open LiuWang.Proof.SingularSeries
open LiuWang.Proof.SourceRoute.MajorOrdinary

namespace LiuWang.Proof.Campaign20260915.OriginalRegion

theorem no_strict_source_denominator_low_weight {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hnone : ¬ ∃ d e, PaperSource N d e) :
    ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      lowWeightSum N q ≤ 0.0194 / sourceL N := by
  intro q _ hq
  exact no_strict_source_low_weight hN
    ((mem_denominators (sourceP_pos (exp_2000_le_of_exp_3100_le hN)).le q).mp hq).2 hnone

theorem threeOddPrimes_strict_source_split {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N)
    (h987 : ∀ d e, PaperSource N d e → 987 ≤ (d.modulus : ℝ))
    (hphi : ∀ d e, PaperSource N d e →
      (d.modulus : ℝ) / (d.modulus.totient : ℝ) ≤ nu d.modulus)
    (hT1 : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N →
      ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N),
        strictFamilyCount q (1 - 0.26213 / Real.log ((q : ℝ) * y)) y ≤ 4)
    (hT7 : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N →
      ∀ alpha y : ℝ, 1 / 2 ≤ alpha → alpha < 1 →
        max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
        (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hsecond :
      ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
        (0.4012 * (N : ℝ) / sourceL N) *
          ∫ alpha in M2 N, ‖S N alpha‖ ^ 2)
    (hthird :
      ‖∫ alpha in M3 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
        (0.5033 * (N : ℝ) / sourceL N) *
          ∫ alpha in M3 N, ‖S N alpha‖ ^ 2) : LiuWang.IsThreeOddPrimeSum N := by
  classical
  by_cases hex : ∃ d e, PaperSource N d e
  · obtain ⟨d, e, hd⟩ := hex
    exact Parent.OriginalRegionConsumers.threeOddPrimes_paper_region_paid hN hodd hd
      (h987 d e hd) (hphi d e hd) hT1 hT7 hsecond hthird
  · exact Parent.OriginalRegionConsumers.threeOddPrimes_ordinary_region_paid hN hodd
      (no_strict_source_denominator_low_weight hN hex) hT1 hT7 hsecond hthird

end LiuWang.Proof.Campaign20260915.OriginalRegion
