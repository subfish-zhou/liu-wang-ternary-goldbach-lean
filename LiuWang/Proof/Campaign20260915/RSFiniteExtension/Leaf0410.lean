import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block040
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_9629 : PrimeGap 9623 9629 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9629 :
    (9629 : ℕ).Prime ∧ logScale (9629 : ℚ) = 13 ∧
      (91725346538 : ℤ) = ⌊logCenter (9629 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9629 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9629 : Reach 9629 95283688705026 163576092619 := by
  have hr := row_9629
  have hl := log_bounds hr.1
    (by change logScale (9629 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9623) (T := 95191963358488) (U := 163559104760)
    (by norm_num) (by norm_num) hr.1 gap_9629
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9623

theorem gap_9631 : PrimeGap 9629 9631 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_9631 :
    (9631 : ℕ).Prime ∧ logScale (9631 : ℚ) = 13 ∧
      (91727423381 : ℤ) = ⌊logCenter (9631 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9631 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9631 : Reach 9631 95375416128407 163593078714 := by
  have hr := row_9631
  have hl := log_bounds hr.1
    (by change logScale (9631 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9629) (T := 95283688705026) (U := 163576092619)
    (by norm_num) (by norm_num) hr.1 gap_9631
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9629

theorem gap_9643 : PrimeGap 9631 9643 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 23, 2, 3, 2, 31, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9643 :
    (9643 : ℕ).Prime ∧ logScale (9643 : ℚ) = 13 ∧
      (91739875391 : ℤ) = ⌊logCenter (9643 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9643 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9643 : Reach 9643 95467156003798 163610045431 := by
  have hr := row_9643
  have hl := log_bounds hr.1
    (by change logScale (9643 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9631) (T := 95375416128407) (U := 163593078714)
    (by norm_num) (by norm_num) hr.1 gap_9643
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9631

theorem gap_9649 : PrimeGap 9643 9649 :=
  (primeGap_of_factors (ds := [2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9649 :
    (9649 : ℕ).Prime ∧ logScale (9649 : ℚ) = 13 ∧
      (91746095586 : ℤ) = ⌊logCenter (9649 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9649 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9649 : Reach 9649 95558902099384 163627003355 := by
  have hr := row_9649
  have hl := log_bounds hr.1
    (by change logScale (9649 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9643) (T := 95467156003798) (U := 163610045431)
    (by norm_num) (by norm_num) hr.1 gap_9649
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9643

theorem gap_9661 : PrimeGap 9649 9661 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9661 :
    (9661 : ℕ).Prime ∧ logScale (9661 : ℚ) = 13 ∧
      (91758524381 : ℤ) = ⌊logCenter (9661 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9661 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9661 : Reach 9661 95650660623765 163643941969 := by
  have hr := row_9661
  have hl := log_bounds hr.1
    (by change logScale (9661 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9649) (T := 95558902099384) (U := 163627003355)
    (by norm_num) (by norm_num) hr.1 gap_9661
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9649

theorem gap_9677 : PrimeGap 9661 9677 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 7, 2, 3, 2, 19, 2, 17, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9677 :
    (9677 : ℕ).Prime ∧ logScale (9677 : ℚ) = 13 ∧
      (91775072115 : ℤ) = ⌊logCenter (9677 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9677 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9677 : Reach 9677 95742435695880 163660854324 := by
  have hr := row_9677
  have hl := log_bounds hr.1
    (by change logScale (9677 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9661) (T := 95650660623765) (U := 163643941969)
    (by norm_num) (by norm_num) hr.1 gap_9677
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9661

theorem gap_9679 : PrimeGap 9677 9679 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_9679 :
    (9679 : ℕ).Prime ∧ logScale (9679 : ℚ) = 13 ∧
      (91777138657 : ℤ) = ⌊logCenter (9679 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9679 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9679 : Reach 9679 95834212834537 163677764931 := by
  have hr := row_9679
  have hl := log_bounds hr.1
    (by change logScale (9679 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9677) (T := 95742435695880) (U := 163660854324)
    (by norm_num) (by norm_num) hr.1 gap_9679
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9677

theorem gap_9689 : PrimeGap 9679 9689 :=
  (primeGap_of_factors (ds := [2, 3, 2, 23, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9689 :
    (9689 : ℕ).Prime ∧ logScale (9689 : ℚ) = 13 ∧
      (91787464970 : ℤ) = ⌊logCenter (9689 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9689 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9689 : Reach 9689 95926000299507 163694659829 := by
  have hr := row_9689
  have hl := log_bounds hr.1
    (by change logScale (9689 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9679) (T := 95834212834537) (U := 163677764931)
    (by norm_num) (by norm_num) hr.1 gap_9689
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9679

#print axioms reach_9689

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
