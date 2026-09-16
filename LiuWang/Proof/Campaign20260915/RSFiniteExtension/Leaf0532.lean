import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0531
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_12503 : PrimeGap 12497 12503 :=
  (primeGap_of_factors (ds := [2, 29, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12503 :
    (12503 : ℕ).Prime ∧ logScale (12503 : ℚ) = 13 ∧
      (94337238911 : ℤ) = ⌊logCenter (12503 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12503 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12503 : Reach 12503 123582706638360 168158637720 := by
  have hr := row_12503
  have hl := log_bounds hr.1
    (by change logScale (12503 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12497) (T := 123488369399449) (U := 168145188256)
    (by norm_num) (by norm_num) hr.1 gap_12503
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12497

theorem gap_12511 : PrimeGap 12503 12511 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12511 :
    (12511 : ℕ).Prime ∧ logScale (12511 : ℚ) = 13 ∧
      (94343635329 : ℤ) = ⌊logCenter (12511 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12511 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12511 : Reach 12511 123677050273689 168172079658 := by
  have hr := row_12511
  have hl := log_bounds hr.1
    (by change logScale (12511 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12503) (T := 123582706638360) (U := 168158637720)
    (by norm_num) (by norm_num) hr.1 gap_12511
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12503

theorem gap_12517 : PrimeGap 12511 12517 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12517 :
    (12517 : ℕ).Prime ∧ logScale (12517 : ℚ) = 13 ∧
      (94348429959 : ℤ) = ⌊logCenter (12517 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12517 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12517 : Reach 12517 123771398703648 168185516226 := by
  have hr := row_12517
  have hl := log_bounds hr.1
    (by change logScale (12517 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12511) (T := 123677050273689) (U := 168172079658)
    (by norm_num) (by norm_num) hr.1 gap_12517
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12511

theorem gap_12527 : PrimeGap 12517 12527 :=
  (primeGap_of_factors (ds := [2, 3, 2, 19, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12527 :
    (12527 : ℕ).Prime ∧ logScale (12527 : ℚ) = 13 ∧
      (94356415904 : ℤ) = ⌊logCenter (12527 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12527 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12527 : Reach 12527 123865755119552 168198943140 := by
  have hr := row_12527
  have hl := log_bounds hr.1
    (by change logScale (12527 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12517) (T := 123771398703648) (U := 168185516226)
    (by norm_num) (by norm_num) hr.1 gap_12527
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12517

theorem gap_12539 : PrimeGap 12527 12539 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 83, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12539 :
    (12539 : ℕ).Prime ∧ logScale (12539 : ℚ) = 13 ∧
      (94365990628 : ℤ) = ⌊logCenter (12539 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12539 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12539 : Reach 12539 123960121110180 168212358274 := by
  have hr := row_12539
  have hl := log_bounds hr.1
    (by change logScale (12539 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12527) (T := 123865755119552) (U := 168198943140)
    (by norm_num) (by norm_num) hr.1 gap_12539
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12527

theorem gap_12541 : PrimeGap 12539 12541 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_12541 :
    (12541 : ℕ).Prime ∧ logScale (12541 : ℚ) = 13 ∧
      (94367585524 : ℤ) = ⌊logCenter (12541 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12541 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12541 : Reach 12541 124054488695704 168225772338 := by
  have hr := row_12541
  have hl := log_bounds hr.1
    (by change logScale (12541 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12539) (T := 123960121110180) (U := 168212358274)
    (by norm_num) (by norm_num) hr.1 gap_12541
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12539

theorem gap_12547 : PrimeGap 12541 12547 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12547 :
    (12547 : ℕ).Prime ∧ logScale (12547 : ℚ) = 13 ∧
      (94372368687 : ℤ) = ⌊logCenter (12547 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12547 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12547 : Reach 12547 124148861064391 168239181056 := by
  have hr := row_12547
  have hl := log_bounds hr.1
    (by change logScale (12547 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12541) (T := 124054488695704) (U := 168225772338)
    (by norm_num) (by norm_num) hr.1 gap_12547
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12541

theorem gap_12553 : PrimeGap 12547 12553 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12553 :
    (12553 : ℕ).Prime ∧ logScale (12553 : ℚ) = 13 ∧
      (94377149564 : ℤ) = ⌊logCenter (12553 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12553 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12553 : Reach 12553 124243238213955 168252584433 := by
  have hr := row_12553
  have hl := log_bounds hr.1
    (by change logScale (12553 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12547) (T := 124148861064391) (U := 168239181056)
    (by norm_num) (by norm_num) hr.1 gap_12553
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12547

#print axioms reach_12553

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
