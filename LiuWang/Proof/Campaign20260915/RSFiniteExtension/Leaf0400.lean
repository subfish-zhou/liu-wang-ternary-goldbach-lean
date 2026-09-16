import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block039
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_9419 : PrimeGap 9413 9419 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9419 :
    (9419 : ℕ).Prime ∧ logScale (9419 : ℚ) = 13 ∧
      (91504842014 : ℤ) = ⌊logCenter (9419 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9419 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9419 : Reach 9419 93085138368983 163163988028 := by
  have hr := row_9419
  have hl := log_bounds hr.1
    (by change logScale (9419 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9413) (T := 92993633526969) (U := 163146665171)
    (by norm_num) (by norm_num) hr.1 gap_9419
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9413

theorem gap_9421 : PrimeGap 9419 9421 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_9421 :
    (9421 : ℕ).Prime ∧ logScale (9421 : ℚ) = 13 ∧
      (91506965156 : ℤ) = ⌊logCenter (9421 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9421 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9421 : Reach 9421 93176645334139 163181309046 := by
  have hr := row_9421
  have hl := log_bounds hr.1
    (by change logScale (9421 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9419) (T := 93085138368983) (U := 163163988028)
    (by norm_num) (by norm_num) hr.1 gap_9421
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9419

theorem gap_9431 : PrimeGap 9421 9431 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9431 :
    (9431 : ℕ).Prime ∧ logScale (9431 : ℚ) = 13 ∧
      (91517574111 : ℤ) = ⌊logCenter (9431 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9431 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9431 : Reach 9431 93268162908250 163198613533 := by
  have hr := row_9431
  have hl := log_bounds hr.1
    (by change logScale (9431 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9421) (T := 93176645334139) (U := 163181309046)
    (by norm_num) (by norm_num) hr.1 gap_9431
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9421

theorem gap_9433 : PrimeGap 9431 9433 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_9433 :
    (9433 : ℕ).Prime ∧ logScale (9433 : ℚ) = 13 ∧
      (91519694552 : ℤ) = ⌊logCenter (9433 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9433 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9433 : Reach 9433 93359682602802 163215916185 := by
  have hr := row_9433
  have hl := log_bounds hr.1
    (by change logScale (9433 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9431) (T := 93268162908250) (U := 163198613533)
    (by norm_num) (by norm_num) hr.1 gap_9433
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9431

theorem gap_9437 : PrimeGap 9433 9437 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9437 :
    (9437 : ℕ).Prime ∧ logScale (9437 : ℚ) = 13 ∧
      (91523934086 : ℤ) = ⌊logCenter (9437 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9437 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9437 : Reach 9437 93451206536888 163233213336 := by
  have hr := row_9437
  have hl := log_bounds hr.1
    (by change logScale (9437 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9433) (T := 93359682602802) (U := 163215916185)
    (by norm_num) (by norm_num) hr.1 gap_9437
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9433

theorem gap_9439 : PrimeGap 9437 9439 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_9439 :
    (9439 : ℕ).Prime ∧ logScale (9439 : ℚ) = 13 ∧
      (91526053179 : ℤ) = ⌊logCenter (9439 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9439 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9439 : Reach 9439 93542732590067 163250508655 := by
  have hr := row_9439
  have hl := log_bounds hr.1
    (by change logScale (9439 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9437) (T := 93451206536888) (U := 163233213336)
    (by norm_num) (by norm_num) hr.1 gap_9439
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9437

theorem gap_9461 : PrimeGap 9439 9461 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9461 :
    (9461 : ℕ).Prime ∧ logScale (9461 : ℚ) = 13 ∧
      (91549333613 : ℤ) = ⌊logCenter (9461 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9461 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9461 : Reach 9461 93634281923680 163267765580 := by
  have hr := row_9461
  have hl := log_bounds hr.1
    (by change logScale (9461 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9439) (T := 93542732590067) (U := 163250508655)
    (by norm_num) (by norm_num) hr.1 gap_9461
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9439

theorem gap_9463 : PrimeGap 9461 9463 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_9463 :
    (9463 : ℕ).Prime ∧ logScale (9463 : ℚ) = 13 ∧
      (91551447331 : ℤ) = ⌊logCenter (9463 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9463 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9463 : Reach 9463 93725833371011 163285020681 := by
  have hr := row_9463
  have hl := log_bounds hr.1
    (by change logScale (9463 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9461) (T := 93634281923680) (U := 163267765580)
    (by norm_num) (by norm_num) hr.1 gap_9463
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9461

#print axioms reach_9463

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
