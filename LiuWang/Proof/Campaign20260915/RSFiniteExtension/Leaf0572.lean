import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0571
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_13399 : PrimeGap 13397 13399 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_13399 :
    (13399 : ℕ).Prime ∧ logScale (13399 : ℚ) = 13 ∧
      (95029353529 : ℤ) = ⌊logCenter (13399 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13399 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13399 : Reach 13399 132671911969574 169411317998 := by
  have hr := row_13399
  have hl := log_bounds hr.1
    (by change logScale (13399 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13397) (T := 132576882616045) (U := 169398674418)
    (by norm_num) (by norm_num) hr.1 gap_13399
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13397

theorem gap_13411 : PrimeGap 13399 13411 :=
  (primeGap_of_factors (ds := [2, 3, 2, 13, 2, 5, 2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13411 :
    (13411 : ℕ).Prime ∧ logScale (13411 : ℚ) = 13 ∧
      (95038305413 : ℤ) = ⌊logCenter (13411 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13411 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13411 : Reach 13411 132766950274987 169423951206 := by
  have hr := row_13411
  have hl := log_bounds hr.1
    (by change logScale (13411 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13399) (T := 132671911969574) (U := 169411317998)
    (by norm_num) (by norm_num) hr.1 gap_13411
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13399

theorem gap_13417 : PrimeGap 13411 13417 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13417 :
    (13417 : ℕ).Prime ∧ logScale (13417 : ℚ) = 13 ∧
      (95042778352 : ℤ) = ⌊logCenter (13417 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13417 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13417 : Reach 13417 132861993053339 169436579706 := by
  have hr := row_13417
  have hl := log_bounds hr.1
    (by change logScale (13417 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13411) (T := 132766950274987) (U := 169423951206)
    (by norm_num) (by norm_num) hr.1 gap_13417
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13411

theorem gap_13421 : PrimeGap 13417 13421 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13421 :
    (13421 : ℕ).Prime ∧ logScale (13421 : ℚ) = 13 ∧
      (95045759200 : ℤ) = ⌊logCenter (13421 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13421 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13421 : Reach 13421 132957038812539 169449205383 := by
  have hr := row_13421
  have hl := log_bounds hr.1
    (by change logScale (13421 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13417) (T := 132861993053339) (U := 169436579706)
    (by norm_num) (by norm_num) hr.1 gap_13421
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13417

theorem gap_13441 : PrimeGap 13421 13441 :=
  (primeGap_of_factors (ds := [2, 31, 2, 3, 2, 29, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 89, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13441 :
    (13441 : ℕ).Prime ∧ logScale (13441 : ℚ) = 13 ∧
      (95060650126 : ℤ) = ⌊logCenter (13441 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13441 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13441 : Reach 13441 133052099462665 169461813211 := by
  have hr := row_13441
  have hl := log_bounds hr.1
    (by change logScale (13441 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13421) (T := 132957038812539) (U := 169449205383)
    (by norm_num) (by norm_num) hr.1 gap_13441
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13421

theorem gap_13451 : PrimeGap 13441 13451 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13451 :
    (13451 : ℕ).Prime ∧ logScale (13451 : ℚ) = 13 ∧
      (95068087283 : ℤ) = ⌊logCenter (13451 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13451 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13451 : Reach 13451 133147167549948 169474412603 := by
  have hr := row_13451
  have hl := log_bounds hr.1
    (by change logScale (13451 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13441) (T := 133052099462665) (U := 169461813211)
    (by norm_num) (by norm_num) hr.1 gap_13451
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13441

theorem gap_13457 : PrimeGap 13451 13457 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13457 :
    (13457 : ℕ).Prime ∧ logScale (13457 : ℚ) = 13 ∧
      (95072546923 : ℤ) = ⌊logCenter (13457 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13457 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13457 : Reach 13457 133242240096871 169487007313 := by
  have hr := row_13457
  have hl := log_bounds hr.1
    (by change logScale (13457 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13451) (T := 133147167549948) (U := 169474412603)
    (by norm_num) (by norm_num) hr.1 gap_13457
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13451

theorem gap_13463 : PrimeGap 13457 13463 :=
  (primeGap_of_factors (ds := [2, 43, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13463 :
    (13463 : ℕ).Prime ∧ logScale (13463 : ℚ) = 13 ∧
      (95077004575 : ℤ) = ⌊logCenter (13463 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13463 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13463 : Reach 13463 133337317101446 169499597345 := by
  have hr := row_13463
  have hl := log_bounds hr.1
    (by change logScale (13463 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13457) (T := 133242240096871) (U := 169487007313)
    (by norm_num) (by norm_num) hr.1 gap_13463
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13457

#print axioms reach_13463

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
