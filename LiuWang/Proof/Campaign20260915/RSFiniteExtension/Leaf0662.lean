import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0661
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_15451 : PrimeGap 15443 15451 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15451 :
    (15451 : ℕ).Prime ∧ logScale (15451 : ℚ) = 13 ∧
      (96454290017 : ℤ) = ⌊logCenter (15451 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15451 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15451 : Reach 15451 153360026209223 171966630104 := by
  have hr := row_15451
  have hl := log_bounds hr.1
    (by change logScale (15451 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15443) (T := 153263571919206) (U := 171955500298)
    (by norm_num) (by norm_num) hr.1 gap_15451
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15443

theorem gap_15461 : PrimeGap 15451 15461 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15461 :
    (15461 : ℕ).Prime ∧ logScale (15461 : ℚ) = 13 ∧
      (96460759997 : ℤ) = ⌊logCenter (15461 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15461 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15461 : Reach 15461 153456486969220 171977753431 := by
  have hr := row_15461
  have hl := log_bounds hr.1
    (by change logScale (15461 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15451) (T := 153360026209223) (U := 171966630104)
    (by norm_num) (by norm_num) hr.1 gap_15461
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15451

theorem gap_15467 : PrimeGap 15461 15467 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15467 :
    (15467 : ℕ).Prime ∧ logScale (15467 : ℚ) = 13 ∧
      (96464639976 : ℤ) = ⌊logCenter (15467 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15467 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15467 : Reach 15467 153552951609196 171988873162 := by
  have hr := row_15467
  have hl := log_bounds hr.1
    (by change logScale (15467 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15461) (T := 153456486969220) (U := 171977753431)
    (by norm_num) (by norm_num) hr.1 gap_15467
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15461

theorem gap_15473 : PrimeGap 15467 15473 :=
  (primeGap_of_factors (ds := [2, 31, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15473 :
    (15473 : ℕ).Prime ∧ logScale (15473 : ℚ) = 13 ∧
      (96468518451 : ℤ) = ⌊logCenter (15473 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15473 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15473 : Reach 15473 153649420127647 171999989300 := by
  have hr := row_15473
  have hl := log_bounds hr.1
    (by change logScale (15473 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15467) (T := 153552951609196) (U := 171988873162)
    (by norm_num) (by norm_num) hr.1 gap_15473
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15467

theorem gap_15493 : PrimeGap 15473 15493 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 23, 2, 113, 2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15493 :
    (15493 : ℕ).Prime ∧ logScale (15493 : ℚ) = 13 ∧
      (96481435846 : ℤ) = ⌊logCenter (15493 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15493 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15493 : Reach 15493 153745901563493 172011091804 := by
  have hr := row_15493
  have hl := log_bounds hr.1
    (by change logScale (15493 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15473) (T := 153649420127647) (U := 171999989300)
    (by norm_num) (by norm_num) hr.1 gap_15493
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15473

theorem gap_15497 : PrimeGap 15493 15497 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15497 :
    (15497 : ℕ).Prime ∧ logScale (15497 : ℚ) = 13 ∧
      (96484017324 : ℤ) = ⌊logCenter (15497 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15497 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15497 : Reach 15497 153842385580817 172022192159 := by
  have hr := row_15497
  have hl := log_bounds hr.1
    (by change logScale (15497 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15493) (T := 153745901563493) (U := 172011091804)
    (by norm_num) (by norm_num) hr.1 gap_15497
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15493

theorem gap_15511 : PrimeGap 15497 15511 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 37, 2, 5, 2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15511 :
    (15511 : ℕ).Prime ∧ logScale (15511 : ℚ) = 13 ∧
      (96493047252 : ℤ) = ⌊logCenter (15511 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15511 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15511 : Reach 15511 153938878628069 172033283210 := by
  have hr := row_15511
  have hl := log_bounds hr.1
    (by change logScale (15511 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15497) (T := 153842385580817) (U := 172022192159)
    (by norm_num) (by norm_num) hr.1 gap_15511
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15497

theorem gap_15527 : PrimeGap 15511 15527 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 59, 2, 3, 2, 11, 2, 19, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15527 :
    (15527 : ℕ).Prime ∧ logScale (15527 : ℚ) = 13 ∧
      (96503357195 : ℤ) = ⌊logCenter (15527 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15527 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15527 : Reach 15527 154035381985264 172044363546 := by
  have hr := row_15527
  have hl := log_bounds hr.1
    (by change logScale (15527 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15511) (T := 153938878628069) (U := 172033283210)
    (by norm_num) (by norm_num) hr.1 gap_15527
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15511

#print axioms reach_15527

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
