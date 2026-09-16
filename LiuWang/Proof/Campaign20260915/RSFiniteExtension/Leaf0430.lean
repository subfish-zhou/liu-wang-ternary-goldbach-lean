import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block042
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_10079 : PrimeGap 10069 10079 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10079 :
    (10079 : ℕ).Prime ∧ logScale (10079 : ℚ) = 13 ∧
      (92182093269 : ℤ) = ⌊logCenter (10079 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10079 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10079 : Reach 10079 99697107878117 164375750794 := by
  have hr := row_10079
  have hl := log_bounds hr.1
    (by change logScale (10079 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10069) (T := 99604925784848) (U := 164359442057)
    (by norm_num) (by norm_num) hr.1 gap_10079
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10069

theorem gap_10091 : PrimeGap 10079 10091 :=
  (primeGap_of_factors (ds := [2, 17, 2, 3, 2, 5, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10091 :
    (10091 : ℕ).Prime ∧ logScale (10091 : ℚ) = 13 ∧
      (92193992130 : ℤ) = ⌊logCenter (10091 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10091 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10091 : Reach 10091 99789301870247 164392041751 := by
  have hr := row_10091
  have hl := log_bounds hr.1
    (by change logScale (10091 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10079) (T := 99697107878117) (U := 164375750794)
    (by norm_num) (by norm_num) hr.1 gap_10091
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10079

theorem gap_10093 : PrimeGap 10091 10093 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_10093 :
    (10093 : ℕ).Prime ∧ logScale (10093 : ℚ) = 13 ∧
      (92195973898 : ℤ) = ⌊logCenter (10093 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10093 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10093 : Reach 10093 99881497844145 164408331094 := by
  have hr := row_10093
  have hl := log_bounds hr.1
    (by change logScale (10093 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10091) (T := 99789301870247) (U := 164392041751)
    (by norm_num) (by norm_num) hr.1 gap_10093
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10091

theorem gap_10099 : PrimeGap 10093 10099 :=
  (primeGap_of_factors (ds := [2, 3, 2, 23, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10099 :
    (10099 : ℕ).Prime ∧ logScale (10099 : ℚ) = 13 ∧
      (92201916846 : ℤ) = ⌊logCenter (10099 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10099 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10099 : Reach 10099 99973699760991 164424612371 := by
  have hr := row_10099
  have hl := log_bounds hr.1
    (by change logScale (10099 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10093) (T := 99881497844145) (U := 164408331094)
    (by norm_num) (by norm_num) hr.1 gap_10099
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10093

theorem gap_10103 : PrimeGap 10099 10103 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10103 :
    (10103 : ℕ).Prime ∧ logScale (10103 : ℚ) = 13 ∧
      (92205876850 : ℤ) = ⌊logCenter (10103 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10103 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10103 : Reach 10103 100065905637841 164440888813 := by
  have hr := row_10103
  have hl := log_bounds hr.1
    (by change logScale (10103 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10099) (T := 99973699760991) (U := 164424612371)
    (by norm_num) (by norm_num) hr.1 gap_10103
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10099

theorem gap_10111 : PrimeGap 10103 10111 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10111 :
    (10111 : ℕ).Prime ∧ logScale (10111 : ℚ) = 13 ∧
      (92213792157 : ℤ) = ⌊logCenter (10111 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10111 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10111 : Reach 10111 100158119429998 164457153985 := by
  have hr := row_10111
  have hl := log_bounds hr.1
    (by change logScale (10111 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10103) (T := 100065905637841) (U := 164440888813)
    (by norm_num) (by norm_num) hr.1 gap_10111
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10103

theorem gap_10133 : PrimeGap 10111 10133 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 67, 2, 3, 2, 29, 2, 53, 2, 3, 2, 13, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10133 :
    (10133 : ℕ).Prime ∧ logScale (10133 : ℚ) = 13 ∧
      (92235527000 : ℤ) = ⌊logCenter (10133 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10133 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10133 : Reach 10133 100250354956998 164473385446 := by
  have hr := row_10133
  have hl := log_bounds hr.1
    (by change logScale (10133 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10111) (T := 100158119429998) (U := 164457153985)
    (by norm_num) (by norm_num) hr.1 gap_10133
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10111

theorem gap_10139 : PrimeGap 10133 10139 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10139 :
    (10139 : ℕ).Prime ∧ logScale (10139 : ℚ) = 13 ∧
      (92241446495 : ℤ) = ⌊logCenter (10139 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10139 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10139 : Reach 10139 100342596403493 164489608901 := by
  have hr := row_10139
  have hl := log_bounds hr.1
    (by change logScale (10139 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10133) (T := 100250354956998) (U := 164473385446)
    (by norm_num) (by norm_num) hr.1 gap_10139
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10133

#print axioms reach_10139

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
