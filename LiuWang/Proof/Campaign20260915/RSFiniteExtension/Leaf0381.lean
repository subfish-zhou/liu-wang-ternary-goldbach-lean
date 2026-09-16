import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0380
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_9049 : PrimeGap 9043 9049 :=
  (primeGap_of_factors (ds := [2, 3, 2, 83, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9049 :
    (9049 : ℕ).Prime ∧ logScale (9049 : ℚ) = 13 ∧
      (91104095299 : ℤ) = ⌊logCenter (9049 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9049 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9049 : Reach 9049 89432363400353 162459544927 := by
  have hr := row_9049
  have hl := log_bounds hr.1
    (by change logScale (9049 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9043) (T := 89341259305054) (U := 162441591612)
    (by norm_num) (by norm_num) hr.1 gap_9049
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9043

theorem gap_9059 : PrimeGap 9049 9059 :=
  (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9059 :
    (9059 : ℕ).Prime ∧ logScale (9059 : ℚ) = 13 ∧
      (91115140142 : ℤ) = ⌊logCenter (9059 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9059 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9059 : Reach 9059 89523478540495 162477480404 := by
  have hr := row_9059
  have hl := log_bounds hr.1
    (by change logScale (9059 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9049) (T := 89432363400353) (U := 162459544927)
    (by norm_num) (by norm_num) hr.1 gap_9059
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9049

theorem gap_9067 : PrimeGap 9059 9067 :=
  (primeGap_of_factors (ds := [2, 13, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9067 :
    (9067 : ℕ).Prime ∧ logScale (9067 : ℚ) = 13 ∧
      (91123967242 : ℤ) = ⌊logCenter (9067 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9067 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9067 : Reach 9067 89614602507737 162495402033 := by
  have hr := row_9067
  have hl := log_bounds hr.1
    (by change logScale (9067 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9059) (T := 89523478540495) (U := 162477480404)
    (by norm_num) (by norm_num) hr.1 gap_9067
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9059

theorem gap_9091 : PrimeGap 9067 9091 :=
  (primeGap_of_factors (ds := [2, 3, 2, 47, 2, 43, 2, 3, 2, 29, 2, 7, 2, 3, 2, 31, 2, 5, 2, 3, 2, 61, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9091 :
    (9091 : ℕ).Prime ∧ logScale (9091 : ℚ) = 13 ∧
      (91150401887 : ℤ) = ⌊logCenter (9091 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9091 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9091 : Reach 9091 89705752909624 162513278315 := by
  have hr := row_9091
  have hl := log_bounds hr.1
    (by change logScale (9091 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9067) (T := 89614602507737) (U := 162495402033)
    (by norm_num) (by norm_num) hr.1 gap_9091
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9067

theorem gap_9103 : PrimeGap 9091 9103 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 11, 2, 3, 2, 19, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9103 :
    (9103 : ℕ).Prime ∧ logScale (9103 : ℚ) = 13 ∧
      (91163593051 : ℤ) = ⌊logCenter (9103 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9103 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9103 : Reach 9103 89796916502675 162531132993 := by
  have hr := row_9103
  have hl := log_bounds hr.1
    (by change logScale (9103 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9091) (T := 89705752909624) (U := 162513278315)
    (by norm_num) (by norm_num) hr.1 gap_9103
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9091

theorem gap_9109 : PrimeGap 9103 9109 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9109 :
    (9109 : ℕ).Prime ∧ logScale (9109 : ℚ) = 13 ∧
      (91170182113 : ℤ) = ⌊logCenter (9109 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9109 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9109 : Reach 9109 89888086684788 162548977870 := by
  have hr := row_9109
  have hl := log_bounds hr.1
    (by change logScale (9109 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9103) (T := 89796916502675) (U := 162531132993)
    (by norm_num) (by norm_num) hr.1 gap_9109
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9103

theorem gap_9127 : PrimeGap 9109 9127 :=
  (primeGap_of_factors (ds := [2, 3, 2, 13, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9127 :
    (9127 : ℕ).Prime ∧ logScale (9127 : ℚ) = 13 ∧
      (91189923291 : ℤ) = ⌊logCenter (9127 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9127 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9127 : Reach 9127 89979276608079 162566789505 := by
  have hr := row_9127
  have hl := log_bounds hr.1
    (by change logScale (9127 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9109) (T := 89888086684788) (U := 162548977870)
    (by norm_num) (by norm_num) hr.1 gap_9127
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9109

theorem gap_9133 : PrimeGap 9127 9133 :=
  (primeGap_of_factors (ds := [2, 3, 2, 23, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9133 :
    (9133 : ℕ).Prime ∧ logScale (9133 : ℚ) = 13 ∧
      (91196495033 : ℤ) = ⌊logCenter (9133 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9133 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9133 : Reach 9133 90070473103112 162584591388 := by
  have hr := row_9133
  have hl := log_bounds hr.1
    (by change logScale (9133 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9127) (T := 89979276608079) (U := 162566789505)
    (by norm_num) (by norm_num) hr.1 gap_9133
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9127

#print axioms reach_9133

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
