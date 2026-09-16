import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0361
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_8707 : PrimeGap 8699 8707 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8707 :
    (8707 : ℕ).Prime ∧ logScale (8707 : ℚ) = 13 ∧
      (90718825754 : ℤ) = ⌊logCenter (8707 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8707 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8707 : Reach 8707 85795752267117 161729278887 := by
  have hr := row_8707
  have hl := log_bounds hr.1
    (by change logScale (8707 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8699) (T := 85705033441363) (U := 161710704259)
    (by norm_num) (by norm_num) hr.1 gap_8707
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8699

theorem gap_8713 : PrimeGap 8707 8713 :=
  (primeGap_of_factors (ds := [2, 3, 2, 31, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8713 :
    (8713 : ℕ).Prime ∧ logScale (8713 : ℚ) = 13 ∧
      (90725714388 : ℤ) = ⌊logCenter (8713 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8713 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8713 : Reach 8713 85886477981505 161747842854 := by
  have hr := row_8713
  have hl := log_bounds hr.1
    (by change logScale (8713 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8707) (T := 85795752267117) (U := 161729278887)
    (by norm_num) (by norm_num) hr.1 gap_8713
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8707

theorem gap_8719 : PrimeGap 8713 8719 :=
  (primeGap_of_factors (ds := [2, 3, 2, 23, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8719 :
    (8719 : ℕ).Prime ∧ logScale (8719 : ℚ) = 13 ∧
      (90732598280 : ℤ) = ⌊logCenter (8719 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8719 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8719 : Reach 8719 85977210579785 161766396174 := by
  have hr := row_8719
  have hl := log_bounds hr.1
    (by change logScale (8719 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8713) (T := 85886477981505) (U := 161747842854)
    (by norm_num) (by norm_num) hr.1 gap_8719
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8713

theorem gap_8731 : PrimeGap 8719 8731 :=
  (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8731 :
    (8731 : ℕ).Prime ∧ logScale (8731 : ℚ) = 13 ∧
      (90746351864 : ℤ) = ⌊logCenter (8731 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8731 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8731 : Reach 8731 86067956931649 161784926117 := by
  have hr := row_8731
  have hl := log_bounds hr.1
    (by change logScale (8731 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8719) (T := 85977210579785) (U := 161766396174)
    (by norm_num) (by norm_num) hr.1 gap_8731
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8719

theorem gap_8737 : PrimeGap 8731 8737 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8737 :
    (8737 : ℕ).Prime ∧ logScale (8737 : ℚ) = 13 ∧
      (90753221569 : ℤ) = ⌊logCenter (8737 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8737 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8737 : Reach 8737 86158710153218 161803445454 := by
  have hr := row_8737
  have hl := log_bounds hr.1
    (by change logScale (8737 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8731) (T := 86067956931649) (U := 161784926117)
    (by norm_num) (by norm_num) hr.1 gap_8737
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8731

theorem gap_8741 : PrimeGap 8737 8741 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8741 :
    (8741 : ℕ).Prime ∧ logScale (8741 : ℚ) = 13 ∧
      (90757798752 : ℤ) = ⌊logCenter (8741 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8741 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8741 : Reach 8741 86249467951970 161821958435 := by
  have hr := row_8741
  have hl := log_bounds hr.1
    (by change logScale (8741 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8737) (T := 86158710153218) (U := 161803445454)
    (by norm_num) (by norm_num) hr.1 gap_8741
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8737

theorem gap_8747 : PrimeGap 8741 8747 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8747 :
    (8747 : ℕ).Prime ∧ logScale (8747 : ℚ) = 13 ∧
      (90764660600 : ℤ) = ⌊logCenter (8747 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8747 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8747 : Reach 8747 86340232612570 161840460832 := by
  have hr := row_8747
  have hl := log_bounds hr.1
    (by change logScale (8747 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8741) (T := 86249467951970) (U := 161821958435)
    (by norm_num) (by norm_num) hr.1 gap_8747
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8741

theorem gap_8753 : PrimeGap 8747 8753 :=
  (primeGap_of_factors (ds := [2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8753 :
    (8753 : ℕ).Prime ∧ logScale (8753 : ℚ) = 13 ∧
      (90771517743 : ℤ) = ⌊logCenter (8753 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8753 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8753 : Reach 8753 86431004130313 161858952658 := by
  have hr := row_8753
  have hl := log_bounds hr.1
    (by change logScale (8753 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8747) (T := 86340232612570) (U := 161840460832)
    (by norm_num) (by norm_num) hr.1 gap_8753
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8747

#print axioms reach_8753

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
