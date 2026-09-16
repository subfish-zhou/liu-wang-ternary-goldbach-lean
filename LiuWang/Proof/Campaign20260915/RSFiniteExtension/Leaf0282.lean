import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0281
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_6959 : PrimeGap 6949 6959 :=
  (primeGap_of_factors (ds := [2, 3, 2, 17, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6959 :
    (6959 : ℕ).Prime ∧ logScale (6959 : ℚ) = 12 ∧
      (88477910617 : ℤ) = ⌊logCenter (6959 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6959 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6959 : Reach 6959 68584672712035 157796915737 := by
  have hr := row_6959
  have hl := log_bounds hr.1
    (by change logScale (6959 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6949) (T := 68496194801418) (U := 157774240508)
    (by norm_num) (by norm_num) hr.1 gap_6959
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6949

theorem gap_6961 : PrimeGap 6959 6961 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_6961 :
    (6961 : ℕ).Prime ∧ logScale (6961 : ℚ) = 12 ∧
      (88480784180 : ℤ) = ⌊logCenter (6961 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6961 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6961 : Reach 6961 68673153496215 157819587708 := by
  have hr := row_6961
  have hl := log_bounds hr.1
    (by change logScale (6961 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6959) (T := 68584672712035) (U := 157796915737)
    (by norm_num) (by norm_num) hr.1 gap_6961
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6959

theorem gap_6967 : PrimeGap 6961 6967 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6967 :
    (6967 : ℕ).Prime ∧ logScale (6967 : ℚ) = 12 ∧
      (88489399919 : ℤ) = ⌊logCenter (6967 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6967 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6967 : Reach 6967 68761642896134 157842243406 := by
  have hr := row_6967
  have hl := log_bounds hr.1
    (by change logScale (6967 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6961) (T := 68673153496215) (U := 157819587708)
    (by norm_num) (by norm_num) hr.1 gap_6967
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6961

theorem gap_6971 : PrimeGap 6967 6971 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6971 :
    (6971 : ℕ).Prime ∧ logScale (6971 : ℚ) = 12 ∧
      (88495139623 : ℤ) = ⌊logCenter (6971 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6971 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6971 : Reach 6971 68850138035757 157864889352 := by
  have hr := row_6971
  have hl := log_bounds hr.1
    (by change logScale (6971 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6967) (T := 68761642896134) (U := 157842243406)
    (by norm_num) (by norm_num) hr.1 gap_6971
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6967

theorem gap_6977 : PrimeGap 6971 6977 :=
  (primeGap_of_factors (ds := [2, 19, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6977 :
    (6977 : ℕ).Prime ∧ logScale (6977 : ℚ) = 12 ∧
      (88503743008 : ℤ) = ⌊logCenter (6977 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6977 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6977 : Reach 6977 68938641778765 157887519067 := by
  have hr := row_6977
  have hl := log_bounds hr.1
    (by change logScale (6977 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6971) (T := 68850138035757) (U := 157864889352)
    (by norm_num) (by norm_num) hr.1 gap_6977
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6971

theorem gap_6983 : PrimeGap 6977 6983 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6983 :
    (6983 : ℕ).Prime ∧ logScale (6983 : ℚ) = 12 ∧
      (88512338997 : ℤ) = ⌊logCenter (6983 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6983 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6983 : Reach 6983 69027154117762 157910132576 := by
  have hr := row_6983
  have hl := log_bounds hr.1
    (by change logScale (6983 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6977) (T := 68938641778765) (U := 157887519067)
    (by norm_num) (by norm_num) hr.1 gap_6983
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6977

theorem gap_6991 : PrimeGap 6983 6991 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 29, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6991 :
    (6991 : ℕ).Prime ∧ logScale (6991 : ℚ) = 12 ∧
      (88523788833 : ℤ) = ⌊logCenter (6991 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6991 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6991 : Reach 6991 69115677906595 157932723440 := by
  have hr := row_6991
  have hl := log_bounds hr.1
    (by change logScale (6991 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6983) (T := 69027154117762) (U := 157910132576)
    (by norm_num) (by norm_num) hr.1 gap_6991
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6983

theorem gap_6997 : PrimeGap 6991 6997 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6997 :
    (6997 : ℕ).Prime ∧ logScale (6997 : ℚ) = 12 ∧
      (88532367616 : ℤ) = ⌊logCenter (6997 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6997 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6997 : Reach 6997 69204210274211 157955298158 := by
  have hr := row_6997
  have hl := log_bounds hr.1
    (by change logScale (6997 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6991) (T := 69115677906595) (U := 157932723440)
    (by norm_num) (by norm_num) hr.1 gap_6997
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6991

#print axioms reach_6997

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
