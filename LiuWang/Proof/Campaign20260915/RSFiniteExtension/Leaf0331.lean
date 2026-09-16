import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0330
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_7951 : PrimeGap 7949 7951 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_7951 :
    (7951 : ℕ).Prime ∧ logScale (7951 : ℚ) = 12 ∧
      (89810529827 : ℤ) = ⌊logCenter (7951 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7951 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7951 : Reach 7951 78571814994119 160186423814 := by
  have hr := row_7951
  have hl := log_bounds hr.1
    (by change logScale (7951 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7949) (T := 78482004464292) (U := 160166277112)
    (by norm_num) (by norm_num) hr.1 gap_7951
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7949

theorem gap_7963 : PrimeGap 7951 7963 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 73, 2, 3, 2, 19, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7963 :
    (7963 : ℕ).Prime ∧ logScale (7963 : ℚ) = 12 ∧
      (89825610891 : ℤ) = ⌊logCenter (7963 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7963 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7963 : Reach 7963 78661640605010 160206542682 := by
  have hr := row_7963
  have hl := log_bounds hr.1
    (by change logScale (7963 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7951) (T := 78571814994119) (U := 160186423814)
    (by norm_num) (by norm_num) hr.1 gap_7963
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7951

theorem gap_7993 : PrimeGap 7963 7993 :=
  (primeGap_of_factors (ds := [2, 3, 2, 31, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 79, 2, 23, 2, 3, 2, 5, 2, 7, 2, 3, 2, 61, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7993 :
    (7993 : ℕ).Prime ∧ logScale (7993 : ℚ) = 12 ∧
      (89863214345 : ℤ) = ⌊logCenter (7993 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7993 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7993 : Reach 7993 78751503819355 160226588546 := by
  have hr := row_7993
  have hl := log_bounds hr.1
    (by change logScale (7993 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7963) (T := 78661640605010) (U := 160206542682)
    (by norm_num) (by norm_num) hr.1 gap_7993
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7963

theorem gap_8009 : PrimeGap 7993 8009 :=
  (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 19, 2, 3, 2, 53, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8009 :
    (8009 : ℕ).Prime ∧ logScale (8009 : ℚ) = 12 ∧
      (89883211851 : ℤ) = ⌊logCenter (8009 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8009 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8009 : Reach 8009 78841387031206 160246596862 := by
  have hr := row_8009
  have hl := log_bounds hr.1
    (by change logScale (8009 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7993) (T := 78751503819355) (U := 160226588546)
    (by norm_num) (by norm_num) hr.1 gap_8009
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7993

theorem gap_8011 : PrimeGap 8009 8011 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_8011 :
    (8011 : ℕ).Prime ∧ logScale (8011 : ℚ) = 12 ∧
      (89885708730 : ℤ) = ⌊logCenter (8011 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8011 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8011 : Reach 8011 78931272739936 160266602680 := by
  have hr := row_8011
  have hl := log_bounds hr.1
    (by change logScale (8011 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 8009) (T := 78841387031206) (U := 160246596862)
    (by norm_num) (by norm_num) hr.1 gap_8011
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8009

theorem gap_8017 : PrimeGap 8011 8017 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8017 :
    (8017 : ℕ).Prime ∧ logScale (8017 : ℚ) = 12 ∧
      (89893195629 : ℤ) = ⌊logCenter (8017 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8017 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8017 : Reach 8017 79021165935565 160286596019 := by
  have hr := row_8017
  have hl := log_bounds hr.1
    (by change logScale (8017 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 8011) (T := 78931272739936) (U := 160266602680)
    (by norm_num) (by norm_num) hr.1 gap_8017
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8011

theorem gap_8039 : PrimeGap 8017 8039 :=
  (primeGap_of_factors (ds := [2, 3, 2, 13, 2, 71, 2, 3, 2, 23, 2, 7, 2, 3, 2, 29, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8039 :
    (8039 : ℕ).Prime ∧ logScale (8039 : ℚ) = 12 ∧
      (89920599732 : ℤ) = ⌊logCenter (8039 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8039 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8039 : Reach 8039 79111086535297 160306537124 := by
  have hr := row_8039
  have hl := log_bounds hr.1
    (by change logScale (8039 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 8017) (T := 79021165935565) (U := 160286596019)
    (by norm_num) (by norm_num) hr.1 gap_8039
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8017

theorem gap_8053 : PrimeGap 8039 8053 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 5, 2, 13, 2, 3, 2, 83, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8053 :
    (8053 : ℕ).Prime ∧ logScale (8053 : ℚ) = 12 ∧
      (89937999686 : ℤ) = ⌊logCenter (8053 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8053 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8053 : Reach 8053 79201024534983 160326446034 := by
  have hr := row_8053
  have hl := log_bounds hr.1
    (by change logScale (8053 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 8039) (T := 79111086535297) (U := 160306537124)
    (by norm_num) (by norm_num) hr.1 gap_8053
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8039

#print axioms reach_8053

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
