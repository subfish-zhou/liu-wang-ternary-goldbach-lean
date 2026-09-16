import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0280
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_6871 : PrimeGap 6869 6871 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_6871 :
    (6871 : ℕ).Prime ∧ logScale (6871 : ℚ) = 12 ∧
      (88350649319 : ℤ) = ⌊logCenter (6871 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6871 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6871 : Reach 6871 67877282225734 157614620844 := by
  have hr := row_6871
  have hl := log_bounds hr.1
    (by change logScale (6871 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6869) (T := 67788931576415) (U := 157591681734)
    (by norm_num) (by norm_num) hr.1 gap_6871
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6869

theorem gap_6883 : PrimeGap 6871 6883 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6883 :
    (6883 : ℕ).Prime ∧ logScale (6883 : ℚ) = 12 ∧
      (88368098792 : ℤ) = ⌊logCenter (6883 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6883 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6883 : Reach 6883 67965650324526 157637523289 := by
  have hr := row_6883
  have hl := log_bounds hr.1
    (by change logScale (6883 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6871) (T := 67877282225734) (U := 157614620844)
    (by norm_num) (by norm_num) hr.1 gap_6883
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6871

theorem gap_6899 : PrimeGap 6883 6899 :=
  (primeGap_of_factors (ds := [2, 3, 2, 71, 2, 83, 2, 3, 2, 61, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6899 :
    (6899 : ℕ).Prime ∧ logScale (6899 : ℚ) = 12 ∧
      (88391317494 : ℤ) = ⌊logCenter (6899 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6899 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6899 : Reach 6899 68054041642020 157660375931 := by
  have hr := row_6899
  have hl := log_bounds hr.1
    (by change logScale (6899 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6883) (T := 67965650324526) (U := 157637523289)
    (by norm_num) (by norm_num) hr.1 gap_6899
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6883

theorem gap_6907 : PrimeGap 6899 6907 :=
  (primeGap_of_factors (ds := [2, 67, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6907 :
    (6907 : ℕ).Prime ∧ logScale (6907 : ℚ) = 12 ∧
      (88402906659 : ℤ) = ⌊logCenter (6907 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6907 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6907 : Reach 6907 68142444548679 157683205410 := by
  have hr := row_6907
  have hl := log_bounds hr.1
    (by change logScale (6907 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6899) (T := 68054041642020) (U := 157660375931)
    (by norm_num) (by norm_num) hr.1 gap_6907
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6899

theorem gap_6911 : PrimeGap 6907 6911 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6911 :
    (6911 : ℕ).Prime ∧ logScale (6911 : ℚ) = 12 ∧
      (88408696209 : ℤ) = ⌊logCenter (6911 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6911 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6911 : Reach 6911 68230853244888 157706024977 := by
  have hr := row_6911
  have hl := log_bounds hr.1
    (by change logScale (6911 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6907) (T := 68142444548679) (U := 157683205410)
    (by norm_num) (by norm_num) hr.1 gap_6911
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6907

theorem gap_6917 : PrimeGap 6911 6917 :=
  (primeGap_of_factors (ds := [2, 31, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6917 :
    (6917 : ℕ).Prime ∧ logScale (6917 : ℚ) = 12 ∧
      (88417374254 : ℤ) = ⌊logCenter (6917 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6917 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6917 : Reach 6917 68319270619142 157728828046 := by
  have hr := row_6917
  have hl := log_bounds hr.1
    (by change logScale (6917 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6911) (T := 68230853244888) (U := 157706024977)
    (by norm_num) (by norm_num) hr.1 gap_6917
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6911

theorem gap_6947 : PrimeGap 6917 6947 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 29, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 53, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_6947 :
    (6947 : ℕ).Prime ∧ logScale (6947 : ℚ) = 12 ∧
      (88460651875 : ℤ) = ⌊logCenter (6947 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6947 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6947 : Reach 6947 68407731271017 157751535911 := by
  have hr := row_6947
  have hl := log_bounds hr.1
    (by change logScale (6947 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6917) (T := 68319270619142) (U := 157728828046)
    (by norm_num) (by norm_num) hr.1 gap_6947
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6917

theorem gap_6949 : PrimeGap 6947 6949 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_6949 :
    (6949 : ℕ).Prime ∧ logScale (6949 : ℚ) = 12 ∧
      (88463530401 : ℤ) = ⌊logCenter (6949 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6949 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6949 : Reach 6949 68496194801418 157774240508 := by
  have hr := row_6949
  have hl := log_bounds hr.1
    (by change logScale (6949 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6947) (T := 68407731271017) (U := 157751535911)
    (by norm_num) (by norm_num) hr.1 gap_6949
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6947

#print axioms reach_6949

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
