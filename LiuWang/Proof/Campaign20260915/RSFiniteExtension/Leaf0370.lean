import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block036
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_8761 : PrimeGap 8753 8761 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 19, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8761 :
    (8761 : ℕ).Prime ∧ logScale (8761 : ℚ) = 13 ∧
      (90780653292 : ℤ) = ⌊logCenter (8761 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8761 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8761 : Reach 8761 86521784783605 161877429708 := by
  have hr := row_8761
  have hl := log_bounds hr.1
    (by change logScale (8761 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8753) (T := 86431004130313) (U := 161858952658)
    (by norm_num) (by norm_num) hr.1 gap_8761
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8753

theorem gap_8779 : PrimeGap 8761 8779 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 31, 2, 3, 2, 67, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8779 :
    (8779 : ℕ).Prime ∧ logScale (8779 : ℚ) = 13 ∧
      (90801177815 : ℤ) = ⌊logCenter (8779 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8779 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8779 : Reach 8779 86612585961420 161895870974 := by
  have hr := row_8779
  have hl := log_bounds hr.1
    (by change logScale (8779 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8761) (T := 86521784783605) (U := 161877429708)
    (by norm_num) (by norm_num) hr.1 gap_8779
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8761

theorem gap_8783 : PrimeGap 8779 8783 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8783 :
    (8783 : ℕ).Prime ∧ logScale (8783 : ℚ) = 13 ∧
      (90805733105 : ℤ) = ⌊logCenter (8783 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8783 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8783 : Reach 8783 86703391694525 161914305940 := by
  have hr := row_8783
  have hl := log_bounds hr.1
    (by change logScale (8783 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8779) (T := 86612585961420) (U := 161895870974)
    (by norm_num) (by norm_num) hr.1 gap_8783
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8779

theorem gap_8803 : PrimeGap 8783 8803 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 11, 2, 59, 2, 3, 2, 5, 2, 19, 2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8803 :
    (8803 : ℕ).Prime ∧ logScale (8803 : ℚ) = 13 ∧
      (90828478480 : ℤ) = ⌊logCenter (8803 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8803 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8803 : Reach 8803 86794220173005 161932701113 := by
  have hr := row_8803
  have hl := log_bounds hr.1
    (by change logScale (8803 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8783) (T := 86703391694525) (U := 161914305940)
    (by norm_num) (by norm_num) hr.1 gap_8803
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8783

theorem gap_8807 : PrimeGap 8803 8807 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8807 :
    (8807 : ℕ).Prime ∧ logScale (8807 : ℚ) = 13 ∧
      (90833021354 : ℤ) = ⌊logCenter (8807 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8807 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8807 : Reach 8807 86885053194359 161951090019 := by
  have hr := row_8807
  have hl := log_bounds hr.1
    (by change logScale (8807 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8803) (T := 86794220173005) (U := 161932701113)
    (by norm_num) (by norm_num) hr.1 gap_8807
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8803

theorem gap_8819 : PrimeGap 8807 8819 :=
  (primeGap_of_factors (ds := [2, 23, 2, 3, 2, 7, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8819 :
    (8819 : ℕ).Prime ∧ logScale (8819 : ℚ) = 13 ∧
      (90846637605 : ℤ) = ⌊logCenter (8819 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8819 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8819 : Reach 8819 86975899831964 161969455986 := by
  have hr := row_8819
  have hl := log_bounds hr.1
    (by change logScale (8819 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8807) (T := 86885053194359) (U := 161951090019)
    (by norm_num) (by norm_num) hr.1 gap_8819
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8807

theorem gap_8821 : PrimeGap 8819 8821 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_8821 :
    (8821 : ℕ).Prime ∧ logScale (8821 : ℚ) = 13 ∧
      (90848905178 : ℤ) = ⌊logCenter (8821 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8821 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8821 : Reach 8821 87066748737142 161987819870 := by
  have hr := row_8821
  have hl := log_bounds hr.1
    (by change logScale (8821 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8819) (T := 86975899831964) (U := 161969455986)
    (by norm_num) (by norm_num) hr.1 gap_8821
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8819

theorem gap_8831 : PrimeGap 8821 8831 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8831 :
    (8831 : ℕ).Prime ∧ logScale (8831 : ℚ) = 13 ∧
      (90860235340 : ℤ) = ⌊logCenter (8831 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8831 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8831 : Reach 8831 87157608972482 162006165037 := by
  have hr := row_8831
  have hl := log_bounds hr.1
    (by change logScale (8831 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8821) (T := 87066748737142) (U := 161987819870)
    (by norm_num) (by norm_num) hr.1 gap_8831
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8821

#print axioms reach_8831

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
