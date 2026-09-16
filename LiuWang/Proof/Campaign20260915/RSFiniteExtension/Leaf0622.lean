import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0621
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_14591 : PrimeGap 14563 14591 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 17, 2, 3, 2, 13, 2, 5, 2, 3, 2, 61, 2, 7, 2, 3, 2, 5, 2, 29, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14591 :
    (14591 : ℕ).Prime ∧ logScale (14591 : ℚ) = 13 ∧
      (95881601758 : ℤ) = ⌊logCenter (14591 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14591 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14591 : Reach 14591 144127198381917 170871248843 := by
  have hr := row_14591
  have hl := log_bounds hr.1
    (by change logScale (14591 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14563) (T := 144031316780159) (U := 170859538113)
    (by norm_num) (by norm_num) hr.1 gap_14591
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14563

theorem gap_14593 : PrimeGap 14591 14593 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_14593 :
    (14593 : ℕ).Prime ∧ logScale (14593 : ℚ) = 13 ∧
      (95882972372 : ℤ) = ⌊logCenter (14593 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14593 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14593 : Reach 14593 144223081354289 170882958770 := by
  have hr := row_14593
  have hl := log_bounds hr.1
    (by change logScale (14593 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14591) (T := 144127198381917) (U := 170871248843)
    (by norm_num) (by norm_num) hr.1 gap_14593
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14591

theorem gap_14621 : PrimeGap 14593 14621 :=
  (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 13, 2, 3, 2, 17, 2, 5, 2, 3, 2, 7, 2, 19, 2, 3, 2, 5, 2, 47, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14621 :
    (14621 : ℕ).Prime ∧ logScale (14621 : ℚ) = 13 ∧
      (95902141270 : ℤ) = ⌊logCenter (14621 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14621 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14621 : Reach 14621 144318983495559 170894647071 := by
  have hr := row_14621
  have hl := log_bounds hr.1
    (by change logScale (14621 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14593) (T := 144223081354289) (U := 170882958770)
    (by norm_num) (by norm_num) hr.1 gap_14621
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14593

theorem gap_14627 : PrimeGap 14621 14627 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14627 :
    (14627 : ℕ).Prime ∧ logScale (14627 : ℚ) = 13 ∧
      (95906244115 : ℤ) = ⌊logCenter (14627 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14627 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14627 : Reach 14627 144414889739674 170906331377 := by
  have hr := row_14627
  have hl := log_bounds hr.1
    (by change logScale (14627 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14621) (T := 144318983495559) (U := 170894647071)
    (by norm_num) (by norm_num) hr.1 gap_14627
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14621

theorem gap_14629 : PrimeGap 14627 14629 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_14629 :
    (14629 : ℕ).Prime ∧ logScale (14629 : ℚ) = 13 ∧
      (95907611355 : ℤ) = ⌊logCenter (14629 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14629 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14629 : Reach 14629 144510797351029 170918014884 := by
  have hr := row_14629
  have hl := log_bounds hr.1
    (by change logScale (14629 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14627) (T := 144414889739674) (U := 170906331377)
    (by norm_num) (by norm_num) hr.1 gap_14629
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14627

theorem gap_14633 : PrimeGap 14629 14633 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14633 :
    (14633 : ℕ).Prime ∧ logScale (14633 : ℚ) = 13 ∧
      (95910345277 : ℤ) = ⌊logCenter (14633 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14633 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14633 : Reach 14633 144606707696306 170929695995 := by
  have hr := row_14633
  have hl := log_bounds hr.1
    (by change logScale (14633 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14629) (T := 144510797351029) (U := 170918014884)
    (by norm_num) (by norm_num) hr.1 gap_14633
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14629

theorem gap_14639 : PrimeGap 14633 14639 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14639 :
    (14639 : ℕ).Prime ∧ logScale (14639 : ℚ) = 13 ∧
      (95914444757 : ℤ) = ⌊logCenter (14639 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14639 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14639 : Reach 14639 144702622141063 170941373116 := by
  have hr := row_14639
  have hl := log_bounds hr.1
    (by change logScale (14639 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14633) (T := 144606707696306) (U := 170929695995)
    (by norm_num) (by norm_num) hr.1 gap_14639
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14633

theorem gap_14653 : PrimeGap 14639 14653 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 5, 2, 97, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14653 :
    (14653 : ℕ).Prime ∧ logScale (14653 : ℚ) = 13 ∧
      (95924003682 : ℤ) = ⌊logCenter (14653 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14653 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14653 : Reach 14653 144798546144745 170953039877 := by
  have hr := row_14653
  have hl := log_bounds hr.1
    (by change logScale (14653 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14639) (T := 144702622141063) (U := 170941373116)
    (by norm_num) (by norm_num) hr.1 gap_14653
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14639

#print axioms reach_14653

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
