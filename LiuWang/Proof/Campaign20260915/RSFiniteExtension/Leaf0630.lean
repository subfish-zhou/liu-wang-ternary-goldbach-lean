import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block062
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_14657 : PrimeGap 14653 14657 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14657 :
    (14657 : ℕ).Prime ∧ logScale (14657 : ℚ) = 13 ∧
      (95926733126 : ℤ) = ⌊logCenter (14657 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14657 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14657 : Reach 14657 144894472877871 170964704250 := by
  have hr := row_14657
  have hl := log_bounds hr.1
    (by change logScale (14657 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14653) (T := 144798546144745) (U := 170953039877)
    (by norm_num) (by norm_num) hr.1 gap_14657
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14653

theorem gap_14669 : PrimeGap 14657 14669 :=
  (primeGap_of_factors (ds := [2, 107, 2, 3, 2, 11, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14669 :
    (14669 : ℕ).Prime ∧ logScale (14669 : ℚ) = 13 ∧
      (95934916991 : ℤ) = ⌊logCenter (14669 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14669 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14669 : Reach 14669 144990407794862 170976359875 := by
  have hr := row_14669
  have hl := log_bounds hr.1
    (by change logScale (14669 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14657) (T := 144894472877871) (U := 170964704250)
    (by norm_num) (by norm_num) hr.1 gap_14669
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14657

theorem gap_14683 : PrimeGap 14669 14683 :=
  (primeGap_of_factors (ds := [2, 17, 2, 3, 2, 5, 2, 13, 2, 3, 2, 53, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14683 :
    (14683 : ℕ).Prime ∧ logScale (14683 : ℚ) = 13 ∧
      (95944456375 : ℤ) = ⌊logCenter (14683 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14683 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14683 : Reach 14683 145086352251237 170988005180 := by
  have hr := row_14683
  have hl := log_bounds hr.1
    (by change logScale (14683 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14669) (T := 144990407794862) (U := 170976359875)
    (by norm_num) (by norm_num) hr.1 gap_14683
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14669

theorem gap_14699 : PrimeGap 14683 14699 :=
  (primeGap_of_factors (ds := [2, 3, 2, 19, 2, 37, 2, 3, 2, 7, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14699 :
    (14699 : ℕ).Prime ∧ logScale (14699 : ℚ) = 13 ∧
      (95955347398 : ℤ) = ⌊logCenter (14699 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14699 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14699 : Reach 14699 145182307598635 170999638600 := by
  have hr := row_14699
  have hl := log_bounds hr.1
    (by change logScale (14699 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14683) (T := 145086352251237) (U := 170988005180)
    (by norm_num) (by norm_num) hr.1 gap_14699
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14683

theorem gap_14713 : PrimeGap 14699 14713 :=
  (primeGap_of_factors (ds := [2, 61, 2, 3, 2, 5, 2, 7, 2, 3, 2, 47, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14713 :
    (14713 : ℕ).Prime ∧ logScale (14713 : ℚ) = 13 ∧
      (95964867323 : ℤ) = ⌊logCenter (14713 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14713 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14713 : Reach 14713 145278272465958 171011261741 := by
  have hr := row_14713
  have hl := log_bounds hr.1
    (by change logScale (14713 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14699) (T := 145182307598635) (U := 170999638600)
    (by norm_num) (by norm_num) hr.1 gap_14713
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14699

theorem gap_14717 : PrimeGap 14713 14717 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14717 :
    (14717 : ℕ).Prime ∧ logScale (14717 : ℚ) = 13 ∧
      (95967585637 : ℤ) = ⌊logCenter (14717 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14717 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14717 : Reach 14717 145374240051595 171022882512 := by
  have hr := row_14717
  have hl := log_bounds hr.1
    (by change logScale (14717 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14713) (T := 145278272465958) (U := 171011261741)
    (by norm_num) (by norm_num) hr.1 gap_14717
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14713

theorem gap_14723 : PrimeGap 14717 14723 :=
  (primeGap_of_factors (ds := [2, 41, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14723 :
    (14723 : ℕ).Prime ∧ logScale (14723 : ℚ) = 13 ∧
      (95971661724 : ℤ) = ⌊logCenter (14723 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14723 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14723 : Reach 14723 145470211713319 171034499336 := by
  have hr := row_14723
  have hl := log_bounds hr.1
    (by change logScale (14723 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14717) (T := 145374240051595) (U := 171022882512)
    (by norm_num) (by norm_num) hr.1 gap_14723
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14717

theorem gap_14731 : PrimeGap 14723 14731 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14731 :
    (14731 : ℕ).Prime ∧ logScale (14731 : ℚ) = 13 ∧
      (95977093924 : ℤ) = ⌊logCenter (14731 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14731 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14731 : Reach 14731 145566188807243 171046110640 := by
  have hr := row_14731
  have hl := log_bounds hr.1
    (by change logScale (14731 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14723) (T := 145470211713319) (U := 171034499336)
    (by norm_num) (by norm_num) hr.1 gap_14731
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14723

#print axioms reach_14731

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
