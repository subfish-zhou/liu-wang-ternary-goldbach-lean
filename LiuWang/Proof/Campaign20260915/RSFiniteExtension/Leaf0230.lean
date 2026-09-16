import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block022

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_5749 :
    (5749 : ℕ).Prime ∧ logScale (5749 : ℚ) = 12 ∧
      (86567812025 : ℤ) = ⌊logCenter (5749 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5749 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5749 : Reach 5749 56676965279988 154446260421 := by
  have hr := row_5749
  have hl := log_bounds hr.1
    (by change logScale (5749 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5743) (T := 56590397467963) (U := 154419395529)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5743

theorem row_5779 :
    (5779 : ℕ).Prime ∧ logScale (5779 : ℚ) = 12 ∧
      (86619859331 : ℤ) = ⌊logCenter (5779 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5779 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5779 : Reach 5779 56763585139319 154472990477 := by
  have hr := row_5779
  have hl := log_bounds hr.1
    (by change logScale (5779 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5749) (T := 56676965279988) (U := 154446260421)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5749

theorem row_5783 :
    (5783 : ℕ).Prime ∧ logScale (5783 : ℚ) = 12 ∧
      (86626778550 : ℤ) = ⌊logCenter (5783 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5783 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5783 : Reach 5783 56850211917869 154499706664 := by
  have hr := row_5783
  have hl := log_bounds hr.1
    (by change logScale (5783 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5779) (T := 56763585139319) (U := 154472990477)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5779

theorem row_5791 :
    (5791 : ℕ).Prime ∧ logScale (5791 : ℚ) = 12 ∧
      (86640602641 : ℤ) = ⌊logCenter (5791 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5791 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5791 : Reach 5791 56936852520510 154526390552 := by
  have hr := row_5791
  have hl := log_bounds hr.1
    (by change logScale (5791 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5783) (T := 56850211917869) (U := 154499706664)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5783

theorem row_5801 :
    (5801 : ℕ).Prime ∧ logScale (5801 : ℚ) = 12 ∧
      (86657855923 : ℤ) = ⌊logCenter (5801 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5801 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5801 : Reach 5801 57023510376433 154553033034 := by
  have hr := row_5801
  have hl := log_bounds hr.1
    (by change logScale (5801 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5791) (T := 56936852520510) (U := 154526390552)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5791

theorem row_5807 :
    (5807 : ℕ).Prime ∧ logScale (5807 : ℚ) = 12 ∧
      (86668193622 : ℤ) = ⌊logCenter (5807 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5807 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5807 : Reach 5807 57110178570055 154579652572 := by
  have hr := row_5807
  have hl := log_bounds hr.1
    (by change logScale (5807 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5801) (T := 57023510376433) (U := 154553033034)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5801

theorem row_5813 :
    (5813 : ℕ).Prime ∧ logScale (5813 : ℚ) = 12 ∧
      (86678520645 : ℤ) = ⌊logCenter (5813 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5813 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5813 : Reach 5813 57196857090700 154606249209 := by
  have hr := row_5813
  have hl := log_bounds hr.1
    (by change logScale (5813 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5807) (T := 57110178570055) (U := 154579652572)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5807

theorem row_5821 :
    (5821 : ℕ).Prime ∧ logScale (5821 : ℚ) = 12 ∧
      (86692273441 : ℤ) = ⌊logCenter (5821 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5821 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5821 : Reach 5821 57283549364141 154632813857 := by
  have hr := row_5821
  have hl := log_bounds hr.1
    (by change logScale (5821 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5813) (T := 57196857090700) (U := 154606249209)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5813

#print axioms reach_5821

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
