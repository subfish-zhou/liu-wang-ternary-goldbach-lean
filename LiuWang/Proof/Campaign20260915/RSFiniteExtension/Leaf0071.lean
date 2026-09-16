import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0070

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_2621 :
    (2621 : ℕ).Prime ∧ logScale (2621 : ℚ) = 11 ∧
      (78713112004 : ℤ) = ⌊logCenter (2621 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2621 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2621 : Reach 2621 25434950348418 140442076792 := by
  have hr := row_2621
  have hl := log_bounds hr.1
    (by change logScale (2621 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2617) (T := 25356237236414) (U := 140388493397)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2617

theorem row_2633 :
    (2633 : ℕ).Prime ∧ logScale (2633 : ℚ) = 11 ∧
      (78758791566 : ℤ) = ⌊logCenter (2633 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2633 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2633 : Reach 2633 25513709139984 140495436244 := by
  have hr := row_2633
  have hl := log_bounds hr.1
    (by change logScale (2633 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2621) (T := 25434950348418) (U := 140442076792)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2621

theorem row_2647 :
    (2647 : ℕ).Prime ∧ logScale (2647 : ℚ) = 11 ∧
      (78811821993 : ℤ) = ⌊logCenter (2647 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2647 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2647 : Reach 2647 25592520961977 140548533537 := by
  have hr := row_2647
  have hl := log_bounds hr.1
    (by change logScale (2647 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2633) (T := 25513709139984) (U := 140495436244)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2633

theorem row_2657 :
    (2657 : ℕ).Prime ∧ logScale (2657 : ℚ) = 11 ∧
      (78849529429 : ℤ) = ⌊logCenter (2657 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2657 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2657 : Reach 2657 25671370491406 140601450907 := by
  have hr := row_2657
  have hl := log_bounds hr.1
    (by change logScale (2657 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2647) (T := 25592520961977) (U := 140548533537)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2647

theorem row_2659 :
    (2659 : ℕ).Prime ∧ logScale (2659 : ℚ) = 11 ∧
      (78857053883 : ℤ) = ⌊logCenter (2659 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2659 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2659 : Reach 2659 25750227545289 140654348368 := by
  have hr := row_2659
  have hl := log_bounds hr.1
    (by change logScale (2659 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2657) (T := 25671370491406) (U := 140601450907)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2657

theorem row_2663 :
    (2663 : ℕ).Prime ∧ logScale (2663 : ℚ) = 11 ∧
      (78872085829 : ℤ) = ⌊logCenter (2663 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2663 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2663 : Reach 2663 25829099631118 140707186215 := by
  have hr := row_2663
  have hl := log_bounds hr.1
    (by change logScale (2663 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2659) (T := 25750227545289) (U := 140654348368)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2659

theorem row_2671 :
    (2671 : ℕ).Prime ∧ logScale (2671 : ℚ) = 11 ∧
      (78902082102 : ℤ) = ⌊logCenter (2671 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2671 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2671 : Reach 2671 25908001713220 140759885536 := by
  have hr := row_2671
  have hl := log_bounds hr.1
    (by change logScale (2671 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2663) (T := 25829099631118) (U := 140707186215)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2663

theorem row_2677 :
    (2677 : ℕ).Prime ∧ logScale (2677 : ℚ) = 11 ∧
      (78924520406 : ℤ) = ⌊logCenter (2677 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2677 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2677 : Reach 2677 25986926233626 140812486391 := by
  have hr := row_2677
  have hl := log_bounds hr.1
    (by change logScale (2677 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2671) (T := 25908001713220) (U := 140759885536)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2671

#print axioms reach_2677

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
