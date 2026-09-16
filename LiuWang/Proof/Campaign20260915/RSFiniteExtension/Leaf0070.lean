import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block006

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_2549 :
    (2549 : ℕ).Prime ∧ logScale (2549 : ℚ) = 11 ∧
      (78434564015 : ℤ) = ⌊logCenter (2549 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2549 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2549 : Reach 2549 24806208598087 140008784099 := by
  have hr := row_2549
  have hl := log_bounds hr.1
    (by change logScale (2549 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2543) (T := 24727774034072) (U := 139953857153)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2543

theorem row_2551 :
    (2551 : ℕ).Prime ∧ logScale (2551 : ℚ) = 11 ∧
      (78442407152 : ℤ) = ⌊logCenter (2551 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2551 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2551 : Reach 2551 24884651005239 140063689505 := by
  have hr := row_2551
  have hl := log_bounds hr.1
    (by change logScale (2551 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2549) (T := 24806208598087) (U := 140008784099)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2549

theorem row_2557 :
    (2557 : ℕ).Prime ∧ logScale (2557 : ℚ) = 11 ∧
      (78465899724 : ℤ) = ⌊logCenter (2557 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2557 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2557 : Reach 2557 24963116904963 140118487506 := by
  have hr := row_2557
  have hl := log_bounds hr.1
    (by change logScale (2557 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2551) (T := 24884651005239) (U := 140063689505)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2551

theorem row_2579 :
    (2579 : ℕ).Prime ∧ logScale (2579 : ℚ) = 11 ∧
      (78551570030 : ℤ) = ⌊logCenter (2579 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2579 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2579 : Reach 2579 25041668474993 140172839131 := by
  have hr := row_2579
  have hl := log_bounds hr.1
    (by change logScale (2579 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2557) (T := 24963116904963) (U := 140118487506)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2557

theorem row_2591 :
    (2591 : ℕ).Prime ∧ logScale (2591 : ℚ) = 11 ∧
      (78597991777 : ℤ) = ⌊logCenter (2591 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2591 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2591 : Reach 2591 25120266466770 140226959919 := by
  have hr := row_2591
  have hl := log_bounds hr.1
    (by change logScale (2591 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2579) (T := 25041668474993) (U := 140172839131)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2579

theorem row_2593 :
    (2593 : ℕ).Prime ∧ logScale (2593 : ℚ) = 11 ∧
      (78605707826 : ℤ) = ⌊logCenter (2593 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2593 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2593 : Reach 2593 25198872174596 140281059827 := by
  have hr := row_2593
  have hl := log_bounds hr.1
    (by change logScale (2593 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2591) (T := 25120266466770) (U := 140226959919)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2591

theorem row_2609 :
    (2609 : ℕ).Prime ∧ logScale (2609 : ℚ) = 11 ∧
      (78667222822 : ℤ) = ⌊logCenter (2609 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2609 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2609 : Reach 2609 25277539397418 140334848577 := by
  have hr := row_2609
  have hl := log_bounds hr.1
    (by change logScale (2609 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2593) (T := 25198872174596) (U := 140281059827)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2593

theorem row_2617 :
    (2617 : ℕ).Prime ∧ logScale (2617 : ℚ) = 11 ∧
      (78697838996 : ℤ) = ⌊logCenter (2617 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2617 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2617 : Reach 2617 25356237236414 140388493397 := by
  have hr := row_2617
  have hl := log_bounds hr.1
    (by change logScale (2617 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2609) (T := 25277539397418) (U := 140334848577)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2609

#print axioms reach_2617

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
