import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0110

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_3389 :
    (3389 : ℕ).Prime ∧ logScale (3389 : ℚ) = 11 ∧
      (81282901687 : ℤ) = ⌊logCenter (3389 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3389 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3389 : Reach 3389 33117041369807 145042976023 := by
  have hr := row_3389
  have hl := log_bounds hr.1
    (by change logScale (3389 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3373) (T := 33035758468120) (U := 145000177859)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3373

theorem row_3391 :
    (3391 : ℕ).Prime ∧ logScale (3391 : ℚ) = 11 ∧
      (81288801392 : ℤ) = ⌊logCenter (3391 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3391 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3391 : Reach 3391 33198330171199 145085761562 := by
  have hr := row_3391
  have hl := log_bounds hr.1
    (by change logScale (3391 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3389) (T := 33117041369807) (U := 145042976023)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3389

theorem row_3407 :
    (3407 : ℕ).Prime ∧ logScale (3407 : ℚ) = 11 ∧
      (81335874148 : ℤ) = ⌊logCenter (3407 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3407 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3407 : Reach 3407 33279666045347 145128358674 := by
  have hr := row_3407
  have hl := log_bounds hr.1
    (by change logScale (3407 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3391) (T := 33198330171199) (U := 145085761562)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3391

theorem row_3413 :
    (3413 : ℕ).Prime ∧ logScale (3413 : ℚ) = 11 ∧
      (81353469460 : ℤ) = ⌊logCenter (3413 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3413 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3413 : Reach 3413 33361019514807 145170893363 := by
  have hr := row_3413
  have hl := log_bounds hr.1
    (by change logScale (3413 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3407) (T := 33279666045347) (U := 145128358674)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3407

theorem row_3433 :
    (3433 : ℕ).Prime ∧ logScale (3433 : ℚ) = 11 ∧
      (81411897905 : ℤ) = ⌊logCenter (3433 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3433 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3433 : Reach 3433 33442431412712 145213192575 := by
  have hr := row_3433
  have hl := log_bounds hr.1
    (by change logScale (3433 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3413) (T := 33361019514807) (U := 145170893363)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3413

theorem row_3449 :
    (3449 : ℕ).Prime ∧ logScale (3449 : ℚ) = 11 ∧
      (81458396100 : ℤ) = ⌊logCenter (3449 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3449 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3449 : Reach 3449 33523889808812 145255307771 := by
  have hr := row_3449
  have hl := log_bounds hr.1
    (by change logScale (3449 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3433) (T := 33442431412712) (U := 145213192575)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3433

theorem row_3457 :
    (3457 : ℕ).Prime ∧ logScale (3457 : ℚ) = 11 ∧
      (81481564370 : ℤ) = ⌊logCenter (3457 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3457 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3457 : Reach 3457 33605371373182 145297337664 := by
  have hr := row_3457
  have hl := log_bounds hr.1
    (by change logScale (3457 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3449) (T := 33523889808812) (U := 145255307771)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3449

theorem row_3461 :
    (3461 : ℕ).Prime ∧ logScale (3461 : ℚ) = 11 ∧
      (81493128407 : ℤ) = ⌊logCenter (3461 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3461 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3461 : Reach 3461 33686864501589 145339331115 := by
  have hr := row_3461
  have hl := log_bounds hr.1
    (by change logScale (3461 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3457) (T := 33605371373182) (U := 145297337664)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3457

#print axioms reach_3461

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
