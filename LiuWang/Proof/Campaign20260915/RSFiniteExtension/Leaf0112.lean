import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0111

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_3463 :
    (3463 : ℕ).Prime ∧ logScale (3463 : ℚ) = 11 ∧
      (81498905415 : ℤ) = ⌊logCenter (3463 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3463 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3463 : Reach 3463 33768363407004 145381312436 := by
  have hr := row_3463
  have hl := log_bounds hr.1
    (by change logScale (3463 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3461) (T := 33686864501589) (U := 145339331115)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3461

theorem row_3467 :
    (3467 : ℕ).Prime ∧ logScale (3467 : ℚ) = 11 ∧
      (81510449428 : ℤ) = ⌊logCenter (3467 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3467 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3467 : Reach 3467 33849873856432 145423257420 := by
  have hr := row_3467
  have hl := log_bounds hr.1
    (by change logScale (3467 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3463) (T := 33768363407004) (U := 145381312436)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3463

theorem row_3469 :
    (3469 : ℕ).Prime ∧ logScale (3469 : ℚ) = 11 ∧
      (81516216441 : ℤ) = ⌊logCenter (3469 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3469 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3469 : Reach 3469 33931390072873 145465190309 := by
  have hr := row_3469
  have hl := log_bounds hr.1
    (by change logScale (3469 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3467) (T := 33849873856432) (U := 145423257420)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3467

theorem row_3491 :
    (3491 : ℕ).Prime ∧ logScale (3491 : ℚ) = 11 ∧
      (81579435042 : ℤ) = ⌊logCenter (3491 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3491 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3491 : Reach 3491 34012969507915 145506870880 := by
  have hr := row_3491
  have hl := log_bounds hr.1
    (by change logScale (3491 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3469) (T := 33931390072873) (U := 145465190309)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3469

theorem row_3499 :
    (3499 : ℕ).Prime ∧ logScale (3499 : ℚ) = 11 ∧
      (81602324895 : ℤ) = ⌊logCenter (3499 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3499 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3499 : Reach 3499 34094571832810 145548468042 := by
  have hr := row_3499
  have hl := log_bounds hr.1
    (by change logScale (3499 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3491) (T := 34012969507915) (U := 145506870880)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3491

theorem row_3511 :
    (3511 : ℕ).Prime ∧ logScale (3511 : ℚ) = 11 ∧
      (81636561733 : ℤ) = ⌊logCenter (3511 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3511 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3511 : Reach 3511 34176208394543 145589934843 := by
  have hr := row_3511
  have hl := log_bounds hr.1
    (by change logScale (3511 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3499) (T := 34094571832810) (U := 145548468042)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3499

theorem row_3517 :
    (3517 : ℕ).Prime ∧ logScale (3517 : ℚ) = 11 ∧
      (81653636296 : ℤ) = ⌊logCenter (3517 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3517 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3517 : Reach 3517 34257862030839 145631342675 := by
  have hr := row_3517
  have hl := log_bounds hr.1
    (by change logScale (3517 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3511) (T := 34176208394543) (U := 145589934843)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3511

theorem row_3527 :
    (3527 : ℕ).Prime ∧ logScale (3527 : ℚ) = 11 ∧
      (81682029273 : ℤ) = ⌊logCenter (3527 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3527 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3527 : Reach 3527 34339544060112 145672644815 := by
  have hr := row_3527
  have hl := log_bounds hr.1
    (by change logScale (3527 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3517) (T := 34257862030839) (U := 145631342675)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3517

#print axioms reach_3527

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
