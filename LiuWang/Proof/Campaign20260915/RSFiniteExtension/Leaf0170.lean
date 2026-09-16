import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block016

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_4517 :
    (4517 : ℕ).Prime ∧ logScale (4517 : ℚ) = 12 ∧
      (84156033325 : ℤ) = ⌊logCenter (4517 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4517 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4517 : Reach 4517 44374320166470 150163088431 := by
  have hr := row_4517
  have hl := log_bounds hr.1
    (by change logScale (4517 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4513) (T := 44290164133145) (U := 150129844444)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4513

theorem row_4519 :
    (4519 : ℕ).Prime ∧ logScale (4519 : ℚ) = 12 ∧
      (84160460062 : ℤ) = ⌊logCenter (4519 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4519 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4519 : Reach 4519 44458480626532 150196325060 := by
  have hr := row_4519
  have hl := log_bounds hr.1
    (by change logScale (4519 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4517) (T := 44374320166470) (U := 150163088431)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4517

theorem row_4523 :
    (4523 : ℕ).Prime ∧ logScale (4523 : ℚ) = 12 ∧
      (84169307663 : ℤ) = ⌊logCenter (4523 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4523 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4523 : Reach 4523 44542649934195 150229539639 := by
  have hr := row_4523
  have hl := log_bounds hr.1
    (by change logScale (4523 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4519) (T := 44458480626532) (U := 150196325060)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4519

theorem row_4547 :
    (4547 : ℕ).Prime ∧ logScale (4547 : ℚ) = 12 ∧
      (84222229507 : ℤ) = ⌊logCenter (4547 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4547 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4547 : Reach 4547 44626872163702 150262586173 := by
  have hr := row_4547
  have hl := log_bounds hr.1
    (by change logScale (4547 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4523) (T := 44542649934195) (U := 150229539639)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4523

theorem row_4549 :
    (4549 : ℕ).Prime ∧ logScale (4549 : ℚ) = 12 ∧
      (84226627044 : ℤ) = ⌊logCenter (4549 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4549 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4549 : Reach 4549 44711098790746 150295625440 := by
  have hr := row_4549
  have hl := log_bounds hr.1
    (by change logScale (4549 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4547) (T := 44626872163702) (U := 150262586173)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4547

theorem row_4561 :
    (4561 : ℕ).Prime ∧ logScale (4561 : ℚ) = 12 ∧
      (84252971735 : ℤ) = ⌊logCenter (4561 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4561 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4561 : Reach 4561 44795351762481 150328585007 := by
  have hr := row_4561
  have hl := log_bounds hr.1
    (by change logScale (4561 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4549) (T := 44711098790746) (U := 150295625440)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4549

theorem row_4567 :
    (4567 : ℕ).Prime ∧ logScale (4567 : ℚ) = 12 ∧
      (84266118100 : ℤ) = ⌊logCenter (4567 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4567 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4567 : Reach 4567 44879617880581 150361508482 := by
  have hr := row_4567
  have hl := log_bounds hr.1
    (by change logScale (4567 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4561) (T := 44795351762481) (U := 150328585007)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4561

theorem row_4583 :
    (4583 : ℕ).Prime ∧ logScale (4583 : ℚ) = 12 ∧
      (84301090813 : ℤ) = ⌊logCenter (4583 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4583 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4583 : Reach 4583 44963918971394 150394324176 := by
  have hr := row_4583
  have hl := log_bounds hr.1
    (by change logScale (4583 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4567) (T := 44879617880581) (U := 150361508482)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4567

#print axioms reach_4583

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
