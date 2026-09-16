import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0160

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_4373 :
    (4373 : ℕ).Prime ∧ logScale (4373 : ℚ) = 12 ∧
      (83832045482 : ℤ) = ⌊logCenter (4373 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4373 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4373 : Reach 4373 43030009843223 149624752529 := by
  have hr := row_4373
  have hl := log_bounds hr.1
    (by change logScale (4373 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4363) (T := 42946177797741) (U := 149590536944)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4363

theorem row_4391 :
    (4391 : ℕ).Prime ∧ logScale (4391 : ℚ) = 12 ∧
      (83873122674 : ℤ) = ⌊logCenter (4391 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4391 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4391 : Reach 4391 43113882965897 149658835617 := by
  have hr := row_4391
  have hl := log_bounds hr.1
    (by change logScale (4391 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4373) (T := 43030009843223) (U := 149624752529)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4373

theorem row_4397 :
    (4397 : ℕ).Prime ∧ logScale (4397 : ℚ) = 12 ∧
      (83886777660 : ℤ) = ⌊logCenter (4397 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4397 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4397 : Reach 4397 43197769743557 149692879939 := by
  have hr := row_4397
  have hl := log_bounds hr.1
    (by change logScale (4397 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4391) (T := 43113882965897) (U := 149658835617)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4391

theorem row_4409 :
    (4409 : ℕ).Prime ∧ logScale (4409 : ℚ) = 12 ∧
      (83914031822 : ℤ) = ⌊logCenter (4409 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4409 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4409 : Reach 4409 43281683775379 149726839304 := by
  have hr := row_4409
  have hl := log_bounds hr.1
    (by change logScale (4409 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4397) (T := 43197769743557) (U := 149692879939)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4397

theorem row_4421 :
    (4421 : ℕ).Prime ∧ logScale (4421 : ℚ) = 12 ∧
      (83941211907 : ℤ) = ⌊logCenter (4421 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4421 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4421 : Reach 4421 43365624987286 149760714155 := by
  have hr := row_4421
  have hl := log_bounds hr.1
    (by change logScale (4421 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4409) (T := 43281683775379) (U := 149726839304)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4409

theorem row_4423 :
    (4423 : ℕ).Prime ∧ logScale (4423 : ℚ) = 12 ∧
      (83945734747 : ℤ) = ⌊logCenter (4423 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4423 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4423 : Reach 4423 43449570722033 149794581345 := by
  have hr := row_4423
  have hl := log_bounds hr.1
    (by change logScale (4423 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4421) (T := 43365624987286) (U := 149760714155)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4421

theorem row_4441 :
    (4441 : ℕ).Prime ∧ logScale (4441 : ℚ) = 12 ∧
      (83986348521 : ℤ) = ⌊logCenter (4441 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4441 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4441 : Reach 4441 43533557070554 149828318864 := by
  have hr := row_4441
  have hl := log_bounds hr.1
    (by change logScale (4441 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4423) (T := 43449570722033) (U := 149794581345)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4423

theorem row_4447 :
    (4447 : ℕ).Prime ∧ logScale (4447 : ℚ) = 12 ∧
      (83999849873 : ℤ) = ⌊logCenter (4447 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4447 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4447 : Reach 4447 43617556920427 149862018441 := by
  have hr := row_4447
  have hl := log_bounds hr.1
    (by change logScale (4447 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4441) (T := 43533557070554) (U := 149828318864)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4441

#print axioms reach_4447

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
