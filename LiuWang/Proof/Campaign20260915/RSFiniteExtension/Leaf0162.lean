import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0161

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_4451 :
    (4451 : ℕ).Prime ∧ logScale (4451 : ℚ) = 12 ∧
      (84008840658 : ℤ) = ⌊logCenter (4451 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4451 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4451 : Reach 4451 43701565761085 149895695300 := by
  have hr := row_4451
  have hl := log_bounds hr.1
    (by change logScale (4451 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4447) (T := 43617556920427) (U := 149862018441)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4447

theorem row_4457 :
    (4457 : ℕ).Prime ∧ logScale (4457 : ℚ) = 12 ∧
      (84022311698 : ℤ) = ⌊logCenter (4457 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4457 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4457 : Reach 4457 43785588072783 149929334370 := by
  have hr := row_4457
  have hl := log_bounds hr.1
    (by change logScale (4457 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4451) (T := 43701565761085) (U := 149895695300)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4451

theorem row_4463 :
    (4463 : ℕ).Prime ∧ logScale (4463 : ℚ) = 12 ∧
      (84035764615 : ℤ) = ⌊logCenter (4463 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4463 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4463 : Reach 4463 43869623837398 149962935745 := by
  have hr := row_4463
  have hl := log_bounds hr.1
    (by change logScale (4463 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4457) (T := 43785588072783) (U := 149929334370)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4457

theorem row_4481 :
    (4481 : ℕ).Prime ∧ logScale (4481 : ℚ) = 12 ∧
      (84076015116 : ℤ) = ⌊logCenter (4481 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4481 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4481 : Reach 4481 43953699852514 149996409615 := by
  have hr := row_4481
  have hl := log_bounds hr.1
    (by change logScale (4481 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4463) (T := 43869623837398) (U := 149962935745)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4463

theorem row_4483 :
    (4483 : ℕ).Prime ∧ logScale (4483 : ℚ) = 12 ∧
      (84080477410 : ℤ) = ⌊logCenter (4483 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4483 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4483 : Reach 4483 44037780329924 150029876017 := by
  have hr := row_4483
  have hl := log_bounds hr.1
    (by change logScale (4483 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4481) (T := 43953699852514) (U := 149996409615)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4481

theorem row_4493 :
    (4493 : ℕ).Prime ∧ logScale (4493 : ℚ) = 12 ∧
      (84102759059 : ℤ) = ⌊logCenter (4493 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4493 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4493 : Reach 4493 44121883088983 150063275367 := by
  have hr := row_4493
  have hl := log_bounds hr.1
    (by change logScale (4493 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4483) (T := 44037780329924) (U := 150029876017)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4483

theorem row_4507 :
    (4507 : ℕ).Prime ∧ logScale (4507 : ℚ) = 12 ∧
      (84133870195 : ℤ) = ⌊logCenter (4507 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4507 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4507 : Reach 4507 44206016959178 150096578358 := by
  have hr := row_4507
  have hl := log_bounds hr.1
    (by change logScale (4507 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4493) (T := 44121883088983) (U := 150063275367)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4493

theorem row_4513 :
    (4513 : ℕ).Prime ∧ logScale (4513 : ℚ) = 12 ∧
      (84147173967 : ℤ) = ⌊logCenter (4513 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4513 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4513 : Reach 4513 44290164133145 150129844444 := by
  have hr := row_4513
  have hl := log_bounds hr.1
    (by change logScale (4513 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4507) (T := 44206016959178) (U := 150096578358)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4507

#print axioms reach_4513

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
