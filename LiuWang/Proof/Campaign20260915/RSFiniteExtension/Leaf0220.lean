import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block021

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_5557 :
    (5557 : ℕ).Prime ∧ logScale (5557 : ℚ) = 12 ∧
      (86228136701 : ℤ) = ⌊logCenter (5557 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5557 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5557 : Reach 5557 54603023497798 153792820901 := by
  have hr := row_5557
  have hl := log_bounds hr.1
    (by change logScale (5557 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5531) (T := 54516795361097) (U := 153765145388)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5531

theorem row_5563 :
    (5563 : ℕ).Prime ∧ logScale (5563 : ℚ) = 12 ∧
      (86238928069 : ℤ) = ⌊logCenter (5563 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5563 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5563 : Reach 5563 54689262425867 153820471535 := by
  have hr := row_5563
  have hl := log_bounds hr.1
    (by change logScale (5563 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5557) (T := 54603023497798) (U := 153792820901)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5557

theorem row_5569 :
    (5569 : ℕ).Prime ∧ logScale (5569 : ℚ) = 12 ∧
      (86249707804 : ℤ) = ⌊logCenter (5569 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5569 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5569 : Reach 5569 54775512133671 153848097339 := by
  have hr := row_5569
  have hl := log_bounds hr.1
    (by change logScale (5569 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5563) (T := 54689262425867) (U := 153820471535)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5563

theorem row_5573 :
    (5573 : ℕ).Prime ∧ logScale (5573 : ℚ) = 12 ∧
      (86256887844 : ℤ) = ⌊logCenter (5573 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5573 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5573 : Reach 5573 54861769021515 153875708269 := by
  have hr := row_5573
  have hl := log_bounds hr.1
    (by change logScale (5573 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5569) (T := 54775512133671) (U := 153848097339)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5569

theorem row_5581 :
    (5581 : ℕ).Prime ∧ logScale (5581 : ℚ) = 12 ∧
      (86271232476 : ℤ) = ⌊logCenter (5581 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5581 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5581 : Reach 5581 54948040253991 153903284561 := by
  have hr := row_5581
  have hl := log_bounds hr.1
    (by change logScale (5581 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5573) (T := 54861769021515) (U := 153875708269)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5573

theorem row_5591 :
    (5591 : ℕ).Prime ∧ logScale (5591 : ℚ) = 12 ∧
      (86289134379 : ℤ) = ⌊logCenter (5591 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5591 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5591 : Reach 5591 55034329388370 153930816455 := by
  have hr := row_5591
  have hl := log_bounds hr.1
    (by change logScale (5591 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5581) (T := 54948040253991) (U := 153903284561)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5581

theorem row_5623 :
    (5623 : ℕ).Prime ∧ logScale (5623 : ℚ) = 12 ∧
      (86346206051 : ℤ) = ⌊logCenter (5623 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5623 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5623 : Reach 5623 55120675594421 153958196537 := by
  have hr := row_5623
  have hl := log_bounds hr.1
    (by change logScale (5623 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5591) (T := 55034329388370) (U := 153930816455)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5591

theorem row_5639 :
    (5639 : ℕ).Prime ∧ logScale (5639 : ℚ) = 12 ∧
      (86374620206 : ℤ) = ⌊logCenter (5639 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5639 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5639 : Reach 5639 55207050214627 153985503773 := by
  have hr := row_5639
  have hl := log_bounds hr.1
    (by change logScale (5639 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5623) (T := 55120675594421) (U := 153958196537)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5623

#print axioms reach_5639

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
