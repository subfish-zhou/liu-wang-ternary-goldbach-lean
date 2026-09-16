import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0090

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_2971 :
    (2971 : ℕ).Prime ∧ logScale (2971 : ℚ) = 11 ∧
      (79966538726 : ℤ) = ⌊logCenter (2971 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2971 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2971 : Reach 2971 29243531766352 142879395238 := by
  have hr := row_2971
  have hl := log_bounds hr.1
    (by change logScale (2971 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2969) (T := 29163565227626) (U := 142831303889)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2969

theorem row_2999 :
    (2999 : ℕ).Prime ∧ logScale (2999 : ℚ) = 11 ∧
      (80060341758 : ℤ) = ⌊logCenter (2999 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2999 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2999 : Reach 2999 29323592108110 142927053476 := by
  have hr := row_2999
  have hl := log_bounds hr.1
    (by change logScale (2999 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2971) (T := 29243531766352) (U := 142879395238)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2971

theorem row_3001 :
    (3001 : ℕ).Prime ∧ logScale (3001 : ℚ) = 11 ∧
      (80067008425 : ℤ) = ⌊logCenter (3001 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3001 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3001 : Reach 3001 29403659116535 142974695828 := by
  have hr := row_3001
  have hl := log_bounds hr.1
    (by change logScale (3001 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2999) (T := 29323592108110) (U := 142927053476)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2999

theorem row_3011 :
    (3011 : ℕ).Prime ∧ logScale (3011 : ℚ) = 11 ∧
      (80100275256 : ℤ) = ⌊logCenter (3011 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3011 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3011 : Reach 3011 29483759391791 143022195727 := by
  have hr := row_3011
  have hl := log_bounds hr.1
    (by change logScale (3011 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3001) (T := 29403659116535) (U := 142974695828)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3001

theorem row_3019 :
    (3019 : ℕ).Prime ∧ logScale (3019 : ℚ) = 11 ∧
      (80126809268 : ℤ) = ⌊logCenter (3019 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3019 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3019 : Reach 3019 29563886201059 143069585454 := by
  have hr := row_3019
  have hl := log_bounds hr.1
    (by change logScale (3019 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3011) (T := 29483759391791) (U := 143022195727)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3011

theorem row_3023 :
    (3023 : ℕ).Prime ∧ logScale (3023 : ℚ) = 11 ∧
      (80140049919 : ℤ) = ⌊logCenter (3023 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3023 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3023 : Reach 3023 29644026250978 143116928137 := by
  have hr := row_3023
  have hl := log_bounds hr.1
    (by change logScale (3023 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3019) (T := 29563886201059) (U := 143069585454)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3019

theorem row_3037 :
    (3037 : ℕ).Prime ∧ logScale (3037 : ℚ) = 11 ∧
      (80186254621 : ℤ) = ⌊logCenter (3037 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3037 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3037 : Reach 3037 29724212505599 143164068101 := by
  have hr := row_3037
  have hl := log_bounds hr.1
    (by change logScale (3037 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3023) (T := 29644026250978) (U := 143116928137)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3023

theorem row_3041 :
    (3041 : ℕ).Prime ∧ logScale (3041 : ℚ) = 11 ∧
      (80199416848 : ℤ) = ⌊logCenter (3041 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3041 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3041 : Reach 3041 29804411922447 143211161545 := by
  have hr := row_3041
  have hl := log_bounds hr.1
    (by change logScale (3041 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3037) (T := 29724212505599) (U := 143164068101)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3037

#print axioms reach_3041

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
