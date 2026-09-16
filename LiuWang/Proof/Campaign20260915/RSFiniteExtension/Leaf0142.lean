import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0141

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_4027 :
    (4027 : ℕ).Prime ∧ logScale (4027 : ℚ) = 11 ∧
      (83007769579 : ℤ) = ⌊logCenter (4027 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4027 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4027 : Reach 4027 39692264408548 148208133441 := by
  have hr := row_4027
  have hl := log_bounds hr.1
    (by change logScale (4027 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4021) (T := 39609256638969) (U := 148171329832)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4021

theorem row_4049 :
    (4049 : ℕ).Prime ∧ logScale (4049 : ℚ) = 11 ∧
      (83062252131 : ℤ) = ⌊logCenter (4049 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4049 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4049 : Reach 4049 39775326660679 148244746123 := by
  have hr := row_4049
  have hl := log_bounds hr.1
    (by change logScale (4049 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4027) (T := 39692264408548) (U := 148208133441)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4027

theorem row_4051 :
    (4051 : ℕ).Prime ∧ logScale (4051 : ℚ) = 11 ∧
      (83067190403 : ℤ) = ⌊logCenter (4051 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4051 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4051 : Reach 4051 39858393851082 148281349765 := by
  have hr := row_4051
  have hl := log_bounds hr.1
    (by change logScale (4051 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4049) (T := 39775326660679) (U := 148244746123)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4049

theorem row_4057 :
    (4057 : ℕ).Prime ∧ logScale (4057 : ℚ) = 11 ∧
      (83081990603 : ℤ) = ⌊logCenter (4057 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4057 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4057 : Reach 4057 39941475841685 148317908284 := by
  have hr := row_4057
  have hl := log_bounds hr.1
    (by change logScale (4057 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4051) (T := 39858393851082) (U := 148281349765)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4051

theorem row_4073 :
    (4073 : ℕ).Prime ∧ logScale (4073 : ℚ) = 11 ∧
      (83121351047 : ℤ) = ⌊logCenter (4073 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4073 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4073 : Reach 4073 40024597192732 148354332132 := by
  have hr := row_4073
  have hl := log_bounds hr.1
    (by change logScale (4073 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4057) (T := 39941475841685) (U := 148317908284)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4057

theorem row_4079 :
    (4079 : ℕ).Prime ∧ logScale (4079 : ℚ) = 11 ∧
      (83136071364 : ℤ) = ⌊logCenter (4079 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4079 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4079 : Reach 4079 40107733264096 148390711321 := by
  have hr := row_4079
  have hl := log_bounds hr.1
    (by change logScale (4079 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4073) (T := 40024597192732) (U := 148354332132)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4073

theorem row_4091 :
    (4091 : ℕ).Prime ∧ logScale (4091 : ℚ) = 11 ∧
      (83165447150 : ℤ) = ⌊logCenter (4091 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4091 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4091 : Reach 4091 40190898711246 148426992669 := by
  have hr := row_4091
  have hl := log_bounds hr.1
    (by change logScale (4091 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4079) (T := 40107733264096) (U := 148390711321)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4079

theorem row_4093 :
    (4093 : ℕ).Prime ∧ logScale (4093 : ℚ) = 11 ∧
      (83170334736 : ℤ) = ⌊logCenter (4093 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4093 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4093 : Reach 4093 40274069045982 148463265151 := by
  have hr := row_4093
  have hl := log_bounds hr.1
    (by change logScale (4093 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4091) (T := 40190898711246) (U := 148426992669)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4091

#print axioms reach_4093

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
