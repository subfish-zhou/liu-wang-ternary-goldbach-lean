import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block014

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_4099 :
    (4099 : ℕ).Prime ∧ logScale (4099 : ℚ) = 12 ∧
      (83184983173 : ℤ) = ⌊logCenter (4099 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4099 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4099 : Reach 4099 40357254029155 148499493376 := by
  have hr := row_4099
  have hl := log_bounds hr.1
    (by change logScale (4099 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4093) (T := 40274069045982) (U := 148463265151)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4093

theorem row_4111 :
    (4111 : ℕ).Prime ∧ logScale (4111 : ℚ) = 12 ∧
      (83214215837 : ℤ) = ⌊logCenter (4111 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4111 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4111 : Reach 4111 40440468244992 148535624640 := by
  have hr := row_4111
  have hl := log_bounds hr.1
    (by change logScale (4111 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4099) (T := 40357254029155) (U := 148499493376)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4099

theorem row_4127 :
    (4127 : ℕ).Prime ∧ logScale (4127 : ℚ) = 12 ∧
      (83253060266 : ℤ) = ⌊logCenter (4127 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4127 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4127 : Reach 4127 40523721305258 148571624550 := by
  have hr := row_4127
  have hl := log_bounds hr.1
    (by change logScale (4127 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4111) (T := 40440468244992) (U := 148535624640)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4111

theorem row_4129 :
    (4129 : ℕ).Prime ∧ logScale (4129 : ℚ) = 12 ∧
      (83257905227 : ℤ) = ⌊logCenter (4129 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4129 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4129 : Reach 4129 40606979210485 148607615739 := by
  have hr := row_4129
  have hl := log_bounds hr.1
    (by change logScale (4129 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4127) (T := 40523721305258) (U := 148571624550)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4127

theorem row_4133 :
    (4133 : ℕ).Prime ∧ logScale (4133 : ℚ) = 12 ∧
      (83267588113 : ℤ) = ⌊logCenter (4133 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4133 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4133 : Reach 4133 40690246798598 148643580797 := by
  have hr := row_4133
  have hl := log_bounds hr.1
    (by change logScale (4133 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4129) (T := 40606979210485) (U := 148607615739)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4129

theorem row_4139 :
    (4139 : ℕ).Prime ∧ logScale (4139 : ℚ) = 12 ∧
      (83282094886 : ℤ) = ⌊logCenter (4139 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4139 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4139 : Reach 4139 40773528893484 148679502397 := by
  have hr := row_4139
  have hl := log_bounds hr.1
    (by change logScale (4139 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4133) (T := 40690246798598) (U := 148643580797)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4133

theorem row_4153 :
    (4153 : ℕ).Prime ∧ logScale (4153 : ℚ) = 12 ∧
      (83315862405 : ℤ) = ⌊logCenter (4153 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4153 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4153 : Reach 4153 40856844755889 148715311526 := by
  have hr := row_4153
  have hl := log_bounds hr.1
    (by change logScale (4153 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4139) (T := 40773528893484) (U := 148679502397)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4139

theorem row_4157 :
    (4157 : ℕ).Prime ∧ logScale (4157 : ℚ) = 12 ∧
      (83325489361 : ℤ) = ⌊logCenter (4157 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4157 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4157 : Reach 4157 40940170245250 148751094806 := by
  have hr := row_4157
  have hl := log_bounds hr.1
    (by change logScale (4157 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4153) (T := 40856844755889) (U := 148715311526)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4153

#print axioms reach_4157

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
