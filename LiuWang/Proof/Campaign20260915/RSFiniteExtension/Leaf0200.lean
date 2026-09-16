import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block019

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_5119 :
    (5119 : ℕ).Prime ∧ logScale (5119 : ℚ) = 12 ∧
      (85407143833 : ℤ) = ⌊logCenter (5119 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5119 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5119 : Reach 5119 50481687185692 152420425319 := by
  have hr := row_5119
  have hl := log_bounds hr.1
    (by change logScale (5119 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5113) (T := 50396280041859) (U := 152390649889)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5113

theorem row_5147 :
    (5147 : ℕ).Prime ∧ logScale (5147 : ℚ) = 12 ∧
      (85461692965 : ℤ) = ⌊logCenter (5147 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5147 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5147 : Reach 5147 50567148878657 152450044524 := by
  have hr := row_5147
  have hl := log_bounds hr.1
    (by change logScale (5147 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5119) (T := 50481687185692) (U := 152420425319)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5119

theorem row_5153 :
    (5153 : ℕ).Prime ∧ logScale (5153 : ℚ) = 12 ∧
      (85473343452 : ℤ) = ⌊logCenter (5153 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5153 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5153 : Reach 5153 50652622222109 152479634983 := by
  have hr := row_5153
  have hl := log_bounds hr.1
    (by change logScale (5153 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5147) (T := 50567148878657) (U := 152450044524)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5147

theorem row_5167 :
    (5167 : ℕ).Prime ∧ logScale (5167 : ℚ) = 12 ∧
      (85500475251 : ℤ) = ⌊logCenter (5167 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5167 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5167 : Reach 5167 50738122697360 152509150979 := by
  have hr := row_5167
  have hl := log_bounds hr.1
    (by change logScale (5167 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5153) (T := 50652622222109) (U := 152479634983)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5153

theorem row_5171 :
    (5171 : ℕ).Prime ∧ logScale (5171 : ℚ) = 12 ∧
      (85508213692 : ℤ) = ⌊logCenter (5171 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5171 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5171 : Reach 5171 50823630911052 152538649848 := by
  have hr := row_5171
  have hl := log_bounds hr.1
    (by change logScale (5171 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5167) (T := 50738122697360) (U := 152509150979)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5167

theorem row_5179 :
    (5179 : ℕ).Prime ∧ logScale (5179 : ℚ) = 12 ∧
      (85523672633 : ℤ) = ⌊logCenter (5179 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5179 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5179 : Reach 5179 50909154583685 152568108838 := by
  have hr := row_5179
  have hl := log_bounds hr.1
    (by change logScale (5179 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5171) (T := 50823630911052) (U := 152538649848)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5171

theorem row_5189 :
    (5189 : ℕ).Prime ∧ logScale (5189 : ℚ) = 12 ∧
      (85542962762 : ℤ) = ⌊logCenter (5189 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5189 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5189 : Reach 5189 50994697546447 152597516724 := by
  have hr := row_5189
  have hl := log_bounds hr.1
    (by change logScale (5189 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5179) (T := 50909154583685) (U := 152568108838)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5179

theorem row_5197 :
    (5197 : ℕ).Prime ∧ logScale (5197 : ℚ) = 12 ∧
      (85558368118 : ℤ) = ⌊logCenter (5197 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5197 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5197 : Reach 5197 51080255914565 152626884992 := by
  have hr := row_5197
  have hl := log_bounds hr.1
    (by change logScale (5197 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5189) (T := 50994697546447) (U := 152597516724)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5189

#print axioms reach_5197

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
