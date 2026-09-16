import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0241

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_6113 :
    (6113 : ℕ).Prime ∧ logScale (6113 : ℚ) = 12 ∧
      (87181729269 : ℤ) = ⌊logCenter (6113 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6113 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6113 : Reach 6113 60152297744271 155491251493 := by
  have hr := row_6113
  have hl := log_bounds hr.1
    (by change logScale (6113 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6101) (T := 60065116015002) (U := 155465815332)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6101

theorem row_6121 :
    (6121 : ℕ).Prime ∧ logScale (6121 : ℚ) = 12 ∧
      (87194807577 : ℤ) = ⌊logCenter (6121 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6121 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6121 : Reach 6121 60239492551848 155516658561 := by
  have hr := row_6121
  have hl := log_bounds hr.1
    (by change logScale (6121 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6113) (T := 60152297744271) (U := 155491251493)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6113

theorem row_6131 :
    (6131 : ℕ).Prime ∧ logScale (6131 : ℚ) = 12 ∧
      (87211131446 : ℤ) = ⌊logCenter (6131 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6131 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6131 : Reach 6131 60326703683294 155542028326 := by
  have hr := row_6131
  have hl := log_bounds hr.1
    (by change logScale (6131 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6121) (T := 60239492551848) (U := 155516658561)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6121

theorem row_6133 :
    (6133 : ℕ).Prime ∧ logScale (6133 : ℚ) = 12 ∧
      (87214393025 : ℤ) = ⌊logCenter (6133 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6133 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6133 : Reach 6133 60413918076319 155567393954 := by
  have hr := row_6133
  have hl := log_bounds hr.1
    (by change logScale (6133 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6131) (T := 60326703683294) (U := 155542028326)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6131

theorem row_6143 :
    (6143 : ℕ).Prime ∧ logScale (6143 : ℚ) = 12 ∧
      (87230684980 : ℤ) = ⌊logCenter (6143 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6143 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6143 : Reach 6143 60501148761299 155592722413 := by
  have hr := row_6143
  have hl := log_bounds hr.1
    (by change logScale (6143 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6133) (T := 60413918076319) (U := 155567393954)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6133

theorem row_6151 :
    (6151 : ℕ).Prime ∧ logScale (6151 : ℚ) = 12 ∧
      (87243699460 : ℤ) = ⌊logCenter (6151 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6151 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6151 : Reach 6151 60588392460759 155618022043 := by
  have hr := row_6151
  have hl := log_bounds hr.1
    (by change logScale (6151 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6143) (T := 60501148761299) (U := 155592722413)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6143

theorem row_6163 :
    (6163 : ℕ).Prime ∧ logScale (6163 : ℚ) = 12 ∧
      (87263189478 : ℤ) = ⌊logCenter (6163 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6163 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6163 : Reach 6163 60675655650237 155643276510 := by
  have hr := row_6163
  have hl := log_bounds hr.1
    (by change logScale (6163 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6151) (T := 60588392460759) (U := 155618022043)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6151

theorem row_6173 :
    (6173 : ℕ).Prime ∧ logScale (6173 : ℚ) = 12 ∧
      (87279402192 : ℤ) = ⌊logCenter (6173 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6173 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6173 : Reach 6173 60762935052429 155668494151 := by
  have hr := row_6173
  have hl := log_bounds hr.1
    (by change logScale (6173 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6163) (T := 60675655650237) (U := 155643276510)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6163

#print axioms reach_6173

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
