import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0100

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_3203 :
    (3203 : ℕ).Prime ∧ logScale (3203 : ℚ) = 11 ∧
      (80718431467 : ℤ) = ⌊logCenter (3203 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3203 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3203 : Reach 3203 31172572962027 143991936298 := by
  have hr := row_3203
  have hl := log_bounds hr.1
    (by change logScale (3203 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3191) (T := 31091854530560) (U := 143946980963)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3191

theorem row_3209 :
    (3209 : ℕ).Prime ∧ logScale (3209 : ℚ) = 11 ∧
      (80737146382 : ℤ) = ⌊logCenter (3209 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3209 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3209 : Reach 3209 31253310108409 144036821565 := by
  have hr := row_3209
  have hl := log_bounds hr.1
    (by change logScale (3209 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3203) (T := 31172572962027) (U := 143991936298)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3203

theorem row_3217 :
    (3217 : ℕ).Prime ∧ logScale (3217 : ℚ) = 11 ∧
      (80762045243 : ℤ) = ⌊logCenter (3217 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3217 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3217 : Reach 3217 31334072153652 144081609134 := by
  have hr := row_3217
  have hl := log_bounds hr.1
    (by change logScale (3217 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3209) (T := 31253310108409) (U := 144036821565)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3209

theorem row_3221 :
    (3221 : ℕ).Prime ∧ logScale (3221 : ℚ) = 11 ∧
      (80774471464 : ℤ) = ⌊logCenter (3221 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3221 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3221 : Reach 3221 31414846625116 144126354976 := by
  have hr := row_3221
  have hl := log_bounds hr.1
    (by change logScale (3221 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3217) (T := 31334072153652) (U := 144081609134)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3217

theorem row_3229 :
    (3229 : ℕ).Prime ∧ logScale (3229 : ℚ) = 11 ∧
      (80799277678 : ℤ) = ⌊logCenter (3229 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3229 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3229 : Reach 3229 31495645902794 144171003785 := by
  have hr := row_3229
  have hl := log_bounds hr.1
    (by change logScale (3229 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3221) (T := 31414846625116) (U := 144126354976)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3221

theorem row_3251 :
    (3251 : ℕ).Prime ∧ logScale (3251 : ℚ) = 11 ∧
      (80867179174 : ℤ) = ⌊logCenter (3251 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3251 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3251 : Reach 3251 31576513081968 144215364094 := by
  have hr := row_3251
  have hl := log_bounds hr.1
    (by change logScale (3251 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3229) (T := 31495645902794) (U := 144171003785)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3229

theorem row_3253 :
    (3253 : ℕ).Prime ∧ logScale (3253 : ℚ) = 11 ∧
      (80873329236 : ℤ) = ⌊logCenter (3253 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3253 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3253 : Reach 3253 31657386411204 144259710762 := by
  have hr := row_3253
  have hl := log_bounds hr.1
    (by change logScale (3253 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3251) (T := 31576513081968) (U := 144215364094)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3251

theorem row_3257 :
    (3257 : ℕ).Prime ∧ logScale (3257 : ℚ) = 11 ∧
      (80885618024 : ℤ) = ⌊logCenter (3257 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3257 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3257 : Reach 3257 31738272029228 144304016570 := by
  have hr := row_3257
  have hl := log_bounds hr.1
    (by change logScale (3257 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3253) (T := 31657386411204) (U := 144259710762)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3253

#print axioms reach_3257

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
