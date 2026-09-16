import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block024

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_6197 :
    (6197 : ℕ).Prime ∧ logScale (6197 : ℚ) = 12 ∧
      (87318205798 : ℤ) = ⌊logCenter (6197 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6197 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6197 : Reach 6197 60850253258227 155693618182 := by
  have hr := row_6197
  have hl := log_bounds hr.1
    (by change logScale (6197 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6173) (T := 60762935052429) (U := 155668494151)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6173

theorem row_6199 :
    (6199 : ℕ).Prime ∧ logScale (6199 : ℚ) = 12 ∧
      (87321432645 : ℤ) = ⌊logCenter (6199 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6199 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6199 : Reach 6199 60937574690872 155718738160 := by
  have hr := row_6199
  have hl := log_bounds hr.1
    (by change logScale (6199 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6197) (T := 60850253258227) (U := 155693618182)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6197

theorem row_6203 :
    (6203 : ℕ).Prime ∧ logScale (6203 : ℚ) = 12 ∧
      (87327883218 : ℤ) = ⌊logCenter (6203 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6203 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6203 : Reach 6203 61024902574090 155743845987 := by
  have hr := row_6203
  have hl := log_bounds hr.1
    (by change logScale (6203 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6199) (T := 60937574690872) (U := 155718738160)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6199

theorem row_6211 :
    (6211 : ℕ).Prime ∧ logScale (6211 : ℚ) = 12 ∧
      (87340771894 : ℤ) = ⌊logCenter (6211 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6211 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6211 : Reach 6211 61112243345984 155768925512 := by
  have hr := row_6211
  have hl := log_bounds hr.1
    (by change logScale (6211 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6203) (T := 61024902574090) (U := 155743845987)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6203

theorem row_6217 :
    (6217 : ℕ).Prime ∧ logScale (6217 : ℚ) = 12 ∧
      (87350427511 : ℤ) = ⌊logCenter (6217 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6217 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6217 : Reach 6217 61199593773495 155793984863 := by
  have hr := row_6217
  have hl := log_bounds hr.1
    (by change logScale (6217 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6211) (T := 61112243345984) (U := 155768925512)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6211

theorem row_6221 :
    (6221 : ℕ).Prime ∧ logScale (6221 : ℚ) = 12 ∧
      (87356859413 : ℤ) = ⌊logCenter (6221 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6221 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6221 : Reach 6221 61286950632908 155819032128 := by
  have hr := row_6221
  have hl := log_bounds hr.1
    (by change logScale (6221 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6217) (T := 61199593773495) (U := 155793984863)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6217

theorem row_6229 :
    (6229 : ℕ).Prime ∧ logScale (6229 : ℚ) = 12 ∧
      (87369710821 : ℤ) = ⌊logCenter (6229 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6229 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6229 : Reach 6229 61374320343729 155844051241 := by
  have hr := row_6229
  have hl := log_bounds hr.1
    (by change logScale (6229 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6221) (T := 61286950632908) (U := 155819032128)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6221

theorem row_6247 :
    (6247 : ℕ).Prime ∧ logScale (6247 : ℚ) = 12 ∧
      (87398566243 : ℤ) = ⌊logCenter (6247 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6247 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6247 : Reach 6247 61461718909972 155869002258 := by
  have hr := row_6247
  have hl := log_bounds hr.1
    (by change logScale (6247 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6229) (T := 61374320343729) (U := 155844051241)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6229

#print axioms reach_6247

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
