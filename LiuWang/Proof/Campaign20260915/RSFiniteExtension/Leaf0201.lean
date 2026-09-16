import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0200

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_5209 :
    (5209 : ℕ).Prime ∧ logScale (5209 : ℚ) = 12 ∧
      (85581431746 : ℤ) = ⌊logCenter (5209 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5209 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5209 : Reach 5209 51165837346311 152656191230 := by
  have hr := row_5209
  have hl := log_bounds hr.1
    (by change logScale (5209 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5197) (T := 51080255914565) (U := 152626884992)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5197

theorem row_5227 :
    (5227 : ℕ).Prime ∧ logScale (5227 : ℚ) = 12 ∧
      (85615927755 : ℤ) = ⌊logCenter (5227 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5227 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5227 : Reach 5227 51251453274066 152685402136 := by
  have hr := row_5227
  have hl := log_bounds hr.1
    (by change logScale (5227 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5209) (T := 51165837346311) (U := 152656191230)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5209

theorem row_5231 :
    (5231 : ℕ).Prime ∧ logScale (5231 : ℚ) = 12 ∧
      (85623577402 : ℤ) = ⌊logCenter (5231 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5231 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5231 : Reach 5231 51337076851468 152714596286 := by
  have hr := row_5231
  have hl := log_bounds hr.1
    (by change logScale (5231 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5227) (T := 51251453274066) (U := 152685402136)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5227

theorem row_5233 :
    (5233 : ℕ).Prime ∧ logScale (5233 : ℚ) = 12 ∧
      (85627400032 : ℤ) = ⌊logCenter (5233 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5233 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5233 : Reach 5233 51422704251500 152743784856 := by
  have hr := row_5233
  have hl := log_bounds hr.1
    (by change logScale (5233 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5231) (T := 51337076851468) (U := 152714596286)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5231

theorem row_5237 :
    (5237 : ℕ).Prime ∧ logScale (5237 : ℚ) = 12 ∧
      (85635040911 : ℤ) = ⌊logCenter (5237 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5237 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5237 : Reach 5237 51508339292411 152772956702 := by
  have hr := row_5237
  have hl := log_bounds hr.1
    (by change logScale (5237 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5233) (T := 51422704251500) (U := 152743784856)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5233

theorem row_5261 :
    (5261 : ℕ).Prime ∧ logScale (5261 : ℚ) = 12 ∧
      (85680763986 : ℤ) = ⌊logCenter (5261 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5261 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5261 : Reach 5261 51594020056397 152802000991 := by
  have hr := row_5261
  have hl := log_bounds hr.1
    (by change logScale (5261 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5237) (T := 51508339292411) (U := 152772956702)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5237

theorem row_5273 :
    (5273 : ℕ).Prime ∧ logScale (5273 : ℚ) = 12 ∧
      (85703547364 : ℤ) = ⌊logCenter (5273 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5273 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5273 : Reach 5273 51679723603761 152830984679 := by
  have hr := row_5273
  have hl := log_bounds hr.1
    (by change logScale (5273 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5261) (T := 51594020056397) (U := 152802000991)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5261

theorem row_5279 :
    (5279 : ℕ).Prime ∧ logScale (5279 : ℚ) = 12 ∧
      (85714919617 : ℤ) = ⌊logCenter (5279 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5279 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5279 : Reach 5279 51765438523378 152859940910 := by
  have hr := row_5279
  have hl := log_bounds hr.1
    (by change logScale (5279 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5273) (T := 51679723603761) (U := 152830984679)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5273

#print axioms reach_5279

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
