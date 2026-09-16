import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0250

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_6257 :
    (6257 : ℕ).Prime ∧ logScale (6257 : ℚ) = 12 ∧
      (87414561128 : ℤ) = ⌊logCenter (6257 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6257 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6257 : Reach 6257 61549133471100 155893917380 := by
  have hr := row_6257
  have hl := log_bounds hr.1
    (by change logScale (6257 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6247) (T := 61461718909972) (U := 155869002258)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6247

theorem row_6263 :
    (6263 : ℕ).Prime ∧ logScale (6263 : ℚ) = 12 ∧
      (87424145794 : ℤ) = ⌊logCenter (6263 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6263 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6263 : Reach 6263 61636557616894 155918812608 := by
  have hr := row_6263
  have hl := log_bounds hr.1
    (by change logScale (6263 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6257) (T := 61549133471100) (U := 155893917380)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6257

theorem row_6269 :
    (6269 : ℕ).Prime ∧ logScale (6269 : ℚ) = 12 ∧
      (87433721281 : ℤ) = ⌊logCenter (6269 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6269 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6269 : Reach 6269 61723991338175 155943687977 := by
  have hr := row_6269
  have hl := log_bounds hr.1
    (by change logScale (6269 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6263) (T := 61636557616894) (U := 155918812608)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6263

theorem row_6271 :
    (6271 : ℕ).Prime ∧ logScale (6271 : ℚ) = 12 ∧
      (87436911074 : ℤ) = ⌊logCenter (6271 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6271 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6271 : Reach 6271 61811428249249 155968559379 := by
  have hr := row_6271
  have hl := log_bounds hr.1
    (by change logScale (6271 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6269) (T := 61723991338175) (U := 155943687977)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6269

theorem row_6277 :
    (6277 : ℕ).Prime ∧ logScale (6277 : ℚ) = 12 ∧
      (87446474351 : ℤ) = ⌊logCenter (6277 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6277 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6277 : Reach 6277 61898874723600 155993410966 := by
  have hr := row_6277
  have hl := log_bounds hr.1
    (by change logScale (6277 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6271) (T := 61811428249249) (U := 155968559379)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6271

theorem row_6287 :
    (6287 : ℕ).Prime ∧ logScale (6287 : ℚ) = 12 ∧
      (87462392852 : ℤ) = ⌊logCenter (6287 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6287 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6287 : Reach 6287 61986337116452 156018226972 := by
  have hr := row_6287
  have hl := log_bounds hr.1
    (by change logScale (6287 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6277) (T := 61898874723600) (U := 155993410966)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6277

theorem row_6299 :
    (6299 : ℕ).Prime ∧ logScale (6299 : ℚ) = 12 ∧
      (87481461665 : ℤ) = ⌊logCenter (6299 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6299 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6299 : Reach 6299 62073818578117 156042999635 := by
  have hr := row_6299
  have hl := log_bounds hr.1
    (by change logScale (6299 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6287) (T := 61986337116452) (U := 156018226972)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6287

theorem row_6301 :
    (6301 : ℕ).Prime ∧ logScale (6301 : ℚ) = 12 ∧
      (87484636268 : ℤ) = ⌊logCenter (6301 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6301 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6301 : Reach 6301 62161303214385 156067768366 := by
  have hr := row_6301
  have hl := log_bounds hr.1
    (by change logScale (6301 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6299) (T := 62073818578117) (U := 156042999635)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6299

#print axioms reach_6301

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
