import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0251

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_6311 :
    (6311 : ℕ).Prime ∧ logScale (6311 : ℚ) = 12 ∧
      (87500494184 : ℤ) = ⌊logCenter (6311 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6311 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6311 : Reach 6311 62248803708569 156092501769 := by
  have hr := row_6311
  have hl := log_bounds hr.1
    (by change logScale (6311 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6301) (T := 62161303214385) (U := 156067768366)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6301

theorem row_6317 :
    (6317 : ℕ).Prime ∧ logScale (6317 : ℚ) = 12 ∧
      (87509996877 : ℤ) = ⌊logCenter (6317 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6317 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6317 : Reach 6317 62336313705446 156117215592 := by
  have hr := row_6317
  have hl := log_bounds hr.1
    (by change logScale (6317 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6311) (T := 62248803708569) (U := 156092501769)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6311

theorem row_6323 :
    (6323 : ℕ).Prime ∧ logScale (6323 : ℚ) = 12 ∧
      (87519490549 : ℤ) = ⌊logCenter (6323 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6323 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6323 : Reach 6323 62423833195995 156141909869 := by
  have hr := row_6323
  have hl := log_bounds hr.1
    (by change logScale (6323 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6317) (T := 62336313705446) (U := 156117215592)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6317

theorem row_6329 :
    (6329 : ℕ).Prime ∧ logScale (6329 : ℚ) = 12 ∧
      (87528975216 : ℤ) = ⌊logCenter (6329 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6329 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6329 : Reach 6329 62511362171211 156166584634 := by
  have hr := row_6329
  have hl := log_bounds hr.1
    (by change logScale (6329 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6323) (T := 62423833195995) (U := 156141909869)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6323

theorem row_6337 :
    (6337 : ℕ).Prime ∧ logScale (6337 : ℚ) = 12 ∧
      (87541607462 : ℤ) = ⌊logCenter (6337 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6337 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6337 : Reach 6337 62598903778673 156191232138 := by
  have hr := row_6337
  have hl := log_bounds hr.1
    (by change logScale (6337 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6329) (T := 62511362171211) (U := 156166584634)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6329

theorem row_6343 :
    (6343 : ℕ).Prime ∧ logScale (6343 : ℚ) = 12 ∧
      (87551071185 : ℤ) = ⌊logCenter (6343 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6343 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6343 : Reach 6343 62686454849858 156215860210 := by
  have hr := row_6343
  have hl := log_bounds hr.1
    (by change logScale (6343 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6337) (T := 62598903778673) (U := 156191232138)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6337

theorem row_6353 :
    (6353 : ℕ).Prime ∧ logScale (6353 : ℚ) = 12 ∧
      (87566824181 : ℤ) = ⌊logCenter (6353 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6353 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6353 : Reach 6353 62774021674039 156240453387 := by
  have hr := row_6353
  have hl := log_bounds hr.1
    (by change logScale (6353 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6343) (T := 62686454849858) (U := 156215860210)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6343

theorem row_6359 :
    (6359 : ℕ).Prime ∧ logScale (6359 : ℚ) = 12 ∧
      (87576264081 : ℤ) = ⌊logCenter (6359 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6359 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6359 : Reach 6359 62861597938120 156265027224 := by
  have hr := row_6359
  have hl := log_bounds hr.1
    (by change logScale (6359 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6353) (T := 62774021674039) (U := 156240453387)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6353

#print axioms reach_6359

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
