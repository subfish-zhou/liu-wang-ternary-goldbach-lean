import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block025

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_6361 :
    (6361 : ℕ).Prime ∧ logScale (6361 : ℚ) = 12 ∧
      (87579408735 : ℤ) = ⌊logCenter (6361 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6361 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6361 : Reach 6361 62949177346855 156289597197 := by
  have hr := row_6361
  have hl := log_bounds hr.1
    (by change logScale (6361 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6359) (T := 62861597938120) (U := 156265027224)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6359

theorem row_6367 :
    (6367 : ℕ).Prime ∧ logScale (6367 : ℚ) = 12 ∧
      (87588836768 : ℤ) = ⌊logCenter (6367 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6367 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6367 : Reach 6367 63036766183623 156314147873 := by
  have hr := row_6367
  have hl := log_bounds hr.1
    (by change logScale (6367 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6361) (T := 62949177346855) (U := 156289597197)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6361

theorem row_6373 :
    (6373 : ℕ).Prime ∧ logScale (6373 : ℚ) = 12 ∧
      (87598255921 : ℤ) = ⌊logCenter (6373 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6373 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6373 : Reach 6373 63124364439544 156338679284 := by
  have hr := row_6373
  have hl := log_bounds hr.1
    (by change logScale (6373 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6367) (T := 63036766183623) (U := 156314147873)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6367

theorem row_6379 :
    (6379 : ℕ).Prime ∧ logScale (6379 : ℚ) = 12 ∧
      (87607666211 : ℤ) = ⌊logCenter (6379 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6379 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6379 : Reach 6379 63211972105755 156363191464 := by
  have hr := row_6379
  have hl := log_bounds hr.1
    (by change logScale (6379 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6373) (T := 63124364439544) (U := 156338679284)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6373

theorem row_6389 :
    (6389 : ℕ).Prime ∧ logScale (6389 : ℚ) = 12 ∧
      (87623330374 : ℤ) = ⌊logCenter (6389 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6389 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6389 : Reach 6389 63299595436129 156387669109 := by
  have hr := row_6389
  have hl := log_bounds hr.1
    (by change logScale (6389 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6379) (T := 63211972105755) (U := 156363191464)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6379

theorem row_6397 :
    (6397 : ℕ).Prime ∧ logScale (6397 : ℚ) = 12 ∧
      (87635844063 : ℤ) = ⌊logCenter (6397 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6397 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6397 : Reach 6397 63387231280192 156412119965 := by
  have hr := row_6397
  have hl := log_bounds hr.1
    (by change logScale (6397 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6389) (T := 63299595436129) (U := 156387669109)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6389

theorem row_6421 :
    (6421 : ℕ).Prime ∧ logScale (6421 : ℚ) = 12 ∧
      (87673291446 : ℤ) = ⌊logCenter (6421 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6421 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6421 : Reach 6421 63474904571638 156436483224 := by
  have hr := row_6421
  have hl := log_bounds hr.1
    (by change logScale (6421 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6397) (T := 63387231280192) (U := 156412119965)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6397

theorem row_6427 :
    (6427 : ℕ).Prime ∧ logScale (6427 : ℚ) = 12 ∧
      (87682631422 : ℤ) = ⌊logCenter (6427 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6427 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6427 : Reach 6427 63562587203060 156460827526 := by
  have hr := row_6427
  have hl := log_bounds hr.1
    (by change logScale (6427 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6421) (T := 63474904571638) (U := 156436483224)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6421

#print axioms reach_6427

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
