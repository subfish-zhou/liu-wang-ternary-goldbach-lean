import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block005

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_2351 :
    (2351 : ℕ).Prime ∧ logScale (2351 : ℚ) = 11 ∧
      (77625960456 : ℤ) = ⌊logCenter (2351 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2351 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2351 : Reach 2351 22933814098469 138640299114 := by
  have hr := row_2351
  have hl := log_bounds hr.1
    (by change logScale (2351 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2347) (T := 22856188138013) (U := 138581328335)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2347

theorem row_2357 :
    (2357 : ℕ).Prime ∧ logScale (2357 : ℚ) = 11 ∧
      (77651449000 : ℤ) = ⌊logCenter (2357 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2357 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2357 : Reach 2357 23011465547469 138699144742 := by
  have hr := row_2357
  have hl := log_bounds hr.1
    (by change logScale (2357 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2351) (T := 22933814098469) (U := 138640299114)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2351

theorem row_2371 :
    (2371 : ℕ).Prime ∧ logScale (2371 : ℚ) = 11 ∧
      (77710670832 : ℤ) = ⌊logCenter (2371 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2371 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2371 : Reach 2371 23089176218301 138757667588 := by
  have hr := row_2371
  have hl := log_bounds hr.1
    (by change logScale (2371 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2357) (T := 23011465547469) (U := 138699144742)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2357

theorem row_2377 :
    (2377 : ℕ).Prime ∧ logScale (2377 : ℚ) = 11 ∧
      (77735944645 : ℤ) = ⌊logCenter (2377 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2377 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2377 : Reach 2377 23166912162946 138816067280 := by
  have hr := row_2377
  have hl := log_bounds hr.1
    (by change logScale (2377 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2371) (T := 23089176218301) (U := 138757667588)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2371

theorem row_2381 :
    (2381 : ℕ).Prime ∧ logScale (2381 : ℚ) = 11 ∧
      (77752758436 : ℤ) = ⌊logCenter (2381 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2381 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2381 : Reach 2381 23244664921382 138874393359 := by
  have hr := row_2381
  have hl := log_bounds hr.1
    (by change logScale (2381 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2377) (T := 23166912162946) (U := 138816067280)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2377

theorem row_2383 :
    (2383 : ℕ).Prime ∧ logScale (2383 : ℚ) = 11 ∧
      (77761154742 : ℤ) = ⌊logCenter (2383 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2383 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2383 : Reach 2383 23322426076124 138932694952 := by
  have hr := row_2383
  have hl := log_bounds hr.1
    (by change logScale (2383 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2381) (T := 23244664921382) (U := 138874393359)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2381

theorem row_2389 :
    (2389 : ℕ).Prime ∧ logScale (2389 : ℚ) = 11 ∧
      (77786301444 : ℤ) = ⌊logCenter (2389 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2389 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2389 : Reach 2389 23400212377568 138990874473 := by
  have hr := row_2389
  have hl := log_bounds hr.1
    (by change logScale (2389 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2383) (T := 23322426076124) (U := 138932694952)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2383

theorem row_2393 :
    (2393 : ℕ).Prime ∧ logScale (2393 : ℚ) = 11 ∧
      (77803030850 : ℤ) = ⌊logCenter (2393 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2393 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2393 : Reach 2393 23478015408418 139048981026 := by
  have hr := row_2393
  have hl := log_bounds hr.1
    (by change logScale (2393 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2389) (T := 23400212377568) (U := 138990874473)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2389

#print axioms reach_2393

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
