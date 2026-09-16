import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block010

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_3329 :
    (3329 : ℕ).Prime ∧ logScale (3329 : ℚ) = 11 ∧
      (81104272347 : ℤ) = ⌊logCenter (3329 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3329 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3329 : Reach 3329 32467484604389 144697908905 := by
  have hr := row_3329
  have hl := log_bounds hr.1
    (by change logScale (3329 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3323) (T := 32386380332042) (U := 144654443026)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3323

theorem row_3331 :
    (3331 : ℕ).Prime ∧ logScale (3331 : ℚ) = 11 ∧
      (81110278353 : ℤ) = ⌊logCenter (3331 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3331 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3331 : Reach 3331 32548594882742 144741361731 := by
  have hr := row_3331
  have hl := log_bounds hr.1
    (by change logScale (3331 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3329) (T := 32467484604389) (U := 144697908905)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3329

theorem row_3343 :
    (3343 : ℕ).Prime ∧ logScale (3343 : ℚ) = 11 ∧
      (81146238835 : ℤ) = ⌊logCenter (3343 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3343 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3343 : Reach 3343 32629741121577 144784671535 := by
  have hr := row_3343
  have hl := log_bounds hr.1
    (by change logScale (3343 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3331) (T := 32548594882742) (U := 144741361731)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3331

theorem row_3347 :
    (3347 : ℕ).Prime ∧ logScale (3347 : ℚ) = 11 ∧
      (81158196983 : ℤ) = ⌊logCenter (3347 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3347 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3347 : Reach 3347 32710899318560 144827942507 := by
  have hr := row_3347
  have hl := log_bounds hr.1
    (by change logScale (3347 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3343) (T := 32629741121577) (U := 144784671535)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3343

theorem row_3359 :
    (3359 : ℕ).Prime ∧ logScale (3359 : ℚ) = 11 ∧
      (81193985867 : ℤ) = ⌊logCenter (3359 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3359 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3359 : Reach 3359 32792093304427 144871071734 := by
  have hr := row_3359
  have hl := log_bounds hr.1
    (by change logScale (3359 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3347) (T := 32710899318560) (U := 144827942507)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3347

theorem row_3361 :
    (3361 : ℕ).Prime ∧ logScale (3361 : ℚ) = 11 ∧
      (81199938248 : ℤ) = ⌊logCenter (3361 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3361 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3361 : Reach 3361 32873293242675 144914188125 := by
  have hr := row_3361
  have hl := log_bounds hr.1
    (by change logScale (3361 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3359) (T := 32792093304427) (U := 144871071734)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3359

theorem row_3371 :
    (3371 : ℕ).Prime ∧ logScale (3371 : ℚ) = 11 ∧
      (81229647123 : ℤ) = ⌊logCenter (3371 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3371 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3371 : Reach 3371 32954522889798 144957189368 := by
  have hr := row_3371
  have hl := log_bounds hr.1
    (by change logScale (3371 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3361) (T := 32873293242675) (U := 144914188125)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3361

theorem row_3373 :
    (3373 : ℕ).Prime ∧ logScale (3373 : ℚ) = 11 ∧
      (81235578322 : ℤ) = ⌊logCenter (3373 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3373 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3373 : Reach 3373 33035758468120 145000177859 := by
  have hr := row_3373
  have hl := log_bounds hr.1
    (by change logScale (3373 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3371) (T := 32954522889798) (U := 144957189368)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3371

#print axioms reach_3373

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
