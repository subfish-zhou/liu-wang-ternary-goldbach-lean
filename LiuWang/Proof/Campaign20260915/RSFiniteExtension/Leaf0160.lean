import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block015

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_4289 :
    (4289 : ℕ).Prime ∧ logScale (4289 : ℚ) = 12 ∧
      (83638088813 : ℤ) = ⌊logCenter (4289 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4289 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4289 : Reach 4289 42359909849308 149349335980 := by
  have hr := row_4289
  have hl := log_bounds hr.1
    (by change logScale (4289 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4283) (T := 42276271760495) (U := 149314514498)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4283

theorem row_4297 :
    (4297 : ℕ).Prime ∧ logScale (4297 : ℚ) = 12 ∧
      (83656723806 : ℤ) = ⌊logCenter (4297 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4297 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4297 : Reach 4297 42443566573114 149384100724 := by
  have hr := row_4297
  have hl := log_bounds hr.1
    (by change logScale (4297 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4289) (T := 42359909849308) (U := 149349335980)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4289

theorem row_4327 :
    (4327 : ℕ).Prime ∧ logScale (4327 : ℚ) = 12 ∧
      (83726297371 : ℤ) = ⌊logCenter (4327 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4327 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4327 : Reach 4327 42527292870485 149418632417 := by
  have hr := row_4327
  have hl := log_bounds hr.1
    (by change logScale (4327 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4297) (T := 42443566573114) (U := 149384100724)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4297

theorem row_4337 :
    (4337 : ℕ).Prime ∧ logScale (4337 : ℚ) = 12 ∧
      (83749381407 : ℤ) = ⌊logCenter (4337 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4337 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4337 : Reach 4337 42611042251892 149453092434 := by
  have hr := row_4337
  have hl := log_bounds hr.1
    (by change logScale (4337 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4327) (T := 42527292870485) (U := 149418632417)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4327

theorem row_4339 :
    (4339 : ℕ).Prime ∧ logScale (4339 : ℚ) = 12 ∧
      (83753991826 : ℤ) = ⌊logCenter (4339 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4339 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4339 : Reach 4339 42694796243718 149487544507 := by
  have hr := row_4339
  have hl := log_bounds hr.1
    (by change logScale (4339 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4337) (T := 42611042251892) (U := 149453092434)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4337

theorem row_4349 :
    (4349 : ℕ).Prime ∧ logScale (4349 : ℚ) = 12 ∧
      (83777012094 : ℤ) = ⌊logCenter (4349 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4349 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4349 : Reach 4349 42778573255812 149521925268 := by
  have hr := row_4349
  have hl := log_bounds hr.1
    (by change logScale (4349 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4339) (T := 42694796243718) (U := 149487544507)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4339

theorem row_4357 :
    (4357 : ℕ).Prime ∧ logScale (4357 : ℚ) = 12 ∧
      (83795390229 : ℤ) = ⌊logCenter (4357 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4357 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4357 : Reach 4357 42862368646041 149556250779 := by
  have hr := row_4357
  have hl := log_bounds hr.1
    (by change logScale (4357 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4349) (T := 42778573255812) (U := 149521925268)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4349

theorem row_4363 :
    (4363 : ℕ).Prime ∧ logScale (4363 : ℚ) = 12 ∧
      (83809151700 : ℤ) = ⌊logCenter (4363 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4363 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4363 : Reach 4363 42946177797741 149590536944 := by
  have hr := row_4363
  have hl := log_bounds hr.1
    (by change logScale (4363 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4357) (T := 42862368646041) (U := 149556250779)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4357

#print axioms reach_4363

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
