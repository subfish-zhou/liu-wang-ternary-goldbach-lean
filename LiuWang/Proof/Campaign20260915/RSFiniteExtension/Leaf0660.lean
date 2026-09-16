import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block065
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_15313 : PrimeGap 15307 15313 :=
  (primeGap_of_factors (ds := [2, 3, 2, 61, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15313 :
    (15313 : ℕ).Prime ∧ logScale (15313 : ℚ) = 13 ∧
      (96364574164 : ℤ) = ⌊logCenter (15313 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15313 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15313 : Reach 15313 151817452146298 171787865010 := by
  have hr := row_15313
  have hl := log_bounds hr.1
    (by change logScale (15313 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15307) (T := 151721087572134) (U := 171776646576)
    (by norm_num) (by norm_num) hr.1 gap_15313
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15307

theorem gap_15319 : PrimeGap 15313 15319 :=
  (primeGap_of_factors (ds := [2, 3, 2, 17, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15319 :
    (15319 : ℕ).Prime ∧ logScale (15319 : ℚ) = 13 ∧
      (96368491636 : ℤ) = ⌊logCenter (15319 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15319 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15319 : Reach 15319 151913820637934 171799079782 := by
  have hr := row_15319
  have hl := log_bounds hr.1
    (by change logScale (15319 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15313) (T := 151817452146298) (U := 171787865010)
    (by norm_num) (by norm_num) hr.1 gap_15319
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15313

theorem gap_15329 : PrimeGap 15319 15329 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15329 :
    (15329 : ℕ).Prime ∧ logScale (15329 : ℚ) = 13 ∧
      (96375017347 : ℤ) = ⌊logCenter (15329 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15329 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15329 : Reach 15329 152010195655281 171810287969 := by
  have hr := row_15329
  have hl := log_bounds hr.1
    (by change logScale (15329 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15319) (T := 151913820637934) (U := 171799079782)
    (by norm_num) (by norm_num) hr.1 gap_15329
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15319

theorem gap_15331 : PrimeGap 15329 15331 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_15331 :
    (15331 : ℕ).Prime ∧ logScale (15331 : ℚ) = 13 ∧
      (96376321979 : ℤ) = ⌊logCenter (15331 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15331 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15331 : Reach 15331 152106571977260 171821495425 := by
  have hr := row_15331
  have hl := log_bounds hr.1
    (by change logScale (15331 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15329) (T := 152010195655281) (U := 171810287969)
    (by norm_num) (by norm_num) hr.1 gap_15331
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15329

theorem gap_15349 : PrimeGap 15331 15349 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 7, 2, 3, 2, 23, 2, 67, 2, 3, 2, 103, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15349 :
    (15349 : ℕ).Prime ∧ logScale (15349 : ℚ) = 13 ∧
      (96388056009 : ℤ) = ⌊logCenter (15349 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15349 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15349 : Reach 15349 152202960033269 171832690467 := by
  have hr := row_15349
  have hl := log_bounds hr.1
    (by change logScale (15349 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15331) (T := 152106571977260) (U := 171821495425)
    (by norm_num) (by norm_num) hr.1 gap_15349
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15331

theorem gap_15359 : PrimeGap 15349 15359 :=
  (primeGap_of_factors (ds := [2, 3, 2, 13, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15359 :
    (15359 : ℕ).Prime ∧ logScale (15359 : ℚ) = 13 ∧
      (96394568970 : ℤ) = ⌊logCenter (15359 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15359 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15359 : Reach 15359 152299354602239 171843878948 := by
  have hr := row_15359
  have hl := log_bounds hr.1
    (by change logScale (15359 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15349) (T := 152202960033269) (U := 171832690467)
    (by norm_num) (by norm_num) hr.1 gap_15359
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15349

theorem gap_15361 : PrimeGap 15359 15361 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_15361 :
    (15361 : ℕ).Prime ∧ logScale (15361 : ℚ) = 13 ∧
      (96395871053 : ℤ) = ⌊logCenter (15361 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15361 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15361 : Reach 15361 152395750473292 171855066701 := by
  have hr := row_15361
  have hl := log_bounds hr.1
    (by change logScale (15361 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15359) (T := 152299354602239) (U := 171843878948)
    (by norm_num) (by norm_num) hr.1 gap_15361
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15359

theorem gap_15373 : PrimeGap 15361 15373 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 11, 2, 3, 2, 19, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15373 :
    (15373 : ℕ).Prime ∧ logScale (15373 : ℚ) = 13 ∧
      (96403679995 : ℤ) = ⌊logCenter (15373 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15373 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15373 : Reach 15373 152492154153287 171866246448 := by
  have hr := row_15373
  have hl := log_bounds hr.1
    (by change logScale (15373 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15361) (T := 152395750473292) (U := 171855066701)
    (by norm_num) (by norm_num) hr.1 gap_15373
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15361

#print axioms reach_15373

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
