import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0521
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_12281 : PrimeGap 12277 12281 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12281 :
    (12281 : ℕ).Prime ∧ logScale (12281 : ℚ) = 13 ∧
      (94158086282 : ℤ) = ⌊logCenter (12281 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12281 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12281 : Reach 12281 121320436866907 167833685168 := by
  have hr := row_12281
  have hl := log_bounds hr.1
    (by change logScale (12281 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12277) (T := 121226278780625) (U := 167820019042)
    (by norm_num) (by norm_num) hr.1 gap_12281
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12277

theorem gap_12289 : PrimeGap 12281 12289 :=
  (primeGap_of_factors (ds := [2, 71, 2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12289 :
    (12289 : ℕ).Prime ∧ logScale (12289 : ℚ) = 13 ∧
      (94164598289 : ℤ) = ⌊logCenter (12289 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12289 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12289 : Reach 12289 121414601465196 167847343509 := by
  have hr := row_12289
  have hl := log_bounds hr.1
    (by change logScale (12289 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12281) (T := 121320436866907) (U := 167833685168)
    (by norm_num) (by norm_num) hr.1 gap_12289
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12281

theorem gap_12301 : PrimeGap 12289 12301 :=
  (primeGap_of_factors (ds := [2, 3, 2, 19, 2, 5, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12301 :
    (12301 : ℕ).Prime ∧ logScale (12301 : ℚ) = 13 ∧
      (94174358354 : ℤ) = ⌊logCenter (12301 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12301 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12301 : Reach 12301 121508775823550 167860989635 := by
  have hr := row_12301
  have hl := log_bounds hr.1
    (by change logScale (12301 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12289) (T := 121414601465196) (U := 167847343509)
    (by norm_num) (by norm_num) hr.1 gap_12301
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12289

theorem gap_12323 : PrimeGap 12301 12323 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 31, 2, 3, 2, 13, 2, 7, 2, 3, 2, 109, 2, 97, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12323 :
    (12323 : ℕ).Prime ∧ logScale (12323 : ℚ) = 13 ∧
      (94192227105 : ℤ) = ⌊logCenter (12323 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12323 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12323 : Reach 12323 121602968050655 167874612504 := by
  have hr := row_12323
  have hl := log_bounds hr.1
    (by change logScale (12323 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12301) (T := 121508775823550) (U := 167860989635)
    (by norm_num) (by norm_num) hr.1 gap_12323
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12301

theorem gap_12329 : PrimeGap 12323 12329 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12329 :
    (12329 : ℕ).Prime ∧ logScale (12329 : ℚ) = 13 ∧
      (94197094864 : ℤ) = ⌊logCenter (12329 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12329 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12329 : Reach 12329 121697165145519 167888229848 := by
  have hr := row_12329
  have hl := log_bounds hr.1
    (by change logScale (12329 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12323) (T := 121602968050655) (U := 167874612504)
    (by norm_num) (by norm_num) hr.1 gap_12329
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12323

theorem gap_12343 : PrimeGap 12329 12343 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12343 :
    (12343 : ℕ).Prime ∧ logScale (12343 : ℚ) = 13 ∧
      (94208443763 : ℤ) = ⌊logCenter (12343 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12343 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12343 : Reach 12343 121791373589282 167901832849 := by
  have hr := row_12343
  have hl := log_bounds hr.1
    (by change logScale (12343 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12329) (T := 121697165145519) (U := 167888229848)
    (by norm_num) (by norm_num) hr.1 gap_12343
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12329

theorem gap_12347 : PrimeGap 12343 12347 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12347 :
    (12347 : ℕ).Prime ∧ logScale (12347 : ℚ) = 13 ∧
      (94211683941 : ℤ) = ⌊logCenter (12347 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12347 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12347 : Reach 12347 121885585273223 167915432544 := by
  have hr := row_12347
  have hl := log_bounds hr.1
    (by change logScale (12347 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12343) (T := 121791373589282) (U := 167901832849)
    (by norm_num) (by norm_num) hr.1 gap_12347
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12343

theorem gap_12373 : PrimeGap 12347 12373 :=
  (primeGap_of_factors (ds := [2, 53, 2, 3, 2, 11, 2, 5, 2, 3, 2, 17, 2, 47, 2, 3, 2, 5, 2, 83, 2, 3, 2, 89, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12373 :
    (12373 : ℕ).Prime ∧ logScale (12373 : ℚ) = 13 ∧
      (94232719548 : ℤ) = ⌊logCenter (12373 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12373 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12373 : Reach 12373 121979817992771 167929004759 := by
  have hr := row_12373
  have hl := log_bounds hr.1
    (by change logScale (12373 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12347) (T := 121885585273223) (U := 167915432544)
    (by norm_num) (by norm_num) hr.1 gap_12373
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12347

#print axioms reach_12373

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
