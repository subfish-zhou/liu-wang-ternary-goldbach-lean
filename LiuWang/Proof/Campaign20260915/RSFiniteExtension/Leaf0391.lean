import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0390
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_9281 : PrimeGap 9277 9281 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9281 :
    (9281 : ℕ).Prime ∧ logScale (9281 : ℚ) = 13 ∧
      (91357245752 : ℤ) = ⌊logCenter (9281 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9281 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9281 : Reach 9281 91622164035058 162885125665 := by
  have hr := row_9281
  have hl := log_bounds hr.1
    (by change logScale (9281 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9277) (T := 91530806789306) (U := 162867575279)
    (by norm_num) (by norm_num) hr.1 gap_9281
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9277

theorem gap_9283 : PrimeGap 9281 9283 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_9283 :
    (9283 : ℕ).Prime ∧ logScale (9283 : ℚ) = 13 ∧
      (91359400460 : ℤ) = ⌊logCenter (9283 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9283 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9283 : Reach 9283 91713523435518 162902674160 := by
  have hr := row_9283
  have hl := log_bounds hr.1
    (by change logScale (9283 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9281) (T := 91622164035058) (U := 162885125665)
    (by norm_num) (by norm_num) hr.1 gap_9283
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9281

theorem gap_9293 : PrimeGap 9283 9293 :=
  (primeGap_of_factors (ds := [2, 3, 2, 37, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9293 :
    (9293 : ℕ).Prime ∧ logScale (9293 : ℚ) = 13 ∧
      (91370167041 : ℤ) = ⌊logCenter (9293 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9293 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9293 : Reach 9293 91804893602559 162920205658 := by
  have hr := row_9293
  have hl := log_bounds hr.1
    (by change logScale (9293 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9283) (T := 91713523435518) (U := 162902674160)
    (by norm_num) (by norm_num) hr.1 gap_9293
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9283

theorem gap_9311 : PrimeGap 9293 9311 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 17, 2, 71, 2, 3, 2, 5, 2, 41, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9311 :
    (9311 : ℕ).Prime ∧ logScale (9311 : ℚ) = 13 ∧
      (91389517725 : ℤ) = ⌊logCenter (9311 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9311 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9311 : Reach 9311 91896283120284 162937705144 := by
  have hr := row_9311
  have hl := log_bounds hr.1
    (by change logScale (9311 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9293) (T := 91804893602559) (U := 162920205658)
    (by norm_num) (by norm_num) hr.1 gap_9311
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9293

theorem gap_9319 : PrimeGap 9311 9319 :=
  (primeGap_of_factors (ds := [2, 67, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9319 :
    (9319 : ℕ).Prime ∧ logScale (9319 : ℚ) = 13 ∧
      (91398106024 : ℤ) = ⌊logCenter (9319 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9319 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9319 : Reach 9319 91987681226308 162955191483 := by
  have hr := row_9319
  have hl := log_bounds hr.1
    (by change logScale (9319 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9311) (T := 91896283120284) (U := 162937705144)
    (by norm_num) (by norm_num) hr.1 gap_9319
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9311

theorem gap_9323 : PrimeGap 9319 9323 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9323 :
    (9323 : ℕ).Prime ∧ logScale (9323 : ℚ) = 13 ∧
      (91402397409 : ℤ) = ⌊logCenter (9323 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9323 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9323 : Reach 9323 92079083623717 162972672195 := by
  have hr := row_9323
  have hl := log_bounds hr.1
    (by change logScale (9323 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9319) (T := 91987681226308) (U := 162955191483)
    (by norm_num) (by norm_num) hr.1 gap_9323
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9319

theorem gap_9337 : PrimeGap 9323 9337 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 19, 2, 7, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9337 :
    (9337 : ℕ).Prime ∧ logScale (9337 : ℚ) = 13 ∧
      (91417402771 : ℤ) = ⌊logCenter (9337 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9337 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9337 : Reach 9337 92170501026488 162990128566 := by
  have hr := row_9337
  have hl := log_bounds hr.1
    (by change logScale (9337 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9323) (T := 92079083623717) (U := 162972672195)
    (by norm_num) (by norm_num) hr.1 gap_9337
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9323

theorem gap_9341 : PrimeGap 9337 9341 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9341 :
    (9341 : ℕ).Prime ∧ logScale (9341 : ℚ) = 13 ∧
      (91421685884 : ℤ) = ⌊logCenter (9341 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9341 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9341 : Reach 9341 92261922712372 163007579330 := by
  have hr := row_9341
  have hl := log_bounds hr.1
    (by change logScale (9341 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9337) (T := 92170501026488) (U := 162990128566)
    (by norm_num) (by norm_num) hr.1 gap_9341
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9337

#print axioms reach_9341

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
