import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0341
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_8269 : PrimeGap 8263 8269 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8269 :
    (8269 : ℕ).Prime ∧ logScale (8269 : ℚ) = 13 ∧
      (90202688583 : ℤ) = ⌊logCenter (8269 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8269 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8269 : Reach 8269 81452853479987 160818285409 := by
  have hr := row_8269
  have hl := log_bounds hr.1
    (by change logScale (8269 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8263) (T := 81362650791404) (U := 160798837073)
    (by norm_num) (by norm_num) hr.1 gap_8269
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8263

theorem gap_8273 : PrimeGap 8269 8273 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8273 :
    (8273 : ℕ).Prime ∧ logScale (8273 : ℚ) = 13 ∧
      (90207524758 : ℤ) = ⌊logCenter (8273 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8273 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8273 : Reach 8273 81543061004745 160837726692 := by
  have hr := row_8273
  have hl := log_bounds hr.1
    (by change logScale (8273 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8269) (T := 81452853479987) (U := 160818285409)
    (by norm_num) (by norm_num) hr.1 gap_8273
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8269

theorem gap_8287 : PrimeGap 8273 8287 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8287 :
    (8287 : ℕ).Prime ∧ logScale (8287 : ℚ) = 13 ∧
      (90224432974 : ℤ) = ⌊logCenter (8287 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8287 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8287 : Reach 8287 81633285437719 160857137473 := by
  have hr := row_8287
  have hl := log_bounds hr.1
    (by change logScale (8287 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8273) (T := 81543061004745) (U := 160837726692)
    (by norm_num) (by norm_num) hr.1 gap_8287
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8273

theorem gap_8291 : PrimeGap 8287 8291 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8291 :
    (8291 : ℕ).Prime ∧ logScale (8291 : ℚ) = 13 ∧
      (90229258647 : ℤ) = ⌊logCenter (8291 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8291 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8291 : Reach 8291 81723514696366 160876541230 := by
  have hr := row_8291
  have hl := log_bounds hr.1
    (by change logScale (8291 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8287) (T := 81633285437719) (U := 160857137473)
    (by norm_num) (by norm_num) hr.1 gap_8291
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8287

theorem gap_8293 : PrimeGap 8291 8293 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_8293 :
    (8293 : ℕ).Prime ∧ logScale (8293 : ℚ) = 13 ∧
      (90231670610 : ℤ) = ⌊logCenter (8293 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8293 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8293 : Reach 8293 81813746366976 160895942646 := by
  have hr := row_8293
  have hl := log_bounds hr.1
    (by change logScale (8293 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8291) (T := 81723514696366) (U := 160876541230)
    (by norm_num) (by norm_num) hr.1 gap_8293
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8291

theorem gap_8297 : PrimeGap 8293 8297 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8297 :
    (8297 : ℕ).Prime ∧ logScale (8297 : ℚ) = 13 ∧
      (90236492792 : ℤ) = ⌊logCenter (8297 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8297 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8297 : Reach 8297 81903982859768 160915337047 := by
  have hr := row_8297
  have hl := log_bounds hr.1
    (by change logScale (8297 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8293) (T := 81813746366976) (U := 160895942646)
    (by norm_num) (by norm_num) hr.1 gap_8297
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8293

theorem gap_8311 : PrimeGap 8297 8311 :=
  (primeGap_of_factors (ds := [2, 43, 2, 3, 2, 19, 2, 5, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8311 :
    (8311 : ℕ).Prime ∧ logScale (8311 : ℚ) = 13 ∧
      (90253352141 : ℤ) = ⌊logCenter (8311 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8311 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8311 : Reach 8311 81994236211909 160934701107 := by
  have hr := row_8311
  have hl := log_bounds hr.1
    (by change logScale (8311 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8297) (T := 81903982859768) (U := 160915337047)
    (by norm_num) (by norm_num) hr.1 gap_8311
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8297

theorem gap_8317 : PrimeGap 8311 8317 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8317 :
    (8317 : ℕ).Prime ∧ logScale (8317 : ℚ) = 13 ∧
      (90260568884 : ℤ) = ⌊logCenter (8317 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8317 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8317 : Reach 8317 82084496780793 160954053525 := by
  have hr := row_8317
  have hl := log_bounds hr.1
    (by change logScale (8317 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8311) (T := 81994236211909) (U := 160934701107)
    (by norm_num) (by norm_num) hr.1 gap_8317
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8311

#print axioms reach_8317

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
