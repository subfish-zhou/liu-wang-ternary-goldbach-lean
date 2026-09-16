import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0391
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_9343 : PrimeGap 9341 9343 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_9343 :
    (9343 : ℕ).Prime ∧ logScale (9343 : ℚ) = 13 ∧
      (91423826754 : ℤ) = ⌊logCenter (9343 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9343 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9343 : Reach 9343 92353346539126 163025028226 := by
  have hr := row_9343
  have hl := log_bounds hr.1
    (by change logScale (9343 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9341) (T := 92261922712372) (U := 163007579330)
    (by norm_num) (by norm_num) hr.1 gap_9343
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9341

theorem gap_9349 : PrimeGap 9343 9349 :=
  (primeGap_of_factors (ds := [2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9349 :
    (9349 : ℕ).Prime ∧ logScale (9349 : ℚ) = 13 ∧
      (91430246613 : ℤ) = ⌊logCenter (9349 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9349 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9349 : Reach 9349 92444776785739 163042467789 := by
  have hr := row_9349
  have hl := log_bounds hr.1
    (by change logScale (9349 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9343) (T := 92353346539126) (U := 163025028226)
    (by norm_num) (by norm_num) hr.1 gap_9349
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9343

theorem gap_9371 : PrimeGap 9349 9371 :=
  (primeGap_of_factors (ds := [2, 3, 2, 47, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 17, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9371 :
    (9371 : ℕ).Prime ∧ logScale (9371 : ℚ) = 13 ∧
      (91453750897 : ℤ) = ⌊logCenter (9371 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9371 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9371 : Reach 9371 92536230536636 163059868266 := by
  have hr := row_9371
  have hl := log_bounds hr.1
    (by change logScale (9371 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9349) (T := 92444776785739) (U := 163042467789)
    (by norm_num) (by norm_num) hr.1 gap_9371
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9349

theorem gap_9377 : PrimeGap 9371 9377 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9377 :
    (9377 : ℕ).Prime ∧ logScale (9377 : ℚ) = 13 ∧
      (91460151580 : ℤ) = ⌊logCenter (9377 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9377 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9377 : Reach 9377 92627690688216 163077259464 := by
  have hr := row_9377
  have hl := log_bounds hr.1
    (by change logScale (9377 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9371) (T := 92536230536636) (U := 163059868266)
    (by norm_num) (by norm_num) hr.1 gap_9377
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9371

theorem gap_9391 : PrimeGap 9377 9391 :=
  (primeGap_of_factors (ds := [2, 83, 2, 3, 2, 11, 2, 5, 2, 3, 2, 41, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9391 :
    (9391 : ℕ).Prime ∧ logScale (9391 : ℚ) = 13 ∧
      (91475070594 : ℤ) = ⌊logCenter (9391 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9391 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9391 : Reach 9391 92719165758810 163094626585 := by
  have hr := row_9391
  have hl := log_bounds hr.1
    (by change logScale (9391 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9377) (T := 92627690688216) (U := 163077259464)
    (by norm_num) (by norm_num) hr.1 gap_9391
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9377

theorem gap_9397 : PrimeGap 9391 9397 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9397 :
    (9397 : ℕ).Prime ∧ logScale (9397 : ℚ) = 13 ∧
      (91481457650 : ℤ) = ⌊logCenter (9397 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9397 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9397 : Reach 9397 92810647216460 163111984464 := by
  have hr := row_9397
  have hl := log_bounds hr.1
    (by change logScale (9397 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9391) (T := 92719165758810) (U := 163094626585)
    (by norm_num) (by norm_num) hr.1 gap_9397
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9391

theorem gap_9403 : PrimeGap 9397 9403 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9403 :
    (9403 : ℕ).Prime ∧ logScale (9403 : ℚ) = 13 ∧
      (91487840628 : ℤ) = ⌊logCenter (9403 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9403 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9403 : Reach 9403 92902135057088 163129333112 := by
  have hr := row_9403
  have hl := log_bounds hr.1
    (by change logScale (9403 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9397) (T := 92810647216460) (U := 163111984464)
    (by norm_num) (by norm_num) hr.1 gap_9403
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9397

theorem gap_9413 : PrimeGap 9403 9413 :=
  (primeGap_of_factors (ds := [2, 3, 2, 23, 2, 97, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9413 :
    (9413 : ℕ).Prime ∧ logScale (9413 : ℚ) = 13 ∧
      (91498469881 : ℤ) = ⌊logCenter (9413 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9413 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9413 : Reach 9413 92993633526969 163146665171 := by
  have hr := row_9413
  have hl := log_bounds hr.1
    (by change logScale (9413 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9403) (T := 92902135057088) (U := 163129333112)
    (by norm_num) (by norm_num) hr.1 gap_9413
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9403

#print axioms reach_9413

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
