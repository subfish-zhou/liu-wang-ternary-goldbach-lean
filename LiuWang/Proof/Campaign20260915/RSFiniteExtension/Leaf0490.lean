import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block048
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_11447 : PrimeGap 11443 11447 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11447 :
    (11447 : ℕ).Prime ∧ logScale (11447 : ℚ) = 13 ∧
      (93454829625 : ℤ) = ⌊logCenter (11447 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11447 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11447 : Reach 11447 113063479740816 166595125997 := by
  have hr := row_11447
  have hl := log_bounds hr.1
    (by change logScale (11447 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11443) (T := 112970024911191) (U := 166580572391)
    (by norm_num) (by norm_num) hr.1 gap_11447
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11443

theorem gap_11467 : PrimeGap 11447 11467 :=
  (primeGap_of_factors (ds := [2, 107, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 73, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11467 :
    (11467 : ℕ).Prime ∧ logScale (11467 : ℚ) = 13 ∧
      (93472286206 : ℤ) = ⌊logCenter (11467 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11467 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11467 : Reach 11467 113156952027022 166609655487 := by
  have hr := row_11467
  have hl := log_bounds hr.1
    (by change logScale (11467 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11447) (T := 113063479740816) (U := 166595125997)
    (by norm_num) (by norm_num) hr.1 gap_11467
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11447

theorem gap_11471 : PrimeGap 11467 11471 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11471 :
    (11471 : ℕ).Prime ∧ logScale (11471 : ℚ) = 13 ∧
      (93475773869 : ℤ) = ⌊logCenter (11471 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11471 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11471 : Reach 11471 113250427800891 166624181177 := by
  have hr := row_11471
  have hl := log_bounds hr.1
    (by change logScale (11471 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11467) (T := 113156952027022) (U := 166609655487)
    (by norm_num) (by norm_num) hr.1 gap_11471
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11467

theorem gap_11483 : PrimeGap 11471 11483 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 23, 2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11483 :
    (11483 : ℕ).Prime ∧ logScale (11483 : ℚ) = 13 ∧
      (93486229563 : ℤ) = ⌊logCenter (11483 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11483 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11483 : Reach 11483 113343914030454 166638692951 := by
  have hr := row_11483
  have hl := log_bounds hr.1
    (by change logScale (11483 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11471) (T := 113250427800891) (U := 166624181177)
    (by norm_num) (by norm_num) hr.1 gap_11483
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11471

theorem gap_11489 : PrimeGap 11483 11489 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11489 :
    (11489 : ℕ).Prime ∧ logScale (11489 : ℚ) = 13 ∧
      (93491453314 : ℤ) = ⌊logCenter (11489 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11489 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11489 : Reach 11489 113437405483768 166653198409 := by
  have hr := row_11489
  have hl := log_bounds hr.1
    (by change logScale (11489 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11483) (T := 113343914030454) (U := 166638692951)
    (by norm_num) (by norm_num) hr.1 gap_11489
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11483

theorem gap_11491 : PrimeGap 11489 11491 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_11491 :
    (11491 : ℕ).Prime ∧ logScale (11491 : ℚ) = 13 ∧
      (93493193958 : ℤ) = ⌊logCenter (11491 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11491 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11491 : Reach 11491 113530898677726 166667702604 := by
  have hr := row_11491
  have hl := log_bounds hr.1
    (by change logScale (11491 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11489) (T := 113437405483768) (U := 166653198409)
    (by norm_num) (by norm_num) hr.1 gap_11491
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11489

theorem gap_11497 : PrimeGap 11491 11497 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11497 :
    (11497 : ℕ).Prime ∧ logScale (11497 : ℚ) = 13 ∧
      (93498414073 : ℤ) = ⌊logCenter (11497 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11497 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11497 : Reach 11497 113624397091799 166682200491 := by
  have hr := row_11497
  have hl := log_bounds hr.1
    (by change logScale (11497 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11491) (T := 113530898677726) (U := 166667702604)
    (by norm_num) (by norm_num) hr.1 gap_11497
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11491

theorem gap_11503 : PrimeGap 11497 11503 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11503 :
    (11503 : ℕ).Prime ∧ logScale (11503 : ℚ) = 13 ∧
      (93503631465 : ℤ) = ⌊logCenter (11503 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11503 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11503 : Reach 11503 113717900723264 166696692076 := by
  have hr := row_11503
  have hl := log_bounds hr.1
    (by change logScale (11503 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11497) (T := 113624397091799) (U := 166682200491)
    (by norm_num) (by norm_num) hr.1 gap_11503
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11497

#print axioms reach_11503

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
