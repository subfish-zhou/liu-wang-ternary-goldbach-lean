import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block034
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_8329 : PrimeGap 8317 8329 :=
  (primeGap_of_factors (ds := [2, 3, 2, 53, 2, 7, 2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8329 :
    (8329 : ℕ).Prime ∧ logScale (8329 : ℚ) = 13 ∧
      (90274986765 : ℤ) = ⌊logCenter (8329 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8329 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8329 : Reach 8329 82174771767558 160973380381 := by
  have hr := row_8329
  have hl := log_bounds hr.1
    (by change logScale (8329 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8317) (T := 82084496780793) (U := 160954053525)
    (by norm_num) (by norm_num) hr.1 gap_8329
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8317

theorem gap_8353 : PrimeGap 8329 8353 :=
  (primeGap_of_factors (ds := [2, 3, 2, 13, 2, 5, 2, 3, 2, 31, 2, 19, 2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8353 :
    (8353 : ℕ).Prime ∧ logScale (8353 : ℚ) = 13 ∧
      (90303760313 : ℤ) = ⌊logCenter (8353 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8353 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8353 : Reach 8353 82265075527871 160992654014 := by
  have hr := row_8353
  have hl := log_bounds hr.1
    (by change logScale (8353 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8329) (T := 82174771767558) (U := 160973380381)
    (by norm_num) (by norm_num) hr.1 gap_8353
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8329

theorem gap_8363 : PrimeGap 8353 8363 :=
  (primeGap_of_factors (ds := [2, 3, 2, 61, 2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8363 :
    (8363 : ℕ).Prime ∧ logScale (8363 : ℚ) = 13 ∧
      (90315724900 : ℤ) = ⌊logCenter (8363 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8363 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8363 : Reach 8363 82355391252771 161011906903 := by
  have hr := row_8363
  have hl := log_bounds hr.1
    (by change logScale (8363 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8353) (T := 82265075527871) (U := 160992654014)
    (by norm_num) (by norm_num) hr.1 gap_8363
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8353

theorem gap_8369 : PrimeGap 8363 8369 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8369 :
    (8369 : ℕ).Prime ∧ logScale (8369 : ℚ) = 13 ∧
      (90322896786 : ℤ) = ⌊logCenter (8369 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8369 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8369 : Reach 8369 82445714149557 161031148288 := by
  have hr := row_8369
  have hl := log_bounds hr.1
    (by change logScale (8369 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8363) (T := 82355391252771) (U := 161011906903)
    (by norm_num) (by norm_num) hr.1 gap_8369
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8363

theorem gap_8377 : PrimeGap 8369 8377 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8377 :
    (8377 : ℕ).Prime ∧ logScale (8377 : ℚ) = 13 ∧
      (90332451307 : ℤ) = ⌊logCenter (8377 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8377 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8377 : Reach 8377 82536046600864 161050373593 := by
  have hr := row_8377
  have hl := log_bounds hr.1
    (by change logScale (8377 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8369) (T := 82445714149557) (U := 161031148288)
    (by norm_num) (by norm_num) hr.1 gap_8377
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8369

theorem gap_8387 : PrimeGap 8377 8387 :=
  (primeGap_of_factors (ds := [2, 3, 2, 17, 2, 83, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8387 :
    (8387 : ℕ).Prime ∧ logScale (8387 : ℚ) = 13 ∧
      (90344381636 : ℤ) = ⌊logCenter (8387 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8387 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8387 : Reach 8387 82626390982500 161069578265 := by
  have hr := row_8387
  have hl := log_bounds hr.1
    (by change logScale (8387 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8377) (T := 82536046600864) (U := 161050373593)
    (by norm_num) (by norm_num) hr.1 gap_8387
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8377

theorem gap_8389 : PrimeGap 8387 8389 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_8389 :
    (8389 : ℕ).Prime ∧ logScale (8389 : ℚ) = 13 ∧
      (90346765994 : ℤ) = ⌊logCenter (8389 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8389 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8389 : Reach 8389 82716737748494 161088780647 := by
  have hr := row_8389
  have hl := log_bounds hr.1
    (by change logScale (8389 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8387) (T := 82626390982500) (U := 161069578265)
    (by norm_num) (by norm_num) hr.1 gap_8389
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8387

theorem gap_8419 : PrimeGap 8389 8419 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 5, 2, 3, 2, 37, 2, 31, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 47, 2, 3, 2, 19, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8419 :
    (8419 : ℕ).Prime ∧ logScale (8419 : ℚ) = 13 ∧
      (90382463319 : ℤ) = ⌊logCenter (8419 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8419 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8419 : Reach 8419 82807120211813 161107916877 := by
  have hr := row_8419
  have hl := log_bounds hr.1
    (by change logScale (8419 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8389) (T := 82716737748494) (U := 161088780647)
    (by norm_num) (by norm_num) hr.1 gap_8419
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8389

#print axioms reach_8419

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
