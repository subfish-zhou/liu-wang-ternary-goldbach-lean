import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0570
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_13313 : PrimeGap 13309 13313 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13313 :
    (13313 : ℕ).Prime ∧ logScale (13313 : ℚ) = 13 ∧
      (94964962770 : ℤ) = ⌊logCenter (13313 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13313 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13313 : Reach 13313 131911912006955 169309898320 := by
  have hr := row_13313
  have hl := log_bounds hr.1
    (by change logScale (13313 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13309) (T := 131816947044185) (U := 169297180683)
    (by norm_num) (by norm_num) hr.1 gap_13313
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13309

theorem gap_13327 : PrimeGap 13313 13327 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 19, 2, 7, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13327 :
    (13327 : ℕ).Prime ∧ logScale (13327 : ℚ) = 13 ∧
      (94975473282 : ℤ) = ⌊logCenter (13327 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13327 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13327 : Reach 13327 132006887480237 169322603551 := by
  have hr := row_13327
  have hl := log_bounds hr.1
    (by change logScale (13327 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13313) (T := 131911912006955) (U := 169309898320)
    (by norm_num) (by norm_num) hr.1 gap_13327
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13313

theorem gap_13331 : PrimeGap 13327 13331 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13331 :
    (13331 : ℕ).Prime ∧ logScale (13331 : ℚ) = 13 ∧
      (94978474257 : ℤ) = ⌊logCenter (13331 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13331 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13331 : Reach 13331 132101865954494 169335305922 := by
  have hr := row_13331
  have hl := log_bounds hr.1
    (by change logScale (13331 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13327) (T := 132006887480237) (U := 169322603551)
    (by norm_num) (by norm_num) hr.1 gap_13331
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13327

theorem gap_13337 : PrimeGap 13331 13337 :=
  (primeGap_of_factors (ds := [2, 67, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13337 :
    (13337 : ℕ).Prime ∧ logScale (13337 : ℚ) = 13 ∧
      (94982974032 : ℤ) = ⌊logCenter (13337 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13337 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13337 : Reach 13337 132196848928526 169348003531 := by
  have hr := row_13337
  have hl := log_bounds hr.1
    (by change logScale (13337 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13331) (T := 132101865954494) (U := 169335305922)
    (by norm_num) (by norm_num) hr.1 gap_13337
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13331

theorem gap_13339 : PrimeGap 13337 13339 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_13339 :
    (13339 : ℕ).Prime ∧ logScale (13339 : ℚ) = 13 ∧
      (94984473507 : ℤ) = ⌊logCenter (13339 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13339 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13339 : Reach 13339 132291833402033 169360700188 := by
  have hr := row_13339
  have hl := log_bounds hr.1
    (by change logScale (13339 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13337) (T := 132196848928526) (U := 169348003531)
    (by norm_num) (by norm_num) hr.1 gap_13339
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13337

theorem gap_13367 : PrimeGap 13339 13367 :=
  (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 19, 2, 3, 2, 31, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13367 :
    (13367 : ℕ).Prime ∧ logScale (13367 : ℚ) = 13 ∧
      (95005442585 : ℤ) = ⌊logCenter (13367 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13367 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13367 : Reach 13367 132386838844618 169373371197 := by
  have hr := row_13367
  have hl := log_bounds hr.1
    (by change logScale (13367 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13339) (T := 132291833402033) (U := 169360700188)
    (by norm_num) (by norm_num) hr.1 gap_13367
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13339

theorem gap_13381 : PrimeGap 13367 13381 :=
  (primeGap_of_factors (ds := [2, 29, 2, 3, 2, 43, 2, 5, 2, 3, 2, 17, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13381 :
    (13381 : ℕ).Prime ∧ logScale (13381 : ℚ) = 13 ∧
      (95015910659 : ℤ) = ⌊logCenter (13381 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13381 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13381 : Reach 13381 132481854755277 169386029895 := by
  have hr := row_13381
  have hl := log_bounds hr.1
    (by change logScale (13381 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13367) (T := 132386838844618) (U := 169373371197)
    (by norm_num) (by norm_num) hr.1 gap_13381
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13367

theorem gap_13397 : PrimeGap 13381 13397 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 59, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13397 :
    (13397 : ℕ).Prime ∧ logScale (13397 : ℚ) = 13 ∧
      (95027860768 : ℤ) = ⌊logCenter (13397 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13397 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13397 : Reach 13397 132576882616045 169398674418 := by
  have hr := row_13397
  have hl := log_bounds hr.1
    (by change logScale (13397 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13381) (T := 132481854755277) (U := 169386029895)
    (by norm_num) (by norm_num) hr.1 gap_13397
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13381

#print axioms reach_13397

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
