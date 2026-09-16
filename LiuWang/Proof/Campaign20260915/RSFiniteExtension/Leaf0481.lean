import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0480
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_11287 : PrimeGap 11279 11287 :=
  (primeGap_of_factors (ds := [2, 29, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11287 :
    (11287 : ℕ).Prime ∧ logScale (11287 : ℚ) = 13 ∧
      (93314068965 : ℤ) = ⌊logCenter (11287 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11287 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11287 : Reach 11287 111569225782424 166360926574 := by
  have hr := row_11287
  have hl := log_bounds hr.1
    (by change logScale (11287 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11279) (T := 111475911713459) (U := 166346187411)
    (by norm_num) (by norm_num) hr.1 gap_11287
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11279

theorem gap_11299 : PrimeGap 11287 11299 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 23, 2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11299 :
    (11299 : ℕ).Prime ∧ logScale (11299 : ℚ) = 13 ∧
      (93324695018 : ℤ) = ⌊logCenter (11299 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11299 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11299 : Reach 11299 111662550477442 166375651387 := by
  have hr := row_11299
  have hl := log_bounds hr.1
    (by change logScale (11299 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11287) (T := 111569225782424) (U := 166360926574)
    (by norm_num) (by norm_num) hr.1 gap_11299
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11287

theorem gap_11311 : PrimeGap 11299 11311 :=
  (primeGap_of_factors (ds := [2, 3, 2, 89, 2, 5, 2, 3, 2, 43, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11311 :
    (11311 : ℕ).Prime ∧ logScale (11311 : ℚ) = 13 ∧
      (93335309791 : ℤ) = ⌊logCenter (11311 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11311 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11311 : Reach 11311 111755885787233 166390361878 := by
  have hr := row_11311
  have hl := log_bounds hr.1
    (by change logScale (11311 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11299) (T := 111662550477442) (U := 166375651387)
    (by norm_num) (by norm_num) hr.1 gap_11311
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11299

theorem gap_11317 : PrimeGap 11311 11317 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11317 :
    (11317 : ℕ).Prime ∧ logScale (11317 : ℚ) = 13 ∧
      (93340612955 : ℤ) = ⌊logCenter (11317 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11317 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11317 : Reach 11317 111849226400188 166405065869 := by
  have hr := row_11317
  have hl := log_bounds hr.1
    (by change logScale (11317 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11311) (T := 111755885787233) (U := 166390361878)
    (by norm_num) (by norm_num) hr.1 gap_11317
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11311

theorem gap_11321 : PrimeGap 11317 11321 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11321 :
    (11321 : ℕ).Prime ∧ logScale (11321 : ℚ) = 13 ∧
      (93344146836 : ℤ) = ⌊logCenter (11321 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11321 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11321 : Reach 11321 111942570547024 166419765964 := by
  have hr := row_11321
  have hl := log_bounds hr.1
    (by change logScale (11321 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11317) (T := 111849226400188) (U := 166405065869)
    (by norm_num) (by norm_num) hr.1 gap_11321
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11317

theorem gap_11329 : PrimeGap 11321 11329 :=
  (primeGap_of_factors (ds := [2, 13, 2, 3, 2, 47, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11329 :
    (11329 : ℕ).Prime ∧ logScale (11329 : ℚ) = 13 ∧
      (93351210854 : ℤ) = ⌊logCenter (11329 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11329 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11329 : Reach 11329 112035921757878 166434456975 := by
  have hr := row_11329
  have hl := log_bounds hr.1
    (by change logScale (11329 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11321) (T := 111942570547024) (U := 166419765964)
    (by norm_num) (by norm_num) hr.1 gap_11329
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11321

theorem gap_11351 : PrimeGap 11329 11351 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11351 :
    (11351 : ℕ).Prime ∧ logScale (11351 : ℚ) = 13 ∧
      (93370611213 : ℤ) = ⌊logCenter (11351 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11351 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11351 : Reach 11351 112129292369091 166449120804 := by
  have hr := row_11351
  have hl := log_bounds hr.1
    (by change logScale (11351 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11329) (T := 112035921757878) (U := 166434456975)
    (by norm_num) (by norm_num) hr.1 gap_11351
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11329

theorem gap_11353 : PrimeGap 11351 11353 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_11353 :
    (11353 : ℕ).Prime ∧ logScale (11353 : ℚ) = 13 ∧
      (93372373017 : ℤ) = ⌊logCenter (11353 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11353 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11353 : Reach 11353 112222664742108 166463783342 := by
  have hr := row_11353
  have hl := log_bounds hr.1
    (by change logScale (11353 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11351) (T := 112129292369091) (U := 166449120804)
    (by norm_num) (by norm_num) hr.1 gap_11353
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11351

#print axioms reach_11353

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
