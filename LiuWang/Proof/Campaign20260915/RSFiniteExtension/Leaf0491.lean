import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0490
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_11519 : PrimeGap 11503 11519 :=
  (primeGap_of_factors (ds := [2, 3, 2, 37, 2, 17, 2, 3, 2, 29, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11519 :
    (11519 : ℕ).Prime ∧ logScale (11519 : ℚ) = 13 ∧
      (93517531215 : ℤ) = ⌊logCenter (11519 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11519 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11519 : Reach 11519 113811418254479 166711164788 := by
  have hr := row_11519
  have hl := log_bounds hr.1
    (by change logScale (11519 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11503) (T := 113717900723264) (U := 166696692076)
    (by norm_num) (by norm_num) hr.1 gap_11519
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11503

theorem gap_11527 : PrimeGap 11519 11527 :=
  (primeGap_of_factors (ds := [2, 41, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11527 :
    (11527 : ℕ).Prime ∧ logScale (11527 : ℚ) = 13 ∧
      (93524473852 : ℤ) = ⌊logCenter (11527 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11527 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11527 : Reach 11527 113904942728331 166725628710 := by
  have hr := row_11527
  have hl := log_bounds hr.1
    (by change logScale (11527 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11519) (T := 113811418254479) (U := 166711164788)
    (by norm_num) (by norm_num) hr.1 gap_11527
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11519

theorem gap_11549 : PrimeGap 11527 11549 :=
  (primeGap_of_factors (ds := [2, 3, 2, 13, 2, 19, 2, 3, 2, 83, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11549 :
    (11549 : ℕ).Prime ∧ logScale (11549 : ℚ) = 13 ∧
      (93543541287 : ℤ) = ⌊logCenter (11549 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11549 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11549 : Reach 11549 113998486269618 166740066330 := by
  have hr := row_11549
  have hl := log_bounds hr.1
    (by change logScale (11549 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11527) (T := 113904942728331) (U := 166725628710)
    (by norm_num) (by norm_num) hr.1 gap_11549
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11527

theorem gap_11551 : PrimeGap 11549 11551 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_11551 :
    (11551 : ℕ).Prime ∧ logScale (11551 : ℚ) = 13 ∧
      (93545272889 : ℤ) = ⌊logCenter (11551 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11551 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11551 : Reach 11551 114092031542507 166754502700 := by
  have hr := row_11551
  have hl := log_bounds hr.1
    (by change logScale (11551 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11549) (T := 113998486269618) (U := 166740066330)
    (by norm_num) (by norm_num) hr.1 gap_11551
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11549

theorem gap_11579 : PrimeGap 11551 11579 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 31, 2, 3, 2, 43, 2, 23, 2, 3, 2, 71, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11579 :
    (11579 : ℕ).Prime ∧ logScale (11579 : ℚ) = 13 ∧
      (93569483882 : ℤ) = ⌊logCenter (11579 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11579 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11579 : Reach 11579 114185601026389 166768905404 := by
  have hr := row_11579
  have hl := log_bounds hr.1
    (by change logScale (11579 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11551) (T := 114092031542507) (U := 166754502700)
    (by norm_num) (by norm_num) hr.1 gap_11579
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11551

theorem gap_11587 : PrimeGap 11579 11587 :=
  (primeGap_of_factors (ds := [2, 37, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11587 :
    (11587 : ℕ).Prime ∧ logScale (11587 : ℚ) = 13 ∧
      (93576390556 : ℤ) = ⌊logCenter (11587 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11587 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11587 : Reach 11587 114279177416945 166783299406 := by
  have hr := row_11587
  have hl := log_bounds hr.1
    (by change logScale (11587 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11579) (T := 114185601026389) (U := 166768905404)
    (by norm_num) (by norm_num) hr.1 gap_11587
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11579

theorem gap_11593 : PrimeGap 11587 11593 :=
  (primeGap_of_factors (ds := [2, 3, 2, 67, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11593 :
    (11593 : ℕ).Prime ∧ logScale (11593 : ℚ) = 13 ∧
      (93581567432 : ℤ) = ⌊logCenter (11593 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11593 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11593 : Reach 11593 114372758984377 166797687200 := by
  have hr := row_11593
  have hl := log_bounds hr.1
    (by change logScale (11593 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11587) (T := 114279177416945) (U := 166783299406)
    (by norm_num) (by norm_num) hr.1 gap_11593
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11587

theorem gap_11597 : PrimeGap 11593 11597 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11597 :
    (11597 : ℕ).Prime ∧ logScale (11597 : ℚ) = 13 ∧
      (93585017195 : ℤ) = ⌊logCenter (11597 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11597 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11597 : Reach 11597 114466344001572 166812071271 := by
  have hr := row_11597
  have hl := log_bounds hr.1
    (by change logScale (11597 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11593) (T := 114372758984377) (U := 166797687200)
    (by norm_num) (by norm_num) hr.1 gap_11597
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11593

#print axioms reach_11597

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
