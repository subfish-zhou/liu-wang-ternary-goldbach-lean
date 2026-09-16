import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0510
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_11981 : PrimeGap 11971 11981 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11981 :
    (11981 : ℕ).Prime ∧ logScale (11981 : ℚ) = 13 ∧
      (93910773372 : ℤ) = ⌊logCenter (11981 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11981 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11981 : Reach 11981 118310941715318 167392024189 := by
  have hr := row_11981
  have hl := log_bounds hr.1
    (by change logScale (11981 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11971) (T := 118217030941946) (U := 167378052732)
    (by norm_num) (by norm_num) hr.1 gap_11981
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11971

theorem gap_11987 : PrimeGap 11981 11987 :=
  (primeGap_of_factors (ds := [2, 23, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11987 :
    (11987 : ℕ).Prime ∧ logScale (11987 : ℚ) = 13 ∧
      (93915780048 : ℤ) = ⌊logCenter (11987 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11987 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11987 : Reach 11987 118404857495366 167405989818 := by
  have hr := row_11987
  have hl := log_bounds hr.1
    (by change logScale (11987 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11981) (T := 118310941715318) (U := 167392024189)
    (by norm_num) (by norm_num) hr.1 gap_11987
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11981

theorem gap_12007 : PrimeGap 11987 12007 :=
  (primeGap_of_factors (ds := [2, 19, 2, 3, 2, 67, 2, 5, 2, 3, 2, 13, 2, 11, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12007 :
    (12007 : ℕ).Prime ∧ logScale (12007 : ℚ) = 13 ∧
      (93932450886 : ℤ) = ⌊logCenter (12007 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12007 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12007 : Reach 12007 118498789946252 167419933346 := by
  have hr := row_12007
  have hl := log_bounds hr.1
    (by change logScale (12007 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11987) (T := 118404857495366) (U := 167405989818)
    (by norm_num) (by norm_num) hr.1 gap_12007
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11987

theorem gap_12011 : PrimeGap 12007 12011 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12011 :
    (12011 : ℕ).Prime ∧ logScale (12011 : ℚ) = 13 ∧
      (93935781721 : ℤ) = ⌊logCenter (12011 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12011 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12011 : Reach 12011 118592725727973 167433873391 := by
  have hr := row_12011
  have hl := log_bounds hr.1
    (by change logScale (12011 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12007) (T := 118498789946252) (U := 167419933346)
    (by norm_num) (by norm_num) hr.1 gap_12011
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12007

theorem gap_12037 : PrimeGap 12011 12037 :=
  (primeGap_of_factors (ds := [2, 41, 2, 3, 2, 61, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 23, 2, 53, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12037 :
    (12037 : ℕ).Prime ∧ logScale (12037 : ℚ) = 13 ∧
      (93957405150 : ℤ) = ⌊logCenter (12037 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12037 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12037 : Reach 12037 118686683133123 167447784481 := by
  have hr := row_12037
  have hl := log_bounds hr.1
    (by change logScale (12037 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12011) (T := 118592725727973) (U := 167433873391)
    (by norm_num) (by norm_num) hr.1 gap_12037
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12011

theorem gap_12041 : PrimeGap 12037 12041 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12041 :
    (12041 : ℕ).Prime ∧ logScale (12041 : ℚ) = 13 ∧
      (93960727685 : ℤ) = ⌊logCenter (12041 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12041 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12041 : Reach 12041 118780643860808 167461692105 := by
  have hr := row_12041
  have hl := log_bounds hr.1
    (by change logScale (12041 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12037) (T := 118686683133123) (U := 167447784481)
    (by norm_num) (by norm_num) hr.1 gap_12041
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12037

theorem gap_12043 : PrimeGap 12041 12043 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_12043 :
    (12043 : ℕ).Prime ∧ logScale (12043 : ℚ) = 13 ∧
      (93962388538 : ℤ) = ⌊logCenter (12043 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12043 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12043 : Reach 12043 118874606249346 167475598574 := by
  have hr := row_12043
  have hl := log_bounds hr.1
    (by change logScale (12043 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12041) (T := 118780643860808) (U := 167461692105)
    (by norm_num) (by norm_num) hr.1 gap_12043
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12041

theorem gap_12049 : PrimeGap 12043 12049 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12049 :
    (12049 : ℕ).Prime ∧ logScale (12049 : ℚ) = 13 ∧
      (93967369445 : ℤ) = ⌊logCenter (12049 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12049 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12049 : Reach 12049 118968573618791 167489499272 := by
  have hr := row_12049
  have hl := log_bounds hr.1
    (by change logScale (12049 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12043) (T := 118874606249346) (U := 167475598574)
    (by norm_num) (by norm_num) hr.1 gap_12049
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12043

#print axioms reach_12049

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
