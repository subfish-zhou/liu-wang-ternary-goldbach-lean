import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0500
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_11789 : PrimeGap 11783 11789 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11789 :
    (11789 : ℕ).Prime ∧ logScale (11789 : ℚ) = 13 ∧
      (93749221689 : ℤ) = ⌊logCenter (11789 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11789 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11789 : Reach 11789 116058887224590 167054501731 := by
  have hr := row_11789
  have hl := log_bounds hr.1
    (by change logScale (11789 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11783) (T := 115965138002901) (U := 167040331360)
    (by norm_num) (by norm_num) hr.1 gap_11789
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11783

theorem gap_11801 : PrimeGap 11789 11801 :=
  (primeGap_of_factors (ds := [2, 13, 2, 3, 2, 5, 2, 47, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11801 :
    (11801 : ℕ).Prime ∧ logScale (11801 : ℚ) = 13 ∧
      (93759395492 : ℤ) = ⌊logCenter (11801 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11801 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11801 : Reach 11801 116152646620082 167068658893 := by
  have hr := row_11801
  have hl := log_bounds hr.1
    (by change logScale (11801 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11789) (T := 116058887224590) (U := 167054501731)
    (by norm_num) (by norm_num) hr.1 gap_11801
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11789

theorem gap_11807 : PrimeGap 11801 11807 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11807 :
    (11807 : ℕ).Prime ∧ logScale (11807 : ℚ) = 13 ∧
      (93764478515 : ℤ) = ⌊logCenter (11807 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11807 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11807 : Reach 11807 116246411098597 167082810059 := by
  have hr := row_11807
  have hl := log_bounds hr.1
    (by change logScale (11807 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11801) (T := 116152646620082) (U := 167068658893)
    (by norm_num) (by norm_num) hr.1 gap_11807
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11801

theorem gap_11813 : PrimeGap 11807 11813 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11813 :
    (11813 : ℕ).Prime ∧ logScale (11813 : ℚ) = 13 ∧
      (93769558955 : ℤ) = ⌊logCenter (11813 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11813 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11813 : Reach 11813 116340180657552 167096955235 := by
  have hr := row_11813
  have hl := log_bounds hr.1
    (by change logScale (11813 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11807) (T := 116246411098597) (U := 167082810059)
    (by norm_num) (by norm_num) hr.1 gap_11813
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11807

theorem gap_11821 : PrimeGap 11813 11821 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 53, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11821 :
    (11821 : ℕ).Prime ∧ logScale (11821 : ℚ) = 13 ∧
      (93776328863 : ℤ) = ⌊logCenter (11821 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11821 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11821 : Reach 11821 116433956986415 167111092034 := by
  have hr := row_11821
  have hl := log_bounds hr.1
    (by change logScale (11821 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11813) (T := 116340180657552) (U := 167096955235)
    (by norm_num) (by norm_num) hr.1 gap_11821
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11813

theorem gap_11827 : PrimeGap 11821 11827 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11827 :
    (11827 : ℕ).Prime ∧ logScale (11827 : ℚ) = 13 ∧
      (93781403288 : ℤ) = ⌊logCenter (11827 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11827 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11827 : Reach 11827 116527738389703 167125222856 := by
  have hr := row_11827
  have hl := log_bounds hr.1
    (by change logScale (11827 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11821) (T := 116433956986415) (U := 167111092034)
    (by norm_num) (by norm_num) hr.1 gap_11827
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11821

theorem gap_11831 : PrimeGap 11827 11831 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11831 :
    (11831 : ℕ).Prime ∧ logScale (11831 : ℚ) = 13 ∧
      (93784784808 : ℤ) = ⌊logCenter (11831 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11831 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11831 : Reach 11831 116621523174511 167139350094 := by
  have hr := row_11831
  have hl := log_bounds hr.1
    (by change logScale (11831 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11827) (T := 116527738389703) (U := 167125222856)
    (by norm_num) (by norm_num) hr.1 gap_11831
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11827

theorem gap_11833 : PrimeGap 11831 11833 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_11833 :
    (11833 : ℕ).Prime ∧ logScale (11833 : ℚ) = 13 ∧
      (93786475140 : ℤ) = ⌊logCenter (11833 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11833 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11833 : Reach 11833 116715309649651 167153476138 := by
  have hr := row_11833
  have hl := log_bounds hr.1
    (by change logScale (11833 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11831) (T := 116621523174511) (U := 167139350094)
    (by norm_num) (by norm_num) hr.1 gap_11833
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11831

#print axioms reach_11833

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
