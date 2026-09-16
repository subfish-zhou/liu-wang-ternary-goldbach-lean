import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0420
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_9901 : PrimeGap 9887 9901 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 13, 2, 5, 2, 3, 2, 19, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9901 :
    (9901 : ℕ).Prime ∧ logScale (9901 : ℚ) = 13 ∧
      (92003910377 : ℤ) = ⌊logCenter (9901 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9901 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9901 : Reach 9901 98223568147753 164112753958 := by
  have hr := row_9901
  have hl := log_bounds hr.1
    (by change logScale (9901 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9887) (T := 98131564237376) (U := 164096178586)
    (by norm_num) (by norm_num) hr.1 gap_9901
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9887

theorem gap_9907 : PrimeGap 9901 9907 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9907 :
    (9907 : ℕ).Prime ∧ logScale (9907 : ℚ) = 13 ∧
      (92009968535 : ℤ) = ⌊logCenter (9907 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9907 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9907 : Reach 9907 98315578116288 164129320964 := by
  have hr := row_9907
  have hl := log_bounds hr.1
    (by change logScale (9907 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9901) (T := 98223568147753) (U := 164112753958)
    (by norm_num) (by norm_num) hr.1 gap_9907
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9901

theorem gap_9923 : PrimeGap 9907 9923 :=
  (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 23, 2, 3, 2, 47, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9923 :
    (9923 : ℕ).Prime ∧ logScale (9923 : ℚ) = 13 ∧
      (92026105705 : ℤ) = ⌊logCenter (9923 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9923 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9923 : Reach 9923 98407604221993 164145862924 := by
  have hr := row_9923
  have hl := log_bounds hr.1
    (by change logScale (9923 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9907) (T := 98315578116288) (U := 164129320964)
    (by norm_num) (by norm_num) hr.1 gap_9923
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9907

theorem gap_9929 : PrimeGap 9923 9929 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9929 :
    (9929 : ℕ).Prime ∧ logScale (9929 : ℚ) = 13 ∧
      (92032150436 : ℤ) = ⌊logCenter (9929 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9929 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9929 : Reach 9929 98499636372429 164162396553 := by
  have hr := row_9929
  have hl := log_bounds hr.1
    (by change logScale (9929 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9923) (T := 98407604221993) (U := 164145862924)
    (by norm_num) (by norm_num) hr.1 gap_9929
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9923

theorem gap_9931 : PrimeGap 9929 9931 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_9931 :
    (9931 : ℕ).Prime ∧ logScale (9931 : ℚ) = 13 ∧
      (92034164535 : ℤ) = ⌊logCenter (9931 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9931 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9931 : Reach 9931 98591670536964 164178928517 := by
  have hr := row_9931
  have hl := log_bounds hr.1
    (by change logScale (9931 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9929) (T := 98499636372429) (U := 164162396553)
    (by norm_num) (by norm_num) hr.1 gap_9931
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9929

theorem gap_9941 : PrimeGap 9931 9941 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 19, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9941 :
    (9941 : ℕ).Prime ∧ logScale (9941 : ℚ) = 13 ∧
      (92044228948 : ℤ) = ⌊logCenter (9941 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9941 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9941 : Reach 9941 98683714765912 164195445512 := by
  have hr := row_9941
  have hl := log_bounds hr.1
    (by change logScale (9941 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9931) (T := 98591670536964) (U := 164178928517)
    (by norm_num) (by norm_num) hr.1 gap_9941
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9931

theorem gap_9949 : PrimeGap 9941 9949 :=
  (primeGap_of_factors (ds := [2, 61, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9949 :
    (9949 : ℕ).Prime ∧ logScale (9949 : ℚ) = 13 ∧
      (92052273192 : ℤ) = ⌊logCenter (9949 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9949 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9949 : Reach 9949 98775767039104 164211950885 := by
  have hr := row_9949
  have hl := log_bounds hr.1
    (by change logScale (9949 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9941) (T := 98683714765912) (U := 164195445512)
    (by norm_num) (by norm_num) hr.1 gap_9949
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9941

theorem gap_9967 : PrimeGap 9949 9967 :=
  (primeGap_of_factors (ds := [2, 3, 2, 37, 2, 5, 2, 3, 2, 23, 2, 7, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9967 :
    (9967 : ℕ).Prime ∧ logScale (9967 : ℚ) = 13 ∧
      (92070349115 : ℤ) = ⌊logCenter (9967 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9967 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9967 : Reach 9967 98867837388219 164228428103 := by
  have hr := row_9967
  have hl := log_bounds hr.1
    (by change logScale (9967 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9949) (T := 98775767039104) (U := 164211950885)
    (by norm_num) (by norm_num) hr.1 gap_9967
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9949

#print axioms reach_9967

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
