import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0461
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_10891 : PrimeGap 10889 10891 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_10891 :
    (10891 : ℕ).Prime ∧ logScale (10891 : ℚ) = 13 ∧
      (92956920356 : ℤ) = ⌊logCenter (10891 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10891 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10891 : Reach 10891 107843283415147 165762541733 := by
  have hr := row_10891
  have hl := log_bounds hr.1
    (by change logScale (10891 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10889) (T := 107750326494791) (U := 165747321593)
    (by norm_num) (by norm_num) hr.1 gap_10891
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10889

theorem gap_10903 : PrimeGap 10891 10903 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 17, 2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10903 :
    (10903 : ℕ).Prime ∧ logScale (10903 : ℚ) = 13 ∧
      (92967932563 : ℤ) = ⌊logCenter (10903 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10903 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10903 : Reach 10903 107936251347710 165777746516 := by
  have hr := row_10903
  have hl := log_bounds hr.1
    (by change logScale (10903 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10891) (T := 107843283415147) (U := 165762541733)
    (by norm_num) (by norm_num) hr.1 gap_10903
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10891

theorem gap_10909 : PrimeGap 10903 10909 :=
  (primeGap_of_factors (ds := [2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10909 :
    (10909 : ℕ).Prime ∧ logScale (10909 : ℚ) = 13 ∧
      (92973434122 : ℤ) = ⌊logCenter (10909 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10909 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10909 : Reach 10909 108029224781832 165792944330 := by
  have hr := row_10909
  have hl := log_bounds hr.1
    (by change logScale (10909 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10903) (T := 107936251347710) (U := 165777746516)
    (by norm_num) (by norm_num) hr.1 gap_10909
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10903

theorem gap_10937 : PrimeGap 10909 10937 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 5, 2, 3, 2, 61, 2, 67, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10937 :
    (10937 : ℕ).Prime ∧ logScale (10937 : ℚ) = 13 ∧
      (92999068119 : ℤ) = ⌊logCenter (10937 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10937 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10937 : Reach 10937 108122223849951 165808104622 := by
  have hr := row_10937
  have hl := log_bounds hr.1
    (by change logScale (10937 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10909) (T := 108029224781832) (U := 165792944330)
    (by norm_num) (by norm_num) hr.1 gap_10937
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10909

theorem gap_10939 : PrimeGap 10937 10939 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_10939 :
    (10939 : ℕ).Prime ∧ logScale (10939 : ℚ) = 13 ∧
      (93000896607 : ℤ) = ⌊logCenter (10939 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10939 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10939 : Reach 10939 108215224746558 165823263528 := by
  have hr := row_10939
  have hl := log_bounds hr.1
    (by change logScale (10939 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10937) (T := 108122223849951) (U := 165808104622)
    (by norm_num) (by norm_num) hr.1 gap_10939
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10937

theorem gap_10949 : PrimeGap 10939 10949 :=
  (primeGap_of_factors (ds := [2, 3, 2, 31, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10949 :
    (10949 : ℕ).Prime ∧ logScale (10949 : ℚ) = 13 ∧
      (93010034034 : ℤ) = ⌊logCenter (10949 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10949 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10949 : Reach 10949 108308234780592 165838409972 := by
  have hr := row_10949
  have hl := log_bounds hr.1
    (by change logScale (10949 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10939) (T := 108215224746558) (U := 165823263528)
    (by norm_num) (by norm_num) hr.1 gap_10949
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10939

theorem gap_10957 : PrimeGap 10949 10957 :=
  (primeGap_of_factors (ds := [2, 47, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10957 :
    (10957 : ℕ).Prime ∧ logScale (10957 : ℚ) = 13 ∧
      (93017337970 : ℤ) = ⌊logCenter (10957 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10957 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10957 : Reach 10957 108401252118562 165853546739 := by
  have hr := row_10957
  have hl := log_bounds hr.1
    (by change logScale (10957 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10949) (T := 108308234780592) (U := 165838409972)
    (by norm_num) (by norm_num) hr.1 gap_10957
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10949

theorem gap_10973 : PrimeGap 10957 10973 :=
  (primeGap_of_factors (ds := [2, 3, 2, 97, 2, 19, 2, 3, 2, 11, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10973 :
    (10973 : ℕ).Prime ∧ logScale (10973 : ℚ) = 13 ∧
      (93031929856 : ℤ) = ⌊logCenter (10973 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10973 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10973 : Reach 10973 108494284048418 165868662812 := by
  have hr := row_10973
  have hl := log_bounds hr.1
    (by change logScale (10973 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10957) (T := 108401252118562) (U := 165853546739)
    (by norm_num) (by norm_num) hr.1 gap_10973
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10957

#print axioms reach_10973

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
