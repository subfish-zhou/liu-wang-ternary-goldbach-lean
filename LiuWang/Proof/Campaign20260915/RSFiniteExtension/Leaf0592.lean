import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0591
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_13859 : PrimeGap 13841 13859 :=
  (primeGap_of_factors (ds := [2, 109, 2, 3, 2, 61, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13859 :
    (13859 : ℕ).Prime ∧ logScale (13859 : ℚ) = 13 ∧
      (95366901166 : ℤ) = ⌊logCenter (13859 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13859 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13859 : Reach 13859 137241729803362 170008770576 := by
  have hr := row_13859
  have hl := log_bounds hr.1
    (by change logScale (13859 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13841) (T := 137146362902196) (U := 169996503545)
    (by norm_num) (by norm_num) hr.1 gap_13859
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13841

theorem gap_13873 : PrimeGap 13859 13873 :=
  (primeGap_of_factors (ds := [2, 83, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13873 :
    (13873 : ℕ).Prime ∧ logScale (13873 : ℚ) = 13 ∧
      (95376997807 : ℤ) = ⌊logCenter (13873 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13873 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13873 : Reach 13873 137337106801169 170021026111 := by
  have hr := row_13873
  have hl := log_bounds hr.1
    (by change logScale (13873 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13859) (T := 137241729803362) (U := 170008770576)
    (by norm_num) (by norm_num) hr.1 gap_13873
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13859

theorem gap_13877 : PrimeGap 13873 13877 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13877 :
    (13877 : ℕ).Prime ∧ logScale (13877 : ℚ) = 13 ∧
      (95379880689 : ℤ) = ⌊logCenter (13877 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13877 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13877 : Reach 13877 137432486681858 170033278996 := by
  have hr := row_13877
  have hl := log_bounds hr.1
    (by change logScale (13877 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13873) (T := 137337106801169) (U := 170021026111)
    (by norm_num) (by norm_num) hr.1 gap_13877
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13873

theorem gap_13879 : PrimeGap 13877 13879 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_13879 :
    (13879 : ℕ).Prime ∧ logScale (13879 : ℚ) = 13 ∧
      (95381321819 : ℤ) = ⌊logCenter (13879 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13879 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13879 : Reach 13879 137527868003677 170045530998 := by
  have hr := row_13879
  have hl := log_bounds hr.1
    (by change logScale (13879 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13877) (T := 137432486681858) (U := 170033278996)
    (by norm_num) (by norm_num) hr.1 gap_13879
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13877

theorem gap_13883 : PrimeGap 13879 13883 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13883 :
    (13883 : ℕ).Prime ∧ logScale (13883 : ℚ) = 13 ∧
      (95384203456 : ℤ) = ⌊logCenter (13883 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13883 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13883 : Reach 13883 137623252207133 170057780352 := by
  have hr := row_13883
  have hl := log_bounds hr.1
    (by change logScale (13883 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13879) (T := 137527868003677) (U := 170045530998)
    (by norm_num) (by norm_num) hr.1 gap_13883
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13879

theorem gap_13901 : PrimeGap 13883 13901 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 17, 2, 29, 2, 3, 2, 5, 2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13901 :
    (13901 : ℕ).Prime ∧ logScale (13901 : ℚ) = 13 ∧
      (95397160555 : ℤ) = ⌊logCenter (13901 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13901 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13901 : Reach 13901 137718649367688 170070014725 := by
  have hr := row_13901
  have hl := log_bounds hr.1
    (by change logScale (13901 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13883) (T := 137623252207133) (U := 170057780352)
    (by norm_num) (by norm_num) hr.1 gap_13901
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13883

theorem gap_13903 : PrimeGap 13901 13903 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_13903 :
    (13903 : ℕ).Prime ∧ logScale (13903 : ℚ) = 13 ∧
      (95398599197 : ℤ) = ⌊logCenter (13903 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13903 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13903 : Reach 13903 137814047966885 170082248218 := by
  have hr := row_13903
  have hl := log_bounds hr.1
    (by change logScale (13903 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13901) (T := 137718649367688) (U := 170070014725)
    (by norm_num) (by norm_num) hr.1 gap_13903
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13901

theorem gap_13907 : PrimeGap 13903 13907 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13907 :
    (13907 : ℕ).Prime ∧ logScale (13907 : ℚ) = 13 ∧
      (95401475860 : ℤ) = ⌊logCenter (13907 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13907 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13907 : Reach 13907 137909449442745 170094479072 := by
  have hr := row_13907
  have hl := log_bounds hr.1
    (by change logScale (13907 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13903) (T := 137814047966885) (U := 170082248218)
    (by norm_num) (by norm_num) hr.1 gap_13907
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13903

#print axioms reach_13907

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
