import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0511
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_12071 : PrimeGap 12049 12071 :=
  (primeGap_of_factors (ds := [2, 3, 2, 17, 2, 5, 2, 3, 2, 31, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12071 :
    (12071 : ℕ).Prime ∧ logScale (12071 : ℚ) = 13 ∧
      (93985611573 : ℤ) = ⌊logCenter (12071 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12071 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12071 : Reach 12071 119062559230364 167503375784 := by
  have hr := row_12071
  have hl := log_bounds hr.1
    (by change logScale (12071 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12049) (T := 118968573618791) (U := 167489499272)
    (by norm_num) (by norm_num) hr.1 gap_12071
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12049

theorem gap_12073 : PrimeGap 12071 12073 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_12073 :
    (12073 : ℕ).Prime ∧ logScale (12073 : ℚ) = 13 ∧
      (93987268299 : ℤ) = ⌊logCenter (12073 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12073 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12073 : Reach 12073 119156546498663 167517251147 := by
  have hr := row_12073
  have hl := log_bounds hr.1
    (by change logScale (12073 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12071) (T := 119062559230364) (U := 167503375784)
    (by norm_num) (by norm_num) hr.1 gap_12073
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12071

theorem gap_12097 : PrimeGap 12073 12097 :=
  (primeGap_of_factors (ds := [2, 3, 2, 13, 2, 47, 2, 3, 2, 43, 2, 5, 2, 3, 2, 7, 2, 107, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12097 :
    (12097 : ℕ).Prime ∧ logScale (12097 : ℚ) = 13 ∧
      (94007127635 : ℤ) = ⌊logCenter (12097 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12097 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12097 : Reach 12097 119250553626298 167531100127 := by
  have hr := row_12097
  have hl := log_bounds hr.1
    (by change logScale (12097 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12073) (T := 119156546498663) (U := 167517251147)
    (by norm_num) (by norm_num) hr.1 gap_12097
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12073

theorem gap_12101 : PrimeGap 12097 12101 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12101 :
    (12101 : ℕ).Prime ∧ logScale (12101 : ℚ) = 13 ∧
      (94010433694 : ℤ) = ⌊logCenter (12101 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12101 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12101 : Reach 12101 119344564059992 167544945673 := by
  have hr := row_12101
  have hl := log_bounds hr.1
    (by change logScale (12101 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12097) (T := 119250553626298) (U := 167531100127)
    (by norm_num) (by norm_num) hr.1 gap_12101
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12097

theorem gap_12107 : PrimeGap 12101 12107 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12107 :
    (12107 : ℕ).Prime ∧ logScale (12107 : ℚ) = 13 ∧
      (94015390733 : ℤ) = ⌊logCenter (12107 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12107 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12107 : Reach 12107 119438579450725 167558785501 := by
  have hr := row_12107
  have hl := log_bounds hr.1
    (by change logScale (12107 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12101) (T := 119344564059992) (U := 167544945673)
    (by norm_num) (by norm_num) hr.1 gap_12107
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12101

theorem gap_12109 : PrimeGap 12107 12109 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_12109 :
    (12109 : ℕ).Prime ∧ logScale (12109 : ℚ) = 13 ∧
      (94017042533 : ℤ) = ⌊logCenter (12109 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12109 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12109 : Reach 12109 119532596493258 167572624185 := by
  have hr := row_12109
  have hl := log_bounds hr.1
    (by change logScale (12109 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12107) (T := 119438579450725) (U := 167558785501)
    (by norm_num) (by norm_num) hr.1 gap_12109
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12107

theorem gap_12113 : PrimeGap 12109 12113 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12113 :
    (12113 : ℕ).Prime ∧ logScale (12113 : ℚ) = 13 ∧
      (94020345316 : ℤ) = ⌊logCenter (12113 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12113 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12113 : Reach 12113 119626616838574 167586459442 := by
  have hr := row_12113
  have hl := log_bounds hr.1
    (by change logScale (12113 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12109) (T := 119532596493258) (U := 167572624185)
    (by norm_num) (by norm_num) hr.1 gap_12113
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12109

theorem gap_12119 : PrimeGap 12113 12119 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12119 :
    (12119 : ℕ).Prime ∧ logScale (12119 : ℚ) = 13 ∧
      (94025297445 : ℤ) = ⌊logCenter (12119 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12119 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12119 : Reach 12119 119720642136019 167600288990 := by
  have hr := row_12119
  have hl := log_bounds hr.1
    (by change logScale (12119 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12113) (T := 119626616838574) (U := 167586459442)
    (by norm_num) (by norm_num) hr.1 gap_12119
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12113

#print axioms reach_12119

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
