import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0631
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_14783 : PrimeGap 14779 14783 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14783 :
    (14783 : ℕ).Prime ∧ logScale (14783 : ℚ) = 13 ∧
      (96012331475 : ℤ) = ⌊logCenter (14783 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14783 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14783 : Reach 14783 146430157573467 171150444866 := by
  have hr := row_14783
  have hl := log_bounds hr.1
    (by change logScale (14783 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14779) (T := 146334145241992) (U := 171138867348)
    (by norm_num) (by norm_num) hr.1 gap_14783
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14779

theorem gap_14797 : PrimeGap 14783 14797 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 23, 2, 7, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14797 :
    (14797 : ℕ).Prime ∧ logScale (14797 : ℚ) = 13 ∧
      (96021797331 : ℤ) = ⌊logCenter (14797 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14797 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14797 : Reach 14797 146526179370798 171162012212 := by
  have hr := row_14797
  have hl := log_bounds hr.1
    (by change logScale (14797 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14783) (T := 146430157573467) (U := 171150444866)
    (by norm_num) (by norm_num) hr.1 gap_14797
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14783

theorem gap_14813 : PrimeGap 14797 14813 :=
  (primeGap_of_factors (ds := [2, 3, 2, 19, 2, 113, 2, 3, 2, 13, 2, 59, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14813 :
    (14813 : ℕ).Prime ∧ logScale (14813 : ℚ) = 13 ∧
      (96032604492 : ℤ) = ⌊logCenter (14813 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14813 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14813 : Reach 14813 146622211975290 171173567844 := by
  have hr := row_14813
  have hl := log_bounds hr.1
    (by change logScale (14813 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14797) (T := 146526179370798) (U := 171162012212)
    (by norm_num) (by norm_num) hr.1 gap_14813
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14797

theorem gap_14821 : PrimeGap 14813 14821 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14821 :
    (14821 : ℕ).Prime ∧ logScale (14821 : ℚ) = 13 ∧
      (96038003695 : ℤ) = ⌊logCenter (14821 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14821 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14821 : Reach 14821 146718249978985 171185118018 := by
  have hr := row_14821
  have hl := log_bounds hr.1
    (by change logScale (14821 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14813) (T := 146622211975290) (U := 171173567844)
    (by norm_num) (by norm_num) hr.1 gap_14821
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14813

theorem gap_14827 : PrimeGap 14821 14827 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14827 :
    (14827 : ℕ).Prime ∧ logScale (14827 : ℚ) = 13 ∧
      (96042051186 : ℤ) = ⌊logCenter (14827 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14827 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14827 : Reach 14827 146814292030171 171196664297 := by
  have hr := row_14827
  have hl := log_bounds hr.1
    (by change logScale (14827 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14821) (T := 146718249978985) (U := 171185118018)
    (by norm_num) (by norm_num) hr.1 gap_14827
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14821

theorem gap_14831 : PrimeGap 14827 14831 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14831 :
    (14831 : ℕ).Prime ∧ logScale (14831 : ℚ) = 13 ∧
      (96044748603 : ℤ) = ⌊logCenter (14831 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14831 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14831 : Reach 14831 146910336778774 171208208240 := by
  have hr := row_14831
  have hl := log_bounds hr.1
    (by change logScale (14831 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14827) (T := 146814292030171) (U := 171196664297)
    (by norm_num) (by norm_num) hr.1 gap_14831
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14827

theorem gap_14843 : PrimeGap 14831 14843 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 37, 2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14843 :
    (14843 : ℕ).Prime ∧ logScale (14843 : ℚ) = 13 ∧
      (96052836492 : ℤ) = ⌊logCenter (14843 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14843 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14843 : Reach 14843 147006389615266 171219743627 := by
  have hr := row_14843
  have hl := log_bounds hr.1
    (by change logScale (14843 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14831) (T := 146910336778774) (U := 171208208240)
    (by norm_num) (by norm_num) hr.1 gap_14843
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14831

theorem gap_14851 : PrimeGap 14843 14851 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 31, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14851 :
    (14851 : ℕ).Prime ∧ logScale (14851 : ℚ) = 13 ∧
      (96058224786 : ℤ) = ⌊logCenter (14851 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14851 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14851 : Reach 14851 147102447840052 171231273577 := by
  have hr := row_14851
  have hl := log_bounds hr.1
    (by change logScale (14851 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14843) (T := 147006389615266) (U := 171219743627)
    (by norm_num) (by norm_num) hr.1 gap_14851
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14843

#print axioms reach_14851

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
