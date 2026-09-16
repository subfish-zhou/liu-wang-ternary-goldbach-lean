import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0370
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_8837 : PrimeGap 8831 8837 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8837 :
    (8837 : ℕ).Prime ∧ logScale (8837 : ℚ) = 13 ∧
      (90867027281 : ℤ) = ⌊logCenter (8837 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8837 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8837 : Reach 8837 87248475999763 162024499823 := by
  have hr := row_8837
  have hl := log_bounds hr.1
    (by change logScale (8837 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8831) (T := 87157608972482) (U := 162006165037)
    (by norm_num) (by norm_num) hr.1 gap_8837
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8831

theorem gap_8839 : PrimeGap 8837 8839 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_8839 :
    (8839 : ℕ).Prime ∧ logScale (8839 : ℚ) = 13 ∧
      (90869290236 : ℤ) = ⌊logCenter (8839 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8839 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8839 : Reach 8839 87339345289999 162042832535 := by
  have hr := row_8839
  have hl := log_bounds hr.1
    (by change logScale (8839 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8837) (T := 87248475999763) (U := 162024499823)
    (by norm_num) (by norm_num) hr.1 gap_8839
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8837

theorem gap_8849 : PrimeGap 8839 8849 :=
  (primeGap_of_factors (ds := [2, 3, 2, 37, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8849 :
    (8849 : ℕ).Prime ∧ logScale (8849 : ℚ) = 13 ∧
      (90880597338 : ℤ) = ⌊logCenter (8849 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8849 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8849 : Reach 8849 87430225887337 162061146599 := by
  have hr := row_8849
  have hl := log_bounds hr.1
    (by change logScale (8849 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8839) (T := 87339345289999) (U := 162042832535)
    (by norm_num) (by norm_num) hr.1 gap_8849
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8839

theorem gap_8861 : PrimeGap 8849 8861 :=
  (primeGap_of_factors (ds := [2, 53, 2, 3, 2, 5, 2, 17, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8861 :
    (8861 : ℕ).Prime ∧ logScale (8861 : ℚ) = 13 ∧
      (90894149006 : ℤ) = ⌊logCenter (8861 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8861 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8861 : Reach 8861 87521120036343 162079437925 := by
  have hr := row_8861
  have hl := log_bounds hr.1
    (by change logScale (8861 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8849) (T := 87430225887337) (U := 162061146599)
    (by norm_num) (by norm_num) hr.1 gap_8861
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8849

theorem gap_8863 : PrimeGap 8861 8863 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_8863 :
    (8863 : ℕ).Prime ∧ logScale (8863 : ℚ) = 13 ∧
      (90896405833 : ℤ) = ⌊logCenter (8863 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8863 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8863 : Reach 8863 87612016442176 162097727187 := by
  have hr := row_8863
  have hl := log_bounds hr.1
    (by change logScale (8863 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8861) (T := 87521120036343) (U := 162079437925)
    (by norm_num) (by norm_num) hr.1 gap_8863
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8861

theorem gap_8867 : PrimeGap 8863 8867 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8867 :
    (8867 : ℕ).Prime ∧ logScale (8867 : ℚ) = 13 ∧
      (90900917960 : ℤ) = ⌊logCenter (8867 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8867 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8867 : Reach 8867 87702917360136 162116010261 := by
  have hr := row_8867
  have hl := log_bounds hr.1
    (by change logScale (8867 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8863) (T := 87612016442176) (U := 162097727187)
    (by norm_num) (by norm_num) hr.1 gap_8867
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8863

theorem gap_8887 : PrimeGap 8867 8887 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 19, 2, 5, 2, 3, 2, 13, 2, 83, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8887 :
    (8887 : ℕ).Prime ∧ logScale (8887 : ℚ) = 13 ∧
      (90923448103 : ℤ) = ⌊logCenter (8887 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8887 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8887 : Reach 8887 87793840808239 162134254242 := by
  have hr := row_8887
  have hl := log_bounds hr.1
    (by change logScale (8887 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8867) (T := 87702917360136) (U := 162116010261)
    (by norm_num) (by norm_num) hr.1 gap_8887
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8867

theorem gap_8893 : PrimeGap 8887 8893 :=
  (primeGap_of_factors (ds := [2, 3, 2, 17, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8893 :
    (8893 : ℕ).Prime ∧ logScale (8893 : ℚ) = 13 ∧
      (90930197260 : ℤ) = ⌊logCenter (8893 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8893 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8893 : Reach 8893 87884771005499 162152487964 := by
  have hr := row_8893
  have hl := log_bounds hr.1
    (by change logScale (8893 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8887) (T := 87793840808239) (U := 162134254242)
    (by norm_num) (by norm_num) hr.1 gap_8893
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8887

#print axioms reach_8893

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
