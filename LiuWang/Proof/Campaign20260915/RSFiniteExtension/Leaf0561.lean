import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0560
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_13093 : PrimeGap 13063 13093 :=
  (primeGap_of_factors (ds := [2, 3, 2, 73, 2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 11, 2, 103, 2, 3, 2, 5, 2, 23, 2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13093 :
    (13093 : ℕ).Prime ∧ logScale (13093 : ℚ) = 13 ∧
      (94798330118 : ℤ) = ⌊logCenter (13093 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13093 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13093 : Reach 13093 129634810816550 169002310789 := by
  have hr := row_13093
  have hl := log_bounds hr.1
    (by change logScale (13093 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13063) (T := 129540012486432) (U := 168989402951)
    (by norm_num) (by norm_num) hr.1 gap_13093
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13063

theorem gap_13099 : PrimeGap 13093 13099 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13099 :
    (13099 : ℕ).Prime ∧ logScale (13099 : ℚ) = 13 ∧
      (94802911670 : ℤ) = ⌊logCenter (13099 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13099 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13099 : Reach 13099 129729613728220 169015213699 := by
  have hr := row_13099
  have hl := log_bounds hr.1
    (by change logScale (13099 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13093) (T := 129634810816550) (U := 169002310789)
    (by norm_num) (by norm_num) hr.1 gap_13099
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13093

theorem gap_13103 : PrimeGap 13099 13103 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13103 :
    (13103 : ℕ).Prime ∧ logScale (13103 : ℚ) = 13 ∧
      (94805964872 : ℤ) = ⌊logCenter (13103 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13103 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13103 : Reach 13103 129824419693092 169028113655 := by
  have hr := row_13103
  have hl := log_bounds hr.1
    (by change logScale (13103 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13099) (T := 129729613728220) (U := 169015213699)
    (by norm_num) (by norm_num) hr.1 gap_13103
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13099

theorem gap_13109 : PrimeGap 13103 13109 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13109 :
    (13109 : ℕ).Prime ∧ logScale (13109 : ℚ) = 13 ∧
      (94810542928 : ℤ) = ⌊logCenter (13109 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13109 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13109 : Reach 13109 129919230236020 169041008690 := by
  have hr := row_13109
  have hl := log_bounds hr.1
    (by change logScale (13109 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13103) (T := 129824419693092) (U := 169028113655)
    (by norm_num) (by norm_num) hr.1 gap_13109
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13103

theorem gap_13121 : PrimeGap 13109 13121 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13121 :
    (13121 : ℕ).Prime ∧ logScale (13121 : ℚ) = 13 ∧
      (94819692757 : ℤ) = ⌊logCenter (13121 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13121 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13121 : Reach 13121 130014049928777 169053892914 := by
  have hr := row_13121
  have hl := log_bounds hr.1
    (by change logScale (13121 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13109) (T := 129919230236020) (U := 169041008690)
    (by norm_num) (by norm_num) hr.1 gap_13121
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13109

theorem gap_13127 : PrimeGap 13121 13127 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13127 :
    (13127 : ℕ).Prime ∧ logScale (13127 : ℚ) = 13 ∧
      (94824264534 : ℤ) = ⌊logCenter (13127 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13127 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13127 : Reach 13127 130108874193311 169066772230 := by
  have hr := row_13127
  have hl := log_bounds hr.1
    (by change logScale (13127 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13121) (T := 130014049928777) (U := 169053892914)
    (by norm_num) (by norm_num) hr.1 gap_13127
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13121

theorem gap_13147 : PrimeGap 13127 13147 :=
  (primeGap_of_factors (ds := [2, 19, 2, 3, 2, 23, 2, 5, 2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13147 :
    (13147 : ℕ).Prime ∧ logScale (13147 : ℚ) = 13 ∧
      (94839488713 : ℤ) = ⌊logCenter (13147 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13147 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13147 : Reach 13147 130203713682024 169079632931 := by
  have hr := row_13147
  have hl := log_bounds hr.1
    (by change logScale (13147 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13127) (T := 130108874193311) (U := 169066772230)
    (by norm_num) (by norm_num) hr.1 gap_13147
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13127

theorem gap_13151 : PrimeGap 13147 13151 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13151 :
    (13151 : ℕ).Prime ∧ logScale (13151 : ℚ) = 13 ∧
      (94842530769 : ℤ) = ⌊logCenter (13151 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13151 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13151 : Reach 13151 130298556212793 169092490698 := by
  have hr := row_13151
  have hl := log_bounds hr.1
    (by change logScale (13151 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13147) (T := 130203713682024) (U := 169079632931)
    (by norm_num) (by norm_num) hr.1 gap_13151
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13147

#print axioms reach_13151

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
