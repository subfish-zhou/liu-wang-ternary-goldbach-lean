import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0290
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_7079 : PrimeGap 7069 7079 :=
  (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7079 :
    (7079 : ℕ).Prime ∧ logScale (7079 : ℚ) = 12 ∧
      (88648879306 : ℤ) = ⌊logCenter (7079 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7079 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7079 : Reach 7079 70001533961433 158157417136 := by
  have hr := row_7079
  have hl := log_bounds hr.1
    (by change logScale (7079 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7069) (T := 69912885082127) (U := 158135075362)
    (by norm_num) (by norm_num) hr.1 gap_7079
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7069

theorem gap_7103 : PrimeGap 7079 7103 :=
  (primeGap_of_factors (ds := [2, 73, 2, 3, 2, 5, 2, 19, 2, 3, 2, 7, 2, 41, 2, 3, 2, 47, 2, 31, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7103 :
    (7103 : ℕ).Prime ∧ logScale (7103 : ℚ) = 12 ∧
      (88682725058 : ℤ) = ⌊logCenter (7103 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7103 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7103 : Reach 7103 70090216686491 158179686556 := by
  have hr := row_7103
  have hl := log_bounds hr.1
    (by change logScale (7103 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7079) (T := 70001533961433) (U := 158157417136)
    (by norm_num) (by norm_num) hr.1 gap_7103
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7079

theorem gap_7109 : PrimeGap 7103 7109 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7109 :
    (7109 : ℕ).Prime ∧ logScale (7109 : ℚ) = 12 ∧
      (88691168628 : ℤ) = ⌊logCenter (7109 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7109 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7109 : Reach 7109 70178907855119 158201940311 := by
  have hr := row_7109
  have hl := log_bounds hr.1
    (by change logScale (7109 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7103) (T := 70090216686491) (U := 158179686556)
    (by norm_num) (by norm_num) hr.1 gap_7109
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7103

theorem gap_7121 : PrimeGap 7109 7121 :=
  (primeGap_of_factors (ds := [2, 13, 2, 3, 2, 5, 2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7121 :
    (7121 : ℕ).Prime ∧ logScale (7121 : ℚ) = 12 ∧
      (88708034408 : ℤ) = ⌊logCenter (7121 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7121 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7121 : Reach 7121 70267615889527 158224159685 := by
  have hr := row_7121
  have hl := log_bounds hr.1
    (by change logScale (7121 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7109) (T := 70178907855119) (U := 158201940311)
    (by norm_num) (by norm_num) hr.1 gap_7121
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7109

theorem gap_7127 : PrimeGap 7121 7127 :=
  (primeGap_of_factors (ds := [2, 17, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7127 :
    (7127 : ℕ).Prime ∧ logScale (7127 : ℚ) = 12 ∧
      (88716456643 : ℤ) = ⌊logCenter (7127 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7127 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7127 : Reach 7127 70356332346170 158246363469 := by
  have hr := row_7127
  have hl := log_bounds hr.1
    (by change logScale (7127 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7121) (T := 70267615889527) (U := 158224159685)
    (by norm_num) (by norm_num) hr.1 gap_7127
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7121

theorem gap_7129 : PrimeGap 7127 7129 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_7129 :
    (7129 : ℕ).Prime ∧ logScale (7129 : ℚ) = 12 ∧
      (88719262479 : ℤ) = ⌊logCenter (7129 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7129 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7129 : Reach 7129 70445051608649 158268564138 := by
  have hr := row_7129
  have hl := log_bounds hr.1
    (by change logScale (7129 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7127) (T := 70356332346170) (U := 158246363469)
    (by norm_num) (by norm_num) hr.1 gap_7129
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7127

theorem gap_7151 : PrimeGap 7129 7151 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 37, 2, 3, 2, 5, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7151 :
    (7151 : ℕ).Prime ∧ logScale (7151 : ℚ) = 12 ∧
      (88750074829 : ℤ) = ⌊logCenter (7151 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7151 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7151 : Reach 7151 70533801683478 158290699602 := by
  have hr := row_7151
  have hl := log_bounds hr.1
    (by change logScale (7151 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7129) (T := 70445051608649) (U := 158268564138)
    (by norm_num) (by norm_num) hr.1 gap_7151
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7129

theorem gap_7159 : PrimeGap 7151 7159 :=
  (primeGap_of_factors (ds := [2, 23, 2, 3, 2, 17, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7159 :
    (7159 : ℕ).Prime ∧ logScale (7159 : ℚ) = 12 ∧
      (88761255822 : ℤ) = ⌊logCenter (7159 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7159 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7159 : Reach 7159 70622562939300 158312813419 := by
  have hr := row_7159
  have hl := log_bounds hr.1
    (by change logScale (7159 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7151) (T := 70533801683478) (U := 158290699602)
    (by norm_num) (by norm_num) hr.1 gap_7159
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7151

#print axioms reach_7159

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
