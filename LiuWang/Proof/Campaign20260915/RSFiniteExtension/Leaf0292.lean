import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0291
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_7177 : PrimeGap 7159 7177 :=
  (primeGap_of_factors (ds := [2, 3, 2, 13, 2, 5, 2, 3, 2, 67, 2, 71, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7177 :
    (7177 : ℕ).Prime ∧ logScale (7177 : ℚ) = 12 ∧
      (88786367443 : ℤ) = ⌊logCenter (7177 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7177 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7177 : Reach 7177 70711349306743 158334874848 := by
  have hr := row_7177
  have hl := log_bounds hr.1
    (by change logScale (7177 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7159) (T := 70622562939300) (U := 158312813419)
    (by norm_num) (by norm_num) hr.1 gap_7177
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7159

theorem gap_7187 : PrimeGap 7177 7187 :=
  (primeGap_of_factors (ds := [2, 3, 2, 43, 2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7187 :
    (7187 : ℕ).Prime ∧ logScale (7187 : ℚ) = 12 ∧
      (88800291143 : ℤ) = ⌊logCenter (7187 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7187 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7187 : Reach 7187 70800149597886 158356908647 := by
  have hr := row_7187
  have hl := log_bounds hr.1
    (by change logScale (7187 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7177) (T := 70711349306743) (U := 158334874848)
    (by norm_num) (by norm_num) hr.1 gap_7187
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7177

theorem gap_7193 : PrimeGap 7187 7193 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7193 :
    (7193 : ℕ).Prime ∧ logScale (7193 : ℚ) = 12 ∧
      (88808636067 : ℤ) = ⌊logCenter (7193 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7193 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7193 : Reach 7193 70888958233953 158378927128 := by
  have hr := row_7193
  have hl := log_bounds hr.1
    (by change logScale (7193 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7187) (T := 70800149597886) (U := 158356908647)
    (by norm_num) (by norm_num) hr.1 gap_7193
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7187

theorem gap_7207 : PrimeGap 7193 7207 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 23, 2, 19, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7207 :
    (7207 : ℕ).Prime ∧ logScale (7207 : ℚ) = 12 ∧
      (88828080518 : ℤ) = ⌊logCenter (7207 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7207 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7207 : Reach 7207 70977786314471 158400905886 := by
  have hr := row_7207
  have hl := log_bounds hr.1
    (by change logScale (7207 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7193) (T := 70888958233953) (U := 158378927128)
    (by norm_num) (by norm_num) hr.1 gap_7207
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7193

theorem gap_7211 : PrimeGap 7207 7211 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7211 :
    (7211 : ℕ).Prime ∧ logScale (7211 : ℚ) = 12 ∧
      (88833629137 : ℤ) = ⌊logCenter (7211 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7211 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7211 : Reach 7211 71066619943608 158422875499 := by
  have hr := row_7211
  have hl := log_bounds hr.1
    (by change logScale (7211 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7207) (T := 70977786314471) (U := 158400905886)
    (by norm_num) (by norm_num) hr.1 gap_7211
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7207

theorem gap_7213 : PrimeGap 7211 7213 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_7213 :
    (7213 : ℕ).Prime ∧ logScale (7213 : ℚ) = 12 ∧
      (88836402293 : ℤ) = ⌊logCenter (7213 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7213 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7213 : Reach 7213 71155456345901 158444842066 := by
  have hr := row_7213
  have hl := log_bounds hr.1
    (by change logScale (7213 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7211) (T := 71066619943608) (U := 158422875499)
    (by norm_num) (by norm_num) hr.1 gap_7213
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7211

theorem gap_7219 : PrimeGap 7213 7219 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7219 :
    (7219 : ℕ).Prime ∧ logScale (7219 : ℚ) = 12 ∧
      (88844717150 : ℤ) = ⌊logCenter (7219 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7219 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7219 : Reach 7219 71244301063051 158466793416 := by
  have hr := row_7219
  have hl := log_bounds hr.1
    (by change logScale (7219 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7213) (T := 71155456345901) (U := 158444842066)
    (by norm_num) (by norm_num) hr.1 gap_7219
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7213

theorem gap_7229 : PrimeGap 7219 7229 :=
  (primeGap_of_factors (ds := [2, 3, 2, 31, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7229 :
    (7229 : ℕ).Prime ∧ logScale (7229 : ℚ) = 12 ∧
      (88858559898 : ℤ) = ⌊logCenter (7229 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7229 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7229 : Reach 7229 71333159622949 158488717433 := by
  have hr := row_7229
  have hl := log_bounds hr.1
    (by change logScale (7229 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7219) (T := 71244301063051) (U := 158466793416)
    (by norm_num) (by norm_num) hr.1 gap_7229
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7219

#print axioms reach_7229

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
