import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block051
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_12143 : PrimeGap 12119 12143 :=
  (primeGap_of_factors (ds := [2, 17, 2, 3, 2, 5, 2, 67, 2, 3, 2, 7, 2, 11, 2, 3, 2, 53, 2, 61, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12143 :
    (12143 : ℕ).Prime ∧ logScale (12143 : ℚ) = 13 ∧
      (94045081476 : ℤ) = ⌊logCenter (12143 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12143 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12143 : Reach 12143 119814687217495 167614092342 := by
  have hr := row_12143
  have hl := log_bounds hr.1
    (by change logScale (12143 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12119) (T := 119720642136019) (U := 167600288990)
    (by norm_num) (by norm_num) hr.1 gap_12143
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12119

theorem gap_12149 : PrimeGap 12143 12149 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12149 :
    (12149 : ℕ).Prime ∧ logScale (12149 : ℚ) = 13 ∧
      (94050021374 : ℤ) = ⌊logCenter (12149 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12149 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12149 : Reach 12149 119908737238869 167627890012 := by
  have hr := row_12149
  have hl := log_bounds hr.1
    (by change logScale (12149 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12143) (T := 119814687217495) (U := 167614092342)
    (by norm_num) (by norm_num) hr.1 gap_12149
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12143

theorem gap_12157 : PrimeGap 12149 12157 :=
  (primeGap_of_factors (ds := [2, 29, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12157 :
    (12157 : ℕ).Prime ∧ logScale (12157 : ℚ) = 13 ∧
      (94056604111 : ℤ) = ⌊logCenter (12157 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12157 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12157 : Reach 12157 120002793842980 167641679737 := by
  have hr := row_12157
  have hl := log_bounds hr.1
    (by change logScale (12157 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12149) (T := 119908737238869) (U := 167627890012)
    (by norm_num) (by norm_num) hr.1 gap_12157
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12149

theorem gap_12161 : PrimeGap 12157 12161 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12161 :
    (12161 : ℕ).Prime ∧ logScale (12161 : ℚ) = 13 ∧
      (94059893856 : ℤ) = ⌊logCenter (12161 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12161 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12161 : Reach 12161 120096853736836 167655466060 := by
  have hr := row_12161
  have hl := log_bounds hr.1
    (by change logScale (12161 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12157) (T := 120002793842980) (U := 167641679737)
    (by norm_num) (by norm_num) hr.1 gap_12161
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12157

theorem gap_12163 : PrimeGap 12161 12163 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_12163 :
    (12163 : ℕ).Prime ∧ logScale (12163 : ℚ) = 13 ∧
      (94061538322 : ℤ) = ⌊logCenter (12163 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12163 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12163 : Reach 12163 120190915275158 167669251249 := by
  have hr := row_12163
  have hl := log_bounds hr.1
    (by change logScale (12163 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12161) (T := 120096853736836) (U := 167655466060)
    (by norm_num) (by norm_num) hr.1 gap_12163
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12161

theorem gap_12197 : PrimeGap 12163 12197 :=
  (primeGap_of_factors (ds := [2, 3, 2, 23, 2, 43, 2, 3, 2, 7, 2, 5, 2, 3, 2, 19, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 73, 2, 89, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12197 :
    (12197 : ℕ).Prime ∧ logScale (12197 : ℚ) = 13 ∧
      (94089452954 : ℤ) = ⌊logCenter (12197 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12197 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12197 : Reach 12197 120285004728112 167682999138 := by
  have hr := row_12197
  have hl := log_bounds hr.1
    (by change logScale (12197 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12163) (T := 120190915275158) (U := 167669251249)
    (by norm_num) (by norm_num) hr.1 gap_12197
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12163

theorem gap_12203 : PrimeGap 12197 12203 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12203 :
    (12203 : ℕ).Prime ∧ logScale (12203 : ℚ) = 13 ∧
      (94094370987 : ℤ) = ⌊logCenter (12203 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12203 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12203 : Reach 12203 120379099099099 167696741394 := by
  have hr := row_12203
  have hl := log_bounds hr.1
    (by change logScale (12203 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12197) (T := 120285004728112) (U := 167682999138)
    (by norm_num) (by norm_num) hr.1 gap_12203
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12197

theorem gap_12211 : PrimeGap 12203 12211 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 29, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12211 :
    (12211 : ℕ).Prime ∧ logScale (12211 : ℚ) = 13 ∧
      (94100924604 : ℤ) = ⌊logCenter (12211 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12211 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12211 : Reach 12211 120473200023703 167710475771 := by
  have hr := row_12211
  have hl := log_bounds hr.1
    (by change logScale (12211 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12203) (T := 120379099099099) (U := 167696741394)
    (by norm_num) (by norm_num) hr.1 gap_12211
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12203

#print axioms reach_12211

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
