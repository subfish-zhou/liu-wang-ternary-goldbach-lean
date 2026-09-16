import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0520
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_12227 : PrimeGap 12211 12227 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 19, 2, 3, 2, 11, 2, 17, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12227 :
    (12227 : ℕ).Prime ∧ logScale (12227 : ℚ) = 13 ∧
      (94114018967 : ℤ) = ⌊logCenter (12227 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12227 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12227 : Reach 12227 120567314042670 167724193298 := by
  have hr := row_12227
  have hl := log_bounds hr.1
    (by change logScale (12227 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12211) (T := 120473200023703) (U := 167710475771)
    (by norm_num) (by norm_num) hr.1 gap_12227
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12211

theorem gap_12239 : PrimeGap 12227 12239 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12239 :
    (12239 : ℕ).Prime ∧ logScale (12239 : ℚ) = 13 ∧
      (94123828500 : ℤ) = ⌊logCenter (12239 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12239 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12239 : Reach 12239 120661437871170 167737898495 := by
  have hr := row_12239
  have hl := log_bounds hr.1
    (by change logScale (12239 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12227) (T := 120567314042670) (U := 167724193298)
    (by norm_num) (by norm_num) hr.1 gap_12239
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12227

theorem gap_12241 : PrimeGap 12239 12241 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_12241 :
    (12241 : ℕ).Prime ∧ logScale (12241 : ℚ) = 13 ∧
      (94125462486 : ℤ) = ⌊logCenter (12241 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12241 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12241 : Reach 12241 120755563333656 167751602572 := by
  have hr := row_12241
  have hl := log_bounds hr.1
    (by change logScale (12241 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12239) (T := 120661437871170) (U := 167737898495)
    (by norm_num) (by norm_num) hr.1 gap_12241
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12239

theorem gap_12251 : PrimeGap 12241 12251 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 37, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12251 :
    (12251 : ℕ).Prime ∧ logScale (12251 : ℚ) = 13 ∧
      (94133628419 : ℤ) = ⌊logCenter (12251 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12251 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12251 : Reach 12251 120849696962075 167765296581 := by
  have hr := row_12251
  have hl := log_bounds hr.1
    (by change logScale (12251 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12241) (T := 120755563333656) (U := 167751602572)
    (by norm_num) (by norm_num) hr.1 gap_12251
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12241

theorem gap_12253 : PrimeGap 12251 12253 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_12253 :
    (12253 : ℕ).Prime ∧ logScale (12253 : ℚ) = 13 ∧
      (94135260805 : ℤ) = ⌊logCenter (12253 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12253 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12253 : Reach 12253 120943832222880 167778989472 := by
  have hr := row_12253
  have hl := log_bounds hr.1
    (by change logScale (12253 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12251) (T := 120849696962075) (U := 167765296581)
    (by norm_num) (by norm_num) hr.1 gap_12253
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12251

theorem gap_12263 : PrimeGap 12253 12263 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12263 :
    (12263 : ℕ).Prime ∧ logScale (12263 : ℚ) = 13 ∧
      (94143418743 : ℤ) = ⌊logCenter (12263 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12263 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12263 : Reach 12263 121037975641623 167792672313 := by
  have hr := row_12263
  have hl := log_bounds hr.1
    (by change logScale (12263 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12253) (T := 120943832222880) (U := 167778989472)
    (by norm_num) (by norm_num) hr.1 gap_12263
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12253

theorem gap_12269 : PrimeGap 12263 12269 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12269 :
    (12269 : ℕ).Prime ∧ logScale (12269 : ℚ) = 13 ∧
      (94148310314 : ℤ) = ⌊logCenter (12269 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12269 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12269 : Reach 12269 121132123951937 167806349577 := by
  have hr := row_12269
  have hl := log_bounds hr.1
    (by change logScale (12269 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12263) (T := 121037975641623) (U := 167792672313)
    (by norm_num) (by norm_num) hr.1 gap_12269
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12263

theorem gap_12277 : PrimeGap 12269 12277 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12277 :
    (12277 : ℕ).Prime ∧ logScale (12277 : ℚ) = 13 ∧
      (94154828688 : ℤ) = ⌊logCenter (12277 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12277 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12277 : Reach 12277 121226278780625 167820019042 := by
  have hr := row_12277
  have hl := log_bounds hr.1
    (by change logScale (12277 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12269) (T := 121132123951937) (U := 167806349577)
    (by norm_num) (by norm_num) hr.1 gap_12277
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12269

#print axioms reach_12277

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
