import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block038
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_9203 : PrimeGap 9199 9203 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9203 :
    (9203 : ℕ).Prime ∧ logScale (9203 : ℚ) = 13 ∧
      (91272847934 : ℤ) = ⌊logCenter (9203 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9203 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9203 : Reach 9203 90891625912746 162744212993 := by
  have hr := row_9203
  have hl := log_bounds hr.1
    (by change logScale (9203 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9199) (T := 90800353064812) (U := 162726529171)
    (by norm_num) (by norm_num) hr.1 gap_9203
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9199

theorem gap_9209 : PrimeGap 9203 9209 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9209 :
    (9209 : ℕ).Prime ∧ logScale (9209 : ℚ) = 13 ∧
      (91279365423 : ℤ) = ⌊logCenter (9209 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9209 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9209 : Reach 9209 90982905278169 162761887213 := by
  have hr := row_9209
  have hl := log_bounds hr.1
    (by change logScale (9209 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9203) (T := 90891625912746) (U := 162744212993)
    (by norm_num) (by norm_num) hr.1 gap_9209
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9203

theorem gap_9221 : PrimeGap 9209 9221 :=
  (primeGap_of_factors (ds := [2, 61, 2, 3, 2, 5, 2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9221 :
    (9221 : ℕ).Prime ∧ logScale (9221 : ℚ) = 13 ∧
      (91292387671 : ℤ) = ⌊logCenter (9221 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9221 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9221 : Reach 9221 91074197665840 162779540347 := by
  have hr := row_9221
  have hl := log_bounds hr.1
    (by change logScale (9221 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9209) (T := 90982905278169) (U := 162761887213)
    (by norm_num) (by norm_num) hr.1 gap_9221
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9209

theorem gap_9227 : PrimeGap 9221 9227 :=
  (primeGap_of_factors (ds := [2, 23, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9227 :
    (9227 : ℕ).Prime ∧ logScale (9227 : ℚ) = 13 ∧
      (91298892441 : ℤ) = ⌊logCenter (9227 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9227 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9227 : Reach 9227 91165496558281 162797183914 := by
  have hr := row_9227
  have hl := log_bounds hr.1
    (by change logScale (9227 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9221) (T := 91074197665840) (U := 162779540347)
    (by norm_num) (by norm_num) hr.1 gap_9227
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9221

theorem gap_9239 : PrimeGap 9227 9239 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9239 :
    (9239 : ℕ).Prime ∧ logScale (9239 : ℚ) = 13 ∧
      (91311889302 : ℤ) = ⌊logCenter (9239 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9239 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9239 : Reach 9239 91256808447583 162814806472 := by
  have hr := row_9239
  have hl := log_bounds hr.1
    (by change logScale (9239 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9227) (T := 91165496558281) (U := 162797183914)
    (by norm_num) (by norm_num) hr.1 gap_9239
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9227

theorem gap_9241 : PrimeGap 9239 9241 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_9241 :
    (9241 : ℕ).Prime ∧ logScale (9241 : ℚ) = 13 ∧
      (91314053805 : ℤ) = ⌊logCenter (9241 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9241 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9241 : Reach 9241 91348122501388 162832427123 := by
  have hr := row_9241
  have hl := log_bounds hr.1
    (by change logScale (9241 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9239) (T := 91256808447583) (U := 162814806472)
    (by norm_num) (by norm_num) hr.1 gap_9241
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9239

theorem gap_9257 : PrimeGap 9241 9257 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 19, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9257 :
    (9257 : ℕ).Prime ∧ logScale (9257 : ℚ) = 13 ∧
      (91331352976 : ℤ) = ⌊logCenter (9257 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9257 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9257 : Reach 9257 91439453854364 162850019218 := by
  have hr := row_9257
  have hl := log_bounds hr.1
    (by change logScale (9257 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9241) (T := 91348122501388) (U := 162832427123)
    (by norm_num) (by norm_num) hr.1 gap_9257
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9241

theorem gap_9277 : PrimeGap 9257 9277 :=
  (primeGap_of_factors (ds := [2, 47, 2, 3, 2, 59, 2, 5, 2, 3, 2, 13, 2, 73, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9277 :
    (9277 : ℕ).Prime ∧ logScale (9277 : ℚ) = 13 ∧
      (91352934942 : ℤ) = ⌊logCenter (9277 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9277 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9277 : Reach 9277 91530806789306 162867575279 := by
  have hr := row_9277
  have hl := log_bounds hr.1
    (by change logScale (9277 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9257) (T := 91439453854364) (U := 162850019218)
    (by norm_num) (by norm_num) hr.1 gap_9277
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9257

#print axioms reach_9277

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
