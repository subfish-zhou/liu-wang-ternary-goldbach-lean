import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0431
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_10211 : PrimeGap 10193 10211 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 7, 2, 101, 2, 3, 2, 5, 2, 59, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10211 :
    (10211 : ℕ).Prime ∧ logScale (10211 : ℚ) = 13 ∧
      (92312208461 : ℤ) = ⌊logCenter (10211 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10211 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10211 : Reach 10211 101173058745190 164635223231 := by
  have hr := row_10211
  have hl := log_bounds hr.1
    (by change logScale (10211 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10193) (T := 101080746536729) (U := 164619099910)
    (by norm_num) (by norm_num) hr.1 gap_10211
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10193

theorem gap_10223 : PrimeGap 10211 10223 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 17, 2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10223 :
    (10223 : ℕ).Prime ∧ logScale (10223 : ℚ) = 13 ∧
      (92323953593 : ℤ) = ⌊logCenter (10223 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10223 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10223 : Reach 10223 101265382698783 164651329201 := by
  have hr := row_10223
  have hl := log_bounds hr.1
    (by change logScale (10223 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10211) (T := 101173058745190) (U := 164635223231)
    (by norm_num) (by norm_num) hr.1 gap_10223
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10211

theorem gap_10243 : PrimeGap 10223 10243 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 53, 2, 13, 2, 3, 2, 5, 2, 29, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10243 :
    (10243 : ℕ).Prime ∧ logScale (10243 : ℚ) = 13 ∧
      (92343498210 : ℤ) = ⌊logCenter (10243 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10243 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10243 : Reach 10243 101357726196993 164667405293 := by
  have hr := row_10243
  have hl := log_bounds hr.1
    (by change logScale (10243 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10223) (T := 101265382698783) (U := 164651329201)
    (by norm_num) (by norm_num) hr.1 gap_10243
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10223

theorem gap_10247 : PrimeGap 10243 10247 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10247 :
    (10247 : ℕ).Prime ∧ logScale (10247 : ℚ) = 13 ∧
      (92347402554 : ℤ) = ⌊logCenter (10247 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10247 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10247 : Reach 10247 101450073599547 164683476678 := by
  have hr := row_10247
  have hl := log_bounds hr.1
    (by change logScale (10247 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10243) (T := 101357726196993) (U := 164667405293)
    (by norm_num) (by norm_num) hr.1 gap_10247
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10243

theorem gap_10253 : PrimeGap 10247 10253 :=
  (primeGap_of_factors (ds := [2, 37, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10253 :
    (10253 : ℕ).Prime ∧ logScale (10253 : ℚ) = 13 ∧
      (92353256212 : ℤ) = ⌊logCenter (10253 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10253 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10253 : Reach 10253 101542426855759 164699540225 := by
  have hr := row_10253
  have hl := log_bounds hr.1
    (by change logScale (10253 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10247) (T := 101450073599547) (U := 164683476678)
    (by norm_num) (by norm_num) hr.1 gap_10253
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10247

theorem gap_10259 : PrimeGap 10253 10259 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10259 :
    (10259 : ℕ).Prime ∧ logScale (10259 : ℚ) = 13 ∧
      (92359106447 : ℤ) = ⌊logCenter (10259 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10259 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10259 : Reach 10259 101634785962206 164715595942 := by
  have hr := row_10259
  have hl := log_bounds hr.1
    (by change logScale (10259 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10253) (T := 101542426855759) (U := 164699540225)
    (by norm_num) (by norm_num) hr.1 gap_10259
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10253

theorem gap_10267 : PrimeGap 10259 10267 :=
  (primeGap_of_factors (ds := [2, 31, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10267 :
    (10267 : ℕ).Prime ∧ logScale (10267 : ℚ) = 13 ∧
      (92366901439 : ℤ) = ⌊logCenter (10267 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10267 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10267 : Reach 10267 101727152863645 164731640711 := by
  have hr := row_10267
  have hl := log_bounds hr.1
    (by change logScale (10267 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10259) (T := 101634785962206) (U := 164715595942)
    (by norm_num) (by norm_num) hr.1 gap_10267
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10259

theorem gap_10271 : PrimeGap 10267 10271 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10271 :
    (10271 : ℕ).Prime ∧ logScale (10271 : ℚ) = 13 ∧
      (92370796657 : ℤ) = ⌊logCenter (10271 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10271 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10271 : Reach 10271 101819523660302 164747680793 := by
  have hr := row_10271
  have hl := log_bounds hr.1
    (by change logScale (10271 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10267) (T := 101727152863645) (U := 164731640711)
    (by norm_num) (by norm_num) hr.1 gap_10271
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10267

#print axioms reach_10271

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
