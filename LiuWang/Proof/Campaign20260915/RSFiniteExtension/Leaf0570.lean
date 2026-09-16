import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block056
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_13229 : PrimeGap 13219 13229 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13229 :
    (13229 : ℕ).Prime ∧ logScale (13229 : ℚ) = 13 ∧
      (94901666650 : ℤ) = ⌊logCenter (13229 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13229 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13229 : Reach 13229 131152401549609 169207917452 := by
  have hr := row_13229
  have hl := log_bounds hr.1
    (by change logScale (13229 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13219) (T := 131057499882959) (U := 169195126771)
    (by norm_num) (by norm_num) hr.1 gap_13229
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13219

theorem gap_13241 : PrimeGap 13229 13241 :=
  (primeGap_of_factors (ds := [2, 101, 2, 3, 2, 5, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13241 :
    (13241 : ℕ).Prime ∧ logScale (13241 : ℚ) = 13 ∧
      (94910733519 : ℤ) = ⌊logCenter (13241 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13241 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13241 : Reach 13241 131247312283128 169220697507 := by
  have hr := row_13241
  have hl := log_bounds hr.1
    (by change logScale (13241 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13229) (T := 131152401549609) (U := 169207917452)
    (by norm_num) (by norm_num) hr.1 gap_13241
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13229

theorem gap_13249 : PrimeGap 13241 13249 :=
  (primeGap_of_factors (ds := [2, 17, 2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13249 :
    (13249 : ℕ).Prime ∧ logScale (13249 : ℚ) = 13 ∧
      (94916773534 : ℤ) = ⌊logCenter (13249 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13249 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13249 : Reach 13249 131342229056662 169233470809 := by
  have hr := row_13249
  have hl := log_bounds hr.1
    (by change logScale (13249 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13241) (T := 131247312283128) (U := 169220697507)
    (by norm_num) (by norm_num) hr.1 gap_13249
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13241

theorem gap_13259 : PrimeGap 13249 13259 :=
  (primeGap_of_factors (ds := [2, 3, 2, 29, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13259 :
    (13259 : ℕ).Prime ∧ logScale (13259 : ℚ) = 13 ∧
      (94924318427 : ℤ) = ⌊logCenter (13259 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13259 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13259 : Reach 13259 131437153375089 169246235440 := by
  have hr := row_13259
  have hl := log_bounds hr.1
    (by change logScale (13259 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13249) (T := 131342229056662) (U := 169233470809)
    (by norm_num) (by norm_num) hr.1 gap_13259
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13249

theorem gap_13267 : PrimeGap 13259 13267 :=
  (primeGap_of_factors (ds := [2, 89, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13267 :
    (13267 : ℕ).Prime ∧ logScale (13267 : ℚ) = 13 ∧
      (94930350245 : ℤ) = ⌊logCenter (13267 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13267 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13267 : Reach 13267 131532083725334 169258993336 := by
  have hr := row_13267
  have hl := log_bounds hr.1
    (by change logScale (13267 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13259) (T := 131437153375089) (U := 169246235440)
    (by norm_num) (by norm_num) hr.1 gap_13267
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13259

theorem gap_13291 : PrimeGap 13267 13291 :=
  (primeGap_of_factors (ds := [2, 3, 2, 23, 2, 13, 2, 3, 2, 11, 2, 7, 2, 3, 2, 37, 2, 5, 2, 3, 2, 97, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13291 :
    (13291 : ℕ).Prime ∧ logScale (13291 : ℚ) = 13 ∧
      (94948423900 : ℤ) = ⌊logCenter (13291 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13291 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13291 : Reach 13291 131627032149234 169271729152 := by
  have hr := row_13291
  have hl := log_bounds hr.1
    (by change logScale (13291 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13267) (T := 131532083725334) (U := 169258993336)
    (by norm_num) (by norm_num) hr.1 gap_13291
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13267

theorem gap_13297 : PrimeGap 13291 13297 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13297 :
    (13297 : ℕ).Prime ∧ logScale (13297 : ℚ) = 13 ∧
      (94952937214 : ℤ) = ⌊logCenter (13297 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13297 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13297 : Reach 13297 131721985086448 169284460179 := by
  have hr := row_13297
  have hl := log_bounds hr.1
    (by change logScale (13297 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13291) (T := 131627032149234) (U := 169271729152)
    (by norm_num) (by norm_num) hr.1 gap_13297
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13291

theorem gap_13309 : PrimeGap 13297 13309 :=
  (primeGap_of_factors (ds := [2, 3, 2, 47, 2, 53, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13309 :
    (13309 : ℕ).Prime ∧ logScale (13309 : ℚ) = 13 ∧
      (94961957737 : ℤ) = ⌊logCenter (13309 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13309 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13309 : Reach 13309 131816947044185 169297180683 := by
  have hr := row_13309
  have hl := log_bounds hr.1
    (by change logScale (13309 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13297) (T := 131721985086448) (U := 169284460179)
    (by norm_num) (by norm_num) hr.1 gap_13309
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13297

#print axioms reach_13309

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
