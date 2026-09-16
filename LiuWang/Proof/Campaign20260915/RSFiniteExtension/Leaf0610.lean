import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block060
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_14177 : PrimeGap 14173 14177 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14177 :
    (14177 : ℕ).Prime ∧ logScale (14177 : ℚ) = 13 ∧
      (95593762087 : ℤ) = ⌊logCenter (14177 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14177 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14177 : Reach 14177 140297001921323 170397474505 := by
  have hr := row_14177
  have hl := log_bounds hr.1
    (by change logScale (14177 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14173) (T := 140201408159236) (U := 170385455214)
    (by norm_num) (by norm_num) hr.1 gap_14177
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14173

theorem gap_14197 : PrimeGap 14177 14197 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 23, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14197 :
    (14197 : ℕ).Prime ∧ logScale (14197 : ℚ) = 13 ∧
      (95607859502 : ℤ) = ⌊logCenter (14197 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14197 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14197 : Reach 14197 140392609780825 170409477709 := by
  have hr := row_14197
  have hl := log_bounds hr.1
    (by change logScale (14197 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14177) (T := 140297001921323) (U := 170397474505)
    (by norm_num) (by norm_num) hr.1 gap_14197
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14177

theorem gap_14207 : PrimeGap 14197 14207 :=
  (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14207 :
    (14207 : ℕ).Prime ∧ logScale (14207 : ℚ) = 13 ∧
      (95614900764 : ℤ) = ⌊logCenter (14207 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14207 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14207 : Reach 14207 140488224681589 170421473308 := by
  have hr := row_14207
  have hl := log_bounds hr.1
    (by change logScale (14207 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14197) (T := 140392609780825) (U := 170409477709)
    (by norm_num) (by norm_num) hr.1 gap_14207
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14197

theorem gap_14221 : PrimeGap 14207 14221 :=
  (primeGap_of_factors (ds := [2, 13, 2, 3, 2, 61, 2, 5, 2, 3, 2, 59, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14221 :
    (14221 : ℕ).Prime ∧ logScale (14221 : ℚ) = 13 ∧
      (95624750209 : ℤ) = ⌊logCenter (14221 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14221 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14221 : Reach 14221 140583849431798 170433457941 := by
  have hr := row_14221
  have hl := log_bounds hr.1
    (by change logScale (14221 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14207) (T := 140488224681589) (U := 170421473308)
    (by norm_num) (by norm_num) hr.1 gap_14221
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14207

theorem gap_14243 : PrimeGap 14221 14243 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 41, 2, 3, 2, 7, 2, 43, 2, 3, 2, 23, 2, 29, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14243 :
    (14243 : ℕ).Prime ∧ logScale (14243 : ℚ) = 13 ∧
      (95640208335 : ℤ) = ⌊logCenter (14243 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14243 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14243 : Reach 14243 140679489640133 170445424902 := by
  have hr := row_14243
  have hl := log_bounds hr.1
    (by change logScale (14243 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14221) (T := 140583849431798) (U := 170433457941)
    (by norm_num) (by norm_num) hr.1 gap_14243
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14221

theorem gap_14249 : PrimeGap 14243 14249 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14249 :
    (14249 : ℕ).Prime ∧ logScale (14249 : ℚ) = 13 ∧
      (95644420044 : ℤ) = ⌊logCenter (14249 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14249 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14249 : Reach 14249 140775134060177 170457387664 := by
  have hr := row_14249
  have hl := log_bounds hr.1
    (by change logScale (14249 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14243) (T := 140679489640133) (U := 170445424902)
    (by norm_num) (by norm_num) hr.1 gap_14249
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14243

theorem gap_14251 : PrimeGap 14249 14251 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_14251 :
    (14251 : ℕ).Prime ∧ logScale (14251 : ℚ) = 13 ∧
      (95645823552 : ℤ) = ⌊logCenter (14251 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14251 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14251 : Reach 14251 140870779883729 170469349586 := by
  have hr := row_14251
  have hl := log_bounds hr.1
    (by change logScale (14251 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14249) (T := 140775134060177) (U := 170457387664)
    (by norm_num) (by norm_num) hr.1 gap_14251
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14249

theorem gap_14281 : PrimeGap 14251 14281 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 53, 2, 3, 2, 13, 2, 17, 2, 3, 2, 11, 2, 19, 2, 3, 2, 7, 2, 5, 2, 3, 2, 109, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14281 :
    (14281 : ℕ).Prime ∧ logScale (14281 : ℚ) = 13 ∧
      (95666852580 : ℤ) = ⌊logCenter (14281 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14281 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14281 : Reach 14281 140966446736309 170481287216 := by
  have hr := row_14281
  have hl := log_bounds hr.1
    (by change logScale (14281 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14251) (T := 140870779883729) (U := 170469349586)
    (by norm_num) (by norm_num) hr.1 gap_14281
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14251

#print axioms reach_14281

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
