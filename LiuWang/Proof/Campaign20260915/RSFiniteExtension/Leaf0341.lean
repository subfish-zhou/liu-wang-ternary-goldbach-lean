import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0340
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_8209 : PrimeGap 8191 8209 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 7, 2, 3, 2, 59, 2, 13, 2, 3, 2, 29, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8209 :
    (8209 : ℕ).Prime ∧ logScale (8209 : ℚ) = 13 ∧
      (90129863889 : ℤ) = ⌊logCenter (8209 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8209 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8209 : Reach 8209 80731518055529 160662207319 := by
  have hr := row_8209
  have hl := log_bounds hr.1
    (by change logScale (8209 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8191) (T := 80641388191640) (U := 160642635847)
    (by norm_num) (by norm_num) hr.1 gap_8209
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8191

theorem gap_8219 : PrimeGap 8209 8219 :=
  (primeGap_of_factors (ds := [2, 3, 2, 43, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8219 :
    (8219 : ℕ).Prime ∧ logScale (8219 : ℚ) = 13 ∧
      (90142038227 : ℤ) = ⌊logCenter (8219 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8219 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8219 : Reach 8219 80821660093756 160681757357 := by
  have hr := row_8219
  have hl := log_bounds hr.1
    (by change logScale (8219 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8209) (T := 80731518055529) (U := 160662207319)
    (by norm_num) (by norm_num) hr.1 gap_8219
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8209

theorem gap_8221 : PrimeGap 8219 8221 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_8221 :
    (8221 : ℕ).Prime ∧ logScale (8221 : ℚ) = 13 ∧
      (90144471317 : ℤ) = ⌊logCenter (8221 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8221 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8221 : Reach 8221 80911804565073 160701305017 := by
  have hr := row_8221
  have hl := log_bounds hr.1
    (by change logScale (8221 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8219) (T := 80821660093756) (U := 160681757357)
    (by norm_num) (by norm_num) hr.1 gap_8221
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8219

theorem gap_8231 : PrimeGap 8221 8231 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 19, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8231 :
    (8231 : ℕ).Prime ∧ logScale (8231 : ℚ) = 13 ∧
      (90156627895 : ℤ) = ⌊logCenter (8231 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8231 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8231 : Reach 8231 81001961192968 160720831300 := by
  have hr := row_8231
  have hl := log_bounds hr.1
    (by change logScale (8231 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8221) (T := 80911804565073) (U := 160701305017)
    (by norm_num) (by norm_num) hr.1 gap_8231
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8221

theorem gap_8233 : PrimeGap 8231 8233 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_8233 :
    (8233 : ℕ).Prime ∧ logScale (8233 : ℚ) = 13 ∧
      (90159057439 : ℤ) = ⌊logCenter (8233 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8233 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8233 : Reach 8233 81092120250407 160740355211 := by
  have hr := row_8233
  have hl := log_bounds hr.1
    (by change logScale (8233 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8231) (T := 81001961192968) (U := 160720831300)
    (by norm_num) (by norm_num) hr.1 gap_8233
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8231

theorem gap_8237 : PrimeGap 8233 8237 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8237 :
    (8237 : ℕ).Prime ∧ logScale (8237 : ℚ) = 13 ∧
      (90163914755 : ℤ) = ⌊logCenter (8237 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8237 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8237 : Reach 8237 81182284165162 160759872010 := by
  have hr := row_8237
  have hl := log_bounds hr.1
    (by change logScale (8237 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8233) (T := 81092120250407) (U := 160740355211)
    (by norm_num) (by norm_num) hr.1 gap_8237
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8233

theorem gap_8243 : PrimeGap 8237 8243 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8243 :
    (8243 : ℕ).Prime ∧ logScale (8243 : ℚ) = 13 ∧
      (90171196309 : ℤ) = ⌊logCenter (8243 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8243 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8243 : Reach 8243 81272455361471 160779376969 := by
  have hr := row_8243
  have hl := log_bounds hr.1
    (by change logScale (8243 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8237) (T := 81182284165162) (U := 160759872010)
    (by norm_num) (by norm_num) hr.1 gap_8243
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8237

theorem gap_8263 : PrimeGap 8243 8263 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 73, 2, 37, 2, 3, 2, 5, 2, 23, 2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8263 :
    (8263 : ℕ).Prime ∧ logScale (8263 : ℚ) = 13 ∧
      (90195429933 : ℤ) = ⌊logCenter (8263 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8263 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8263 : Reach 8263 81362650791404 160798837073 := by
  have hr := row_8263
  have hl := log_bounds hr.1
    (by change logScale (8263 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8243) (T := 81272455361471) (U := 160779376969)
    (by norm_num) (by norm_num) hr.1 gap_8263
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8243

#print axioms reach_8263

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
