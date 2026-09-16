import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0651
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_15263 : PrimeGap 15259 15263 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15263 :
    (15263 : ℕ).Prime ∧ logScale (15263 : ℚ) = 13 ∧
      (96331868745 : ℤ) = ⌊logCenter (15263 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15263 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15263 : Reach 15263 151046661075045 171697997143 := by
  have hr := row_15263
  have hl := log_bounds hr.1
    (by change logScale (15263 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15259) (T := 150950329206300) (U := 171686747847)
    (by norm_num) (by norm_num) hr.1 gap_15263
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15259

theorem gap_15269 : PrimeGap 15263 15269 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15269 :
    (15269 : ℕ).Prime ∧ logScale (15269 : ℚ) = 13 ∧
      (96335799048 : ℤ) = ⌊logCenter (15269 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15269 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15269 : Reach 15269 151142996874093 171709242755 := by
  have hr := row_15269
  have hl := log_bounds hr.1
    (by change logScale (15269 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15263) (T := 151046661075045) (U := 171697997143)
    (by norm_num) (by norm_num) hr.1 gap_15269
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15263

theorem gap_15271 : PrimeGap 15269 15271 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_15271 :
    (15271 : ℕ).Prime ∧ logScale (15271 : ℚ) = 13 ∧
      (96337108805 : ℤ) = ⌊logCenter (15271 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15271 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15271 : Reach 15271 151239333982898 171720487631 := by
  have hr := row_15271
  have hl := log_bounds hr.1
    (by change logScale (15271 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15269) (T := 151142996874093) (U := 171709242755)
    (by norm_num) (by norm_num) hr.1 gap_15271
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15269

theorem gap_15277 : PrimeGap 15271 15277 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15277 :
    (15277 : ℕ).Prime ∧ logScale (15277 : ℚ) = 13 ∧
      (96341037049 : ℤ) = ⌊logCenter (15277 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15277 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15277 : Reach 15277 151335675019947 171731728826 := by
  have hr := row_15277
  have hl := log_bounds hr.1
    (by change logScale (15277 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15271) (T := 151239333982898) (U := 171720487631)
    (by norm_num) (by norm_num) hr.1 gap_15277
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15271

theorem gap_15287 : PrimeGap 15277 15287 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 17, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15287 :
    (15287 : ℕ).Prime ∧ logScale (15287 : ℚ) = 13 ∧
      (96347580696 : ℤ) = ⌊logCenter (15287 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15287 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15287 : Reach 15287 151432022600643 171742963403 := by
  have hr := row_15287
  have hl := log_bounds hr.1
    (by change logScale (15287 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15277) (T := 151335675019947) (U := 171731728826)
    (by norm_num) (by norm_num) hr.1 gap_15287
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15277

theorem gap_15289 : PrimeGap 15287 15289 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_15289 :
    (15289 : ℕ).Prime ∧ logScale (15289 : ℚ) = 13 ∧
      (96348888911 : ℤ) = ⌊logCenter (15289 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15289 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15289 : Reach 15289 151528371489554 171754197245 := by
  have hr := row_15289
  have hl := log_bounds hr.1
    (by change logScale (15289 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15287) (T := 151432022600643) (U := 171742963403)
    (by norm_num) (by norm_num) hr.1 gap_15289
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15287

theorem gap_15299 : PrimeGap 15289 15299 :=
  (primeGap_of_factors (ds := [2, 3, 2, 41, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15299 :
    (15299 : ℕ).Prime ∧ logScale (15299 : ℚ) = 13 ∧
      (96355427423 : ℤ) = ⌊logCenter (15299 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15299 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15299 : Reach 15299 151624726916977 171765424478 := by
  have hr := row_15299
  have hl := log_bounds hr.1
    (by change logScale (15299 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15289) (T := 151528371489554) (U := 171754197245)
    (by norm_num) (by norm_num) hr.1 gap_15299
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15289

theorem gap_15307 : PrimeGap 15299 15307 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15307 :
    (15307 : ℕ).Prime ∧ logScale (15307 : ℚ) = 13 ∧
      (96360655157 : ℤ) = ⌊logCenter (15307 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15307 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15307 : Reach 15307 151721087572134 171776646576 := by
  have hr := row_15307
  have hl := log_bounds hr.1
    (by change logScale (15307 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15299) (T := 151624726916977) (U := 171765424478)
    (by norm_num) (by norm_num) hr.1 gap_15307
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15299

#print axioms reach_15307

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
