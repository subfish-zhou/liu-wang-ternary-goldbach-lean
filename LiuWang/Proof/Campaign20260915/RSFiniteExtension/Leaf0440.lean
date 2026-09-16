import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block043
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_10273 : PrimeGap 10271 10273 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_10273 :
    (10273 : ℕ).Prime ∧ logScale (10273 : ℚ) = 13 ∧
      (92372743698 : ℤ) = ⌊logCenter (10273 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10273 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10273 : Reach 10273 101911896404000 164763719314 := by
  have hr := row_10273
  have hl := log_bounds hr.1
    (by change logScale (10273 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10271) (T := 101819523660302) (U := 164747680793)
    (by norm_num) (by norm_num) hr.1 gap_10273
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10271

theorem gap_10289 : PrimeGap 10273 10289 :=
  (primeGap_of_factors (ds := [2, 3, 2, 43, 2, 19, 2, 3, 2, 7, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10289 :
    (10289 : ℕ).Prime ∧ logScale (10289 : ℚ) = 13 ∧
      (92388306389 : ℤ) = ⌊logCenter (10289 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10289 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10289 : Reach 10289 102004284710389 164779734451 := by
  have hr := row_10289
  have hl := log_bounds hr.1
    (by change logScale (10289 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10273) (T := 101911896404000) (U := 164763719314)
    (by norm_num) (by norm_num) hr.1 gap_10289
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10273

theorem gap_10301 : PrimeGap 10289 10301 :=
  (primeGap_of_factors (ds := [2, 41, 2, 3, 2, 5, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10301 :
    (10301 : ℕ).Prime ∧ logScale (10301 : ℚ) = 13 ∧
      (92399962535 : ℤ) = ⌊logCenter (10301 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10301 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10301 : Reach 10301 102096684672924 164795732484 := by
  have hr := row_10301
  have hl := log_bounds hr.1
    (by change logScale (10301 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10289) (T := 102004284710389) (U := 164779734451)
    (by norm_num) (by norm_num) hr.1 gap_10301
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10289

theorem gap_10303 : PrimeGap 10301 10303 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_10303 :
    (10303 : ℕ).Prime ∧ logScale (10303 : ℚ) = 13 ∧
      (92401903905 : ℤ) = ⌊logCenter (10303 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10303 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10303 : Reach 10303 102189086576829 164811728964 := by
  have hr := row_10303
  have hl := log_bounds hr.1
    (by change logScale (10303 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10301) (T := 102096684672924) (U := 164795732484)
    (by norm_num) (by norm_num) hr.1 gap_10303
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10301

theorem gap_10313 : PrimeGap 10303 10313 :=
  (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10313 :
    (10313 : ℕ).Prime ∧ logScale (10313 : ℚ) = 13 ∧
      (92411605109 : ℤ) = ⌊logCenter (10313 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10313 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10313 : Reach 10313 102281498181938 164827711483 := by
  have hr := row_10313
  have hl := log_bounds hr.1
    (by change logScale (10313 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10303) (T := 102189086576829) (U := 164811728964)
    (by norm_num) (by norm_num) hr.1 gap_10313
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10303

theorem gap_10321 : PrimeGap 10313 10321 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 17, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10321 :
    (10321 : ℕ).Prime ∧ logScale (10321 : ℚ) = 13 ∧
      (92419359301 : ℤ) = ⌊logCenter (10321 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10321 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10321 : Reach 10321 102373917541239 164843683161 := by
  have hr := row_10321
  have hl := log_bounds hr.1
    (by change logScale (10321 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10313) (T := 102281498181938) (U := 164827711483)
    (by norm_num) (by norm_num) hr.1 gap_10321
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10313

theorem gap_10331 : PrimeGap 10321 10331 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 23, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10331 :
    (10331 : ℕ).Prime ∧ logScale (10331 : ℚ) = 13 ∧
      (92429043594 : ℤ) = ⌊logCenter (10331 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10331 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10331 : Reach 10331 102466346584833 164859640924 := by
  have hr := row_10331
  have hl := log_bounds hr.1
    (by change logScale (10331 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10321) (T := 102373917541239) (U := 164843683161)
    (by norm_num) (by norm_num) hr.1 gap_10331
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10321

theorem gap_10333 : PrimeGap 10331 10333 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_10333 :
    (10333 : ℕ).Prime ∧ logScale (10333 : ℚ) = 13 ∧
      (92430979328 : ℤ) = ⌊logCenter (10333 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10333 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10333 : Reach 10333 102558777564161 164875597142 := by
  have hr := row_10333
  have hl := log_bounds hr.1
    (by change logScale (10333 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10331) (T := 102466346584833) (U := 164859640924)
    (by norm_num) (by norm_num) hr.1 gap_10333
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10331

#print axioms reach_10333

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
