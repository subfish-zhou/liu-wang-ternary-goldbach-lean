import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block029
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_7237 : PrimeGap 7229 7237 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7237 :
    (7237 : ℕ).Prime ∧ logScale (7237 : ℚ) = 12 ∧
      (88869620317 : ℤ) = ⌊logCenter (7237 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7237 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7237 : Reach 7237 71422029243266 158510620241 := by
  have hr := row_7237
  have hl := log_bounds hr.1
    (by change logScale (7237 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7229) (T := 71333159622949) (U := 158488717433)
    (by norm_num) (by norm_num) hr.1 gap_7237
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7229

theorem gap_7243 : PrimeGap 7237 7243 :=
  (primeGap_of_factors (ds := [2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7243 :
    (7243 : ℕ).Prime ∧ logScale (7243 : ℚ) = 12 ∧
      (88877907610 : ℤ) = ⌊logCenter (7243 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7243 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7243 : Reach 7243 71510907150876 158532507927 := by
  have hr := row_7243
  have hl := log_bounds hr.1
    (by change logScale (7243 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7237) (T := 71422029243266) (U := 158510620241)
    (by norm_num) (by norm_num) hr.1 gap_7243
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7237

theorem gap_7247 : PrimeGap 7243 7247 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7247 :
    (7247 : ℕ).Prime ∧ logScale (7247 : ℚ) = 12 ∧
      (88883428659 : ℤ) = ⌊logCenter (7247 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7247 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7247 : Reach 7247 71599790579535 158554386551 := by
  have hr := row_7247
  have hl := log_bounds hr.1
    (by change logScale (7247 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7243) (T := 71510907150876) (U := 158532507927)
    (by norm_num) (by norm_num) hr.1 gap_7247
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7243

theorem gap_7253 : PrimeGap 7247 7253 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7253 :
    (7253 : ℕ).Prime ∧ logScale (7253 : ℚ) = 12 ∧
      (88891704522 : ℤ) = ⌊logCenter (7253 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7253 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7253 : Reach 7253 71688682284057 158576250091 := by
  have hr := row_7253
  have hl := log_bounds hr.1
    (by change logScale (7253 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7247) (T := 71599790579535) (U := 158554386551)
    (by norm_num) (by norm_num) hr.1 gap_7253
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7247

theorem gap_7283 : PrimeGap 7253 7283 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 7, 2, 53, 2, 3, 2, 5, 2, 13, 2, 3, 2, 11, 2, 7, 2, 3, 2, 19, 2, 29, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7283 :
    (7283 : ℕ).Prime ∧ logScale (7283 : ℚ) = 12 ∧
      (88932981410 : ℤ) = ⌊logCenter (7283 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7283 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7283 : Reach 7283 71777615265467 158598026561 := by
  have hr := row_7283
  have hl := log_bounds hr.1
    (by change logScale (7283 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7253) (T := 71688682284057) (U := 158576250091)
    (by norm_num) (by norm_num) hr.1 gap_7283
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7253

theorem gap_7297 : PrimeGap 7283 7297 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 37, 2, 23, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7297 :
    (7297 : ℕ).Prime ∧ logScale (7297 : ℚ) = 12 ∧
      (88952185806 : ℤ) = ⌊logCenter (7297 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7297 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7297 : Reach 7297 71866567451273 158619764230 := by
  have hr := row_7297
  have hl := log_bounds hr.1
    (by change logScale (7297 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7283) (T := 71777615265467) (U := 158598026561)
    (by norm_num) (by norm_num) hr.1 gap_7297
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7283

theorem gap_7307 : PrimeGap 7297 7307 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 67, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7307 :
    (7307 : ℕ).Prime ∧ logScale (7307 : ℚ) = 12 ∧
      (88965880686 : ℤ) = ⌊logCenter (7307 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7307 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7307 : Reach 7307 71955533331959 158641475121 := by
  have hr := row_7307
  have hl := log_bounds hr.1
    (by change logScale (7307 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7297) (T := 71866567451273) (U := 158619764230)
    (by norm_num) (by norm_num) hr.1 gap_7307
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7297

theorem gap_7309 : PrimeGap 7307 7309 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_7309 :
    (7309 : ℕ).Prime ∧ logScale (7309 : ℚ) = 12 ∧
      (88968617413 : ℤ) = ⌊logCenter (7309 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7309 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7309 : Reach 7309 72044501949372 158663183041 := by
  have hr := row_7309
  have hl := log_bounds hr.1
    (by change logScale (7309 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7307) (T := 71955533331959) (U := 158641475121)
    (by norm_num) (by norm_num) hr.1 gap_7309
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7307

#print axioms reach_7309

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
