import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block052
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_12377 : PrimeGap 12373 12377 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12377 :
    (12377 : ℕ).Prime ∧ logScale (12377 : ℚ) = 13 ∧
      (94235951871 : ℤ) = ⌊logCenter (12377 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12377 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12377 : Reach 12377 122074053944642 167942573684 := by
  have hr := row_12377
  have hl := log_bounds hr.1
    (by change logScale (12377 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12373) (T := 121979817992771) (U := 167929004759)
    (by norm_num) (by norm_num) hr.1 gap_12377
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12373

theorem gap_12379 : PrimeGap 12377 12379 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_12379 :
    (12379 : ℕ).Prime ∧ logScale (12379 : ℚ) = 13 ∧
      (94237567641 : ℤ) = ⌊logCenter (12379 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12379 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12379 : Reach 12379 122168291512283 167956141512 := by
  have hr := row_12379
  have hl := log_bounds hr.1
    (by change logScale (12379 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12377) (T := 122074053944642) (U := 167942573684)
    (by norm_num) (by norm_num) hr.1 gap_12379
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12377

theorem gap_12391 : PrimeGap 12379 12391 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12391 :
    (12391 : ℕ).Prime ∧ logScale (12391 : ℚ) = 13 ∧
      (94247256782 : ℤ) = ⌊logCenter (12391 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12391 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12391 : Reach 12391 122262538769065 167969697295 := by
  have hr := row_12391
  have hl := log_bounds hr.1
    (by change logScale (12391 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12379) (T := 122168291512283) (U := 167956141512)
    (by norm_num) (by norm_num) hr.1 gap_12391
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12379

theorem gap_12401 : PrimeGap 12391 12401 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12401 :
    (12401 : ℕ).Prime ∧ logScale (12401 : ℚ) = 13 ∧
      (94255323901 : ℤ) = ⌊logCenter (12401 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12401 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12401 : Reach 12401 122356794092966 167983243239 := by
  have hr := row_12401
  have hl := log_bounds hr.1
    (by change logScale (12401 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12391) (T := 122262538769065) (U := 167969697295)
    (by norm_num) (by norm_num) hr.1 gap_12401
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12391

theorem gap_12409 : PrimeGap 12401 12409 :=
  (primeGap_of_factors (ds := [2, 79, 2, 3, 2, 19, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12409 :
    (12409 : ℕ).Prime ∧ logScale (12409 : ℚ) = 13 ∧
      (94261772913 : ℤ) = ⌊logCenter (12409 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12409 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12409 : Reach 12409 122451055865879 167996781541 := by
  have hr := row_12409
  have hl := log_bounds hr.1
    (by change logScale (12409 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12401) (T := 122356794092966) (U := 167983243239)
    (by norm_num) (by norm_num) hr.1 gap_12409
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12401

theorem gap_12413 : PrimeGap 12409 12413 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12413 :
    (12413 : ℕ).Prime ∧ logScale (12413 : ℚ) = 13 ∧
      (94264995861 : ℤ) = ⌊logCenter (12413 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12413 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12413 : Reach 12413 122545320861740 168010316571 := by
  have hr := row_12413
  have hl := log_bounds hr.1
    (by change logScale (12413 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12409) (T := 122451055865879) (U := 167996781541)
    (by norm_num) (by norm_num) hr.1 gap_12413
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12409

theorem gap_12421 : PrimeGap 12413 12421 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12421 :
    (12421 : ℕ).Prime ∧ logScale (12421 : ℚ) = 13 ∧
      (94271438641 : ℤ) = ⌊logCenter (12421 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12421 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12421 : Reach 12421 122639592300381 168023843972 := by
  have hr := row_12421
  have hl := log_bounds hr.1
    (by change logScale (12421 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12413) (T := 122545320861740) (U := 168010316571)
    (by norm_num) (by norm_num) hr.1 gap_12421
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12413

theorem gap_12433 : PrimeGap 12421 12433 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 17, 2, 3, 2, 31, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12433 :
    (12433 : ℕ).Prime ∧ logScale (12433 : ℚ) = 13 ∧
      (94281095035 : ℤ) = ⌊logCenter (12433 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12433 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12433 : Reach 12433 122733873395416 168037359404 := by
  have hr := row_12433
  have hl := log_bounds hr.1
    (by change logScale (12433 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12421) (T := 122639592300381) (U := 168023843972)
    (by norm_num) (by norm_num) hr.1 gap_12433
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12421

#print axioms reach_12433

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
