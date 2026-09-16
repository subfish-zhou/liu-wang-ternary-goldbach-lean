import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0530
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_12437 : PrimeGap 12433 12437 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12437 :
    (12437 : ℕ).Prime ∧ logScale (12437 : ℚ) = 13 ∧
      (94284311762 : ℤ) = ⌊logCenter (12437 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12437 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12437 : Reach 12437 122828157707178 168050871576 := by
  have hr := row_12437
  have hl := log_bounds hr.1
    (by change logScale (12437 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12433) (T := 122733873395416) (U := 168037359404)
    (by norm_num) (by norm_num) hr.1 gap_12437
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12433

theorem gap_12451 : PrimeGap 12437 12451 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 23, 2, 5, 2, 3, 2, 59, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12451 :
    (12451 : ℕ).Prime ∧ logScale (12451 : ℚ) = 13 ∧
      (94295562165 : ℤ) = ⌊logCenter (12451 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12451 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12451 : Reach 12451 122922453269343 168064369638 := by
  have hr := row_12451
  have hl := log_bounds hr.1
    (by change logScale (12451 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12437) (T := 122828157707178) (U := 168050871576)
    (by norm_num) (by norm_num) hr.1 gap_12451
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12437

theorem gap_12457 : PrimeGap 12451 12457 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12457 :
    (12457 : ℕ).Prime ∧ logScale (12457 : ℚ) = 13 ∧
      (94300379895 : ℤ) = ⌊logCenter (12457 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12457 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12457 : Reach 12457 123016753649238 168077862282 := by
  have hr := row_12457
  have hl := log_bounds hr.1
    (by change logScale (12457 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12451) (T := 122922453269343) (U := 168064369638)
    (by norm_num) (by norm_num) hr.1 gap_12457
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12451

theorem gap_12473 : PrimeGap 12457 12473 :=
  (primeGap_of_factors (ds := [2, 3, 2, 17, 2, 11, 2, 3, 2, 7, 2, 37, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12473 :
    (12473 : ℕ).Prime ∧ logScale (12473 : ℚ) = 13 ∧
      (94313215837 : ℤ) = ⌊logCenter (12473 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12473 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12473 : Reach 12473 123111066865075 168091338699 := by
  have hr := row_12473
  have hl := log_bounds hr.1
    (by change logScale (12473 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12457) (T := 123016753649238) (U := 168077862282)
    (by norm_num) (by norm_num) hr.1 gap_12473
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12457

theorem gap_12479 : PrimeGap 12473 12479 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12479 :
    (12479 : ℕ).Prime ∧ logScale (12479 : ℚ) = 13 ∧
      (94318025071 : ℤ) = ⌊logCenter (12479 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12479 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12479 : Reach 12479 123205384890146 168104809716 := by
  have hr := row_12479
  have hl := log_bounds hr.1
    (by change logScale (12479 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12473) (T := 123111066865075) (U := 168091338699)
    (by norm_num) (by norm_num) hr.1 gap_12479
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12473

theorem gap_12487 : PrimeGap 12479 12487 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12487 :
    (12487 : ℕ).Prime ∧ logScale (12487 : ℚ) = 13 ∧
      (94324433787 : ℤ) = ⌊logCenter (12487 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12487 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12487 : Reach 12487 123299709323933 168118273180 := by
  have hr := row_12487
  have hl := log_bounds hr.1
    (by change logScale (12487 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12479) (T := 123205384890146) (U := 168104809716)
    (by norm_num) (by norm_num) hr.1 gap_12487
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12479

theorem gap_12491 : PrimeGap 12487 12491 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12491 :
    (12491 : ℕ).Prime ∧ logScale (12491 : ℚ) = 13 ∧
      (94327636605 : ℤ) = ⌊logCenter (12491 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12491 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12491 : Reach 12491 123394036960538 168131733411 := by
  have hr := row_12491
  have hl := log_bounds hr.1
    (by change logScale (12491 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12487) (T := 123299709323933) (U := 168118273180)
    (by norm_num) (by norm_num) hr.1 gap_12491
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12487

theorem gap_12497 : PrimeGap 12491 12497 :=
  (primeGap_of_factors (ds := [2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_12497 :
    (12497 : ℕ).Prime ∧ logScale (12497 : ℚ) = 13 ∧
      (94332438911 : ℤ) = ⌊logCenter (12497 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (12497 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_12497 : Reach 12497 123488369399449 168145188256 := by
  have hr := row_12497
  have hl := log_bounds hr.1
    (by change logScale (12497 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 12491) (T := 123394036960538) (U := 168131733411)
    (by norm_num) (by norm_num) hr.1 gap_12497
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_12491

#print axioms reach_12497

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
