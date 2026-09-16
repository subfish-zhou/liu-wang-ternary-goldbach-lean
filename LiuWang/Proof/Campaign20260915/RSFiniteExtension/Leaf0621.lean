import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0620
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_14533 : PrimeGap 14519 14533 :=
  (primeGap_of_factors (ds := [2, 13, 2, 3, 2, 5, 2, 73, 2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14533 :
    (14533 : ℕ).Prime ∧ logScale (14533 : ℚ) = 13 ∧
      (95841772012 : ℤ) = ⌊logCenter (14533 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14533 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14533 : Reach 14533 143360334994381 170777363435 := by
  have hr := row_14533
  have hl := log_bounds hr.1
    (by change logScale (14533 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14519) (T := 143264493222369) (U := 170765612429)
    (by norm_num) (by norm_num) hr.1 gap_14533
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14519

theorem gap_14537 : PrimeGap 14533 14537 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14537 :
    (14537 : ℕ).Prime ∧ logScale (14537 : ℚ) = 13 ∧
      (95844523990 : ℤ) = ⌊logCenter (14537 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14537 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14537 : Reach 14537 143456179518371 170789112016 := by
  have hr := row_14537
  have hl := log_bounds hr.1
    (by change logScale (14537 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14533) (T := 143360334994381) (U := 170777363435)
    (by norm_num) (by norm_num) hr.1 gap_14537
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14533

theorem gap_14543 : PrimeGap 14537 14543 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14543 :
    (14543 : ℕ).Prime ∧ logScale (14543 : ℚ) = 13 ∧
      (95848650537 : ℤ) = ⌊logCenter (14543 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14543 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14543 : Reach 14543 143552028168908 170800856557 := by
  have hr := row_14543
  have hl := log_bounds hr.1
    (by change logScale (14543 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14537) (T := 143456179518371) (U := 170789112016)
    (by norm_num) (by norm_num) hr.1 gap_14543
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14537

theorem gap_14549 : PrimeGap 14543 14549 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14549 :
    (14549 : ℕ).Prime ∧ logScale (14549 : ℚ) = 13 ∧
      (95852775383 : ℤ) = ⌊logCenter (14549 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14549 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14549 : Reach 14549 143647880944291 170812597062 := by
  have hr := row_14549
  have hl := log_bounds hr.1
    (by change logScale (14549 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14543) (T := 143552028168908) (U := 170800856557)
    (by norm_num) (by norm_num) hr.1 gap_14549
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14543

theorem gap_14551 : PrimeGap 14549 14551 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_14551 :
    (14551 : ℕ).Prime ∧ logScale (14551 : ℚ) = 13 ∧
      (95854149953 : ℤ) = ⌊logCenter (14551 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14551 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14551 : Reach 14551 143743735094244 170824336760 := by
  have hr := row_14551
  have hl := log_bounds hr.1
    (by change logScale (14551 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14549) (T := 143647880944291) (U := 170812597062)
    (by norm_num) (by norm_num) hr.1 gap_14551
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14549

theorem gap_14557 : PrimeGap 14551 14557 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14557 :
    (14557 : ℕ).Prime ∧ logScale (14557 : ℚ) = 13 ∧
      (95858272531 : ℤ) = ⌊logCenter (14557 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14557 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14557 : Reach 14557 143839593366775 170836072425 := by
  have hr := row_14557
  have hl := log_bounds hr.1
    (by change logScale (14557 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14551) (T := 143743735094244) (U := 170824336760)
    (by norm_num) (by norm_num) hr.1 gap_14557
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14551

theorem gap_14561 : PrimeGap 14557 14561 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14561 :
    (14561 : ℕ).Prime ∧ logScale (14561 : ℚ) = 13 ∧
      (95861019973 : ℤ) = ⌊logCenter (14561 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14561 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14561 : Reach 14561 143935454386748 170847805672 := by
  have hr := row_14561
  have hl := log_bounds hr.1
    (by change logScale (14561 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14557) (T := 143839593366775) (U := 170836072425)
    (by norm_num) (by norm_num) hr.1 gap_14561
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14557

theorem gap_14563 : PrimeGap 14561 14563 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_14563 :
    (14563 : ℕ).Prime ∧ logScale (14563 : ℚ) = 13 ∧
      (95862393411 : ℤ) = ⌊logCenter (14563 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14563 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14563 : Reach 14563 144031316780159 170859538113 := by
  have hr := row_14563
  have hl := log_bounds hr.1
    (by change logScale (14563 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14561) (T := 143935454386748) (U := 170847805672)
    (by norm_num) (by norm_num) hr.1 gap_14563
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14561

#print axioms reach_14563

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
