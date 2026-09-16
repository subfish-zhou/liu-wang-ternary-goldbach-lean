import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0360
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_8647 : PrimeGap 8641 8647 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8647 :
    (8647 : ℕ).Prime ∧ logScale (8647 : ℚ) = 13 ∧
      (90649677155 : ℤ) = ⌊logCenter (8647 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8647 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8647 : Reach 8647 85070206460659 161580360800 := by
  have hr := row_8647
  have hl := log_bounds hr.1
    (by change logScale (8647 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8641) (T := 84979556783504) (U := 161561674508)
    (by norm_num) (by norm_num) hr.1 gap_8647
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8641

theorem gap_8663 : PrimeGap 8647 8663 :=
  (primeGap_of_factors (ds := [2, 3, 2, 41, 2, 17, 2, 3, 2, 11, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8663 :
    (8663 : ℕ).Prime ∧ logScale (8663 : ℚ) = 13 ∧
      (90668163585 : ℤ) = ⌊logCenter (8663 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8663 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8663 : Reach 8663 85160874624244 161599014733 := by
  have hr := row_8663
  have hl := log_bounds hr.1
    (by change logScale (8663 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8647) (T := 85070206460659) (U := 161580360800)
    (by norm_num) (by norm_num) hr.1 gap_8663
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8647

theorem gap_8669 : PrimeGap 8663 8669 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8669 :
    (8669 : ℕ).Prime ∧ logScale (8669 : ℚ) = 13 ∧
      (90675087194 : ℤ) = ⌊logCenter (8669 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8669 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8669 : Reach 8669 85251549711438 161617657905 := by
  have hr := row_8669
  have hl := log_bounds hr.1
    (by change logScale (8669 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8663) (T := 85160874624244) (U := 161599014733)
    (by norm_num) (by norm_num) hr.1 gap_8669
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8663

theorem gap_8677 : PrimeGap 8669 8677 :=
  (primeGap_of_factors (ds := [2, 13, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8677 :
    (8677 : ℕ).Prime ∧ logScale (8677 : ℚ) = 13 ∧
      (90684311224 : ℤ) = ⌊logCenter (8677 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8677 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8677 : Reach 8677 85342234022662 161636286036 := by
  have hr := row_8677
  have hl := log_bounds hr.1
    (by change logScale (8677 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8669) (T := 85251549711438) (U := 161617657905)
    (by norm_num) (by norm_num) hr.1 gap_8677
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8669

theorem gap_8681 : PrimeGap 8677 8681 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8681 :
    (8681 : ℕ).Prime ∧ logScale (8681 : ℚ) = 13 ∧
      (90688920050 : ℤ) = ⌊logCenter (8681 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8681 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8681 : Reach 8681 85432922942712 161654907728 := by
  have hr := row_8681
  have hl := log_bounds hr.1
    (by change logScale (8681 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8677) (T := 85342234022662) (U := 161636286036)
    (by norm_num) (by norm_num) hr.1 gap_8681
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8677

theorem gap_8689 : PrimeGap 8681 8689 :=
  (primeGap_of_factors (ds := [2, 19, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8689 :
    (8689 : ℕ).Prime ∧ logScale (8689 : ℚ) = 13 ∧
      (90698131334 : ℤ) = ⌊logCenter (8689 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8689 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8689 : Reach 8689 85523621074046 161673514417 := by
  have hr := row_8689
  have hl := log_bounds hr.1
    (by change logScale (8689 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8681) (T := 85432922942712) (U := 161654907728)
    (by norm_num) (by norm_num) hr.1 gap_8689
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8681

theorem gap_8693 : PrimeGap 8689 8693 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8693 :
    (8693 : ℕ).Prime ∧ logScale (8693 : ℚ) = 13 ∧
      (90702733796 : ℤ) = ⌊logCenter (8693 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8693 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8693 : Reach 8693 85614323807842 161692114684 := by
  have hr := row_8693
  have hl := log_bounds hr.1
    (by change logScale (8693 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8689) (T := 85523621074046) (U := 161673514417)
    (by norm_num) (by norm_num) hr.1 gap_8693
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8689

theorem gap_8699 : PrimeGap 8693 8699 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8699 :
    (8699 : ℕ).Prime ∧ logScale (8699 : ℚ) = 13 ∧
      (90709633521 : ℤ) = ⌊logCenter (8699 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8699 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8699 : Reach 8699 85705033441363 161710704259 := by
  have hr := row_8699
  have hl := log_bounds hr.1
    (by change logScale (8699 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 8693) (T := 85614323807842) (U := 161692114684)
    (by norm_num) (by norm_num) hr.1 gap_8699
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8693

#print axioms reach_8699

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
