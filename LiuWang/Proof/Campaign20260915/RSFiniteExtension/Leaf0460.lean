import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block045
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_10733 : PrimeGap 10729 10733 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10733 :
    (10733 : ℕ).Prime ∧ logScale (10733 : ℚ) = 13 ∧
      (92810783831 : ℤ) = ⌊logCenter (10733 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10733 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10733 : Reach 10733 106356900632688 165517770225 := by
  have hr := row_10733
  have hl := log_bounds hr.1
    (by change logScale (10733 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10729) (T := 106264089848857) (U := 165502348835)
    (by norm_num) (by norm_num) hr.1 gap_10733
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10729

theorem gap_10739 : PrimeGap 10733 10739 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10739 :
    (10739 : ℕ).Prime ∧ logScale (10739 : ℚ) = 13 ∧
      (92816372504 : ℤ) = ⌊logCenter (10739 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10739 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10739 : Reach 10739 106449717005192 165533184434 := by
  have hr := row_10739
  have hl := log_bounds hr.1
    (by change logScale (10739 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10733) (T := 106356900632688) (U := 165517770225)
    (by norm_num) (by norm_num) hr.1 gap_10739
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10733

theorem gap_10753 : PrimeGap 10739 10753 :=
  (primeGap_of_factors (ds := [2, 23, 2, 3, 2, 5, 2, 11, 2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10753 :
    (10753 : ℕ).Prime ∧ logScale (10753 : ℚ) = 13 ∧
      (92829400610 : ℤ) = ⌊logCenter (10753 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10753 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10753 : Reach 10753 106542546405802 165548580006 := by
  have hr := row_10753
  have hl := log_bounds hr.1
    (by change logScale (10753 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10739) (T := 106449717005192) (U := 165533184434)
    (by norm_num) (by norm_num) hr.1 gap_10753
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10739

theorem gap_10771 : PrimeGap 10753 10771 :=
  (primeGap_of_factors (ds := [2, 3, 2, 31, 2, 7, 2, 3, 2, 47, 2, 5, 2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10771 :
    (10771 : ℕ).Prime ∧ logScale (10771 : ℚ) = 13 ∧
      (92846126129 : ℤ) = ⌊logCenter (10771 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10771 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10771 : Reach 10771 106635392531931 165563951277 := by
  have hr := row_10771
  have hl := log_bounds hr.1
    (by change logScale (10771 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10753) (T := 106542546405802) (U := 165548580006)
    (by norm_num) (by norm_num) hr.1 gap_10771
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10753

theorem gap_10781 : PrimeGap 10771 10781 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10781 :
    (10781 : ℕ).Prime ∧ logScale (10781 : ℚ) = 13 ∧
      (92855406011 : ℤ) = ⌊logCenter (10781 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10781 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10781 : Reach 10781 106728247937942 165579309715 := by
  have hr := row_10781
  have hl := log_bounds hr.1
    (by change logScale (10781 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10771) (T := 106635392531931) (U := 165563951277)
    (by norm_num) (by norm_num) hr.1 gap_10781
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10771

theorem gap_10789 : PrimeGap 10781 10789 :=
  (primeGap_of_factors (ds := [2, 41, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10789 :
    (10789 : ℕ).Prime ∧ logScale (10789 : ℚ) = 13 ∧
      (92862823721 : ℤ) = ⌊logCenter (10789 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10789 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10789 : Reach 10789 106821110761663 165594658187 := by
  have hr := row_10789
  have hl := log_bounds hr.1
    (by change logScale (10789 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10781) (T := 106728247937942) (U := 165579309715)
    (by norm_num) (by norm_num) hr.1 gap_10789
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10781

theorem gap_10799 : PrimeGap 10789 10799 :=
  (primeGap_of_factors (ds := [2, 3, 2, 43, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10799 :
    (10799 : ℕ).Prime ∧ logScale (10799 : ℚ) = 13 ∧
      (92872088128 : ℤ) = ⌊logCenter (10799 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10799 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10799 : Reach 10799 106913982849791 165609993866 := by
  have hr := row_10799
  have hl := log_bounds hr.1
    (by change logScale (10799 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10789) (T := 106821110761663) (U := 165594658187)
    (by norm_num) (by norm_num) hr.1 gap_10799
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10789

theorem gap_10831 : PrimeGap 10799 10831 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 5, 2, 101, 2, 3, 2, 19, 2, 11, 2, 3, 2, 29, 2, 31, 2, 3, 2, 79, 2, 5, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10831 :
    (10831 : ℕ).Prime ∧ logScale (10831 : ℚ) = 13 ∧
      (92901676684 : ℤ) = ⌊logCenter (10831 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10831 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10831 : Reach 10831 107006884526475 165625285648 := by
  have hr := row_10831
  have hl := log_bounds hr.1
    (by change logScale (10831 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10799) (T := 106913982849791) (U := 165609993866)
    (by norm_num) (by norm_num) hr.1 gap_10831
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10799

#print axioms reach_10831

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
