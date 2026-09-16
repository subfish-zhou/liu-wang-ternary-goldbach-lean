import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block044
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_10501 : PrimeGap 10499 10501 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_10501 :
    (10501 : ℕ).Prime ∧ logScale (10501 : ℚ) = 13 ∧
      (92592257663 : ℤ) = ⌊logCenter (10501 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10501 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10501 : Reach 10501 104131662694804 165144612947 := by
  have hr := row_10501
  have hl := log_bounds hr.1
    (by change logScale (10501 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10499) (T := 104039070437141) (U := 165128886386)
    (by norm_num) (by norm_num) hr.1 gap_10501
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10499

theorem gap_10513 : PrimeGap 10501 10513 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 7, 2, 3, 2, 23, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10513 :
    (10513 : ℕ).Prime ∧ logScale (10513 : ℚ) = 13 ∧
      (92603678621 : ℤ) = ⌊logCenter (10513 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10513 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10513 : Reach 10513 104224266373425 165160323051 := by
  have hr := row_10513
  have hl := log_bounds hr.1
    (by change logScale (10513 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10501) (T := 104131662694804) (U := 165144612947)
    (by norm_num) (by norm_num) hr.1 gap_10513
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10501

theorem gap_10529 : PrimeGap 10513 10529 :=
  (primeGap_of_factors (ds := [2, 3, 2, 13, 2, 67, 2, 3, 2, 17, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10529 :
    (10529 : ℕ).Prime ∧ logScale (10529 : ℚ) = 13 ∧
      (92618886304 : ℤ) = ⌊logCenter (10529 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10529 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10529 : Reach 10529 104316885259729 165176010772 := by
  have hr := row_10529
  have hl := log_bounds hr.1
    (by change logScale (10529 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10513) (T := 104224266373425) (U := 165160323051)
    (by norm_num) (by norm_num) hr.1 gap_10529
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10513

theorem gap_10531 : PrimeGap 10529 10531 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_10531 :
    (10531 : ℕ).Prime ∧ logScale (10531 : ℚ) = 13 ∧
      (92620785640 : ℤ) = ⌊logCenter (10531 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10531 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10531 : Reach 10531 104409506045369 165191697003 := by
  have hr := row_10531
  have hl := log_bounds hr.1
    (by change logScale (10531 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10529) (T := 104316885259729) (U := 165176010772)
    (by norm_num) (by norm_num) hr.1 gap_10531
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10529

theorem gap_10559 : PrimeGap 10531 10559 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 41, 2, 3, 2, 83, 2, 13, 2, 3, 2, 53, 2, 7, 2, 3, 2, 61, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10559 :
    (10559 : ℕ).Prime ∧ logScale (10559 : ℚ) = 13 ∧
      (92647338524 : ℤ) = ⌊logCenter (10559 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10559 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10559 : Reach 10559 104502153383893 165207343120 := by
  have hr := row_10559
  have hl := log_bounds hr.1
    (by change logScale (10559 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10531) (T := 104409506045369) (U := 165191697003)
    (by norm_num) (by norm_num) hr.1 gap_10559
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10531

theorem gap_10567 : PrimeGap 10559 10567 :=
  (primeGap_of_factors (ds := [2, 59, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10567 :
    (10567 : ℕ).Prime ∧ logScale (10567 : ℚ) = 13 ∧
      (92654912130 : ℤ) = ⌊logCenter (10567 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10567 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10567 : Reach 10567 104594808296023 165222978871 := by
  have hr := row_10567
  have hl := log_bounds hr.1
    (by change logScale (10567 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10559) (T := 104502153383893) (U := 165207343120)
    (by norm_num) (by norm_num) hr.1 gap_10567
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10559

theorem gap_10589 : PrimeGap 10567 10589 :=
  (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 97, 2, 3, 2, 7, 2, 71, 2, 3, 2, 19, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10589 :
    (10589 : ℕ).Prime ∧ logScale (10589 : ℚ) = 13 ∧
      (92675710020 : ℤ) = ⌊logCenter (10589 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10589 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10589 : Reach 10589 104687484006043 165238583611 := by
  have hr := row_10589
  have hl := log_bounds hr.1
    (by change logScale (10589 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10567) (T := 104594808296023) (U := 165222978871)
    (by norm_num) (by norm_num) hr.1 gap_10589
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10567

theorem gap_10597 : PrimeGap 10589 10597 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10597 :
    (10597 : ℕ).Prime ∧ logScale (10597 : ℚ) = 13 ∧
      (92683262177 : ℤ) = ⌊logCenter (10597 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10597 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10597 : Reach 10597 104780167268220 165254178042 := by
  have hr := row_10597
  have hl := log_bounds hr.1
    (by change logScale (10597 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10589) (T := 104687484006043) (U := 165238583611)
    (by norm_num) (by norm_num) hr.1 gap_10597
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10589

#print axioms reach_10597

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
