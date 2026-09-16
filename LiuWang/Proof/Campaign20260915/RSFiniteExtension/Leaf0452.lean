import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0451
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_10663 : PrimeGap 10657 10663 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10663 :
    (10663 : ℕ).Prime ∧ logScale (10663 : ℚ) = 13 ∧
      (92745350806 : ℤ) = ⌊logCenter (10663 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10663 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10663 : Reach 10663 105614614156945 165394130787 := by
  have hr := row_10663
  have hl := log_bounds hr.1
    (by change logScale (10663 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10657) (T := 105521868806139) (U := 165378619755)
    (by norm_num) (by norm_num) hr.1 gap_10663
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10657

theorem gap_10667 : PrimeGap 10663 10667 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10667 :
    (10667 : ℕ).Prime ∧ logScale (10667 : ℚ) = 13 ∧
      (92749101392 : ℤ) = ⌊logCenter (10667 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10667 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10667 : Reach 10667 105707363258337 165409637456 := by
  have hr := row_10667
  have hl := log_bounds hr.1
    (by change logScale (10667 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10663) (T := 105614614156945) (U := 165394130787)
    (by norm_num) (by norm_num) hr.1 gap_10667
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10663

theorem gap_10687 : PrimeGap 10667 10687 :=
  (primeGap_of_factors (ds := [2, 47, 2, 3, 2, 13, 2, 5, 2, 3, 2, 59, 2, 11, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10687 :
    (10687 : ℕ).Prime ∧ logScale (10687 : ℚ) = 13 ∧
      (92767833251 : ℤ) = ⌊logCenter (10687 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10687 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10687 : Reach 10687 105800131091588 165425116554 := by
  have hr := row_10687
  have hl := log_bounds hr.1
    (by change logScale (10687 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10667) (T := 105707363258337) (U := 165409637456)
    (by norm_num) (by norm_num) hr.1 gap_10687
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10667

theorem gap_10691 : PrimeGap 10687 10691 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10691 :
    (10691 : ℕ).Prime ∧ logScale (10691 : ℚ) = 13 ∧
      (92771575416 : ℤ) = ⌊logCenter (10691 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10691 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10691 : Reach 10691 105892902667004 165440591308 := by
  have hr := row_10691
  have hl := log_bounds hr.1
    (by change logScale (10691 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10687) (T := 105800131091588) (U := 165425116554)
    (by norm_num) (by norm_num) hr.1 gap_10691
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10687

theorem gap_10709 : PrimeGap 10691 10709 :=
  (primeGap_of_factors (ds := [2, 17, 2, 3, 2, 19, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10709 :
    (10709 : ℕ).Prime ∧ logScale (10709 : ℚ) = 13 ∧
      (92788397850 : ℤ) = ⌊logCenter (10709 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10709 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10709 : Reach 10709 105985691064854 165456041494 := by
  have hr := row_10709
  have hl := log_bounds hr.1
    (by change logScale (10709 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10691) (T := 105892902667004) (U := 165440591308)
    (by norm_num) (by norm_num) hr.1 gap_10709
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10691

theorem gap_10711 : PrimeGap 10709 10711 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_10711 :
    (10711 : ℕ).Prime ∧ logScale (10711 : ℚ) = 13 ∧
      (92790265263 : ℤ) = ⌊logCenter (10711 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10711 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10711 : Reach 10711 106078481330117 165471490238 := by
  have hr := row_10711
  have hl := log_bounds hr.1
    (by change logScale (10711 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10709) (T := 105985691064854) (U := 165456041494)
    (by norm_num) (by norm_num) hr.1 gap_10711
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10709

theorem gap_10723 : PrimeGap 10711 10723 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 7, 2, 3, 2, 71, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10723 :
    (10723 : ℕ).Prime ∧ logScale (10723 : ℚ) = 13 ∧
      (92801462428 : ℤ) = ⌊logCenter (10723 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10723 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10723 : Reach 10723 106171282792545 165486923133 := by
  have hr := row_10723
  have hl := log_bounds hr.1
    (by change logScale (10723 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10711) (T := 106078481330117) (U := 165471490238)
    (by norm_num) (by norm_num) hr.1 gap_10723
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10711

theorem gap_10729 : PrimeGap 10723 10729 :=
  (primeGap_of_factors (ds := [2, 3, 2, 17, 2]) (by decide +kernel) (by decide +kernel))

theorem row_10729 :
    (10729 : ℕ).Prime ∧ logScale (10729 : ℚ) = 13 ∧
      (92807056312 : ℤ) = ⌊logCenter (10729 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (10729 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_10729 : Reach 10729 106264089848857 165502348835 := by
  have hr := row_10729
  have hl := log_bounds hr.1
    (by change logScale (10729 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 10723) (T := 106171282792545) (U := 165486923133)
    (by norm_num) (by norm_num) hr.1 gap_10729
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_10723

#print axioms reach_10729

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
