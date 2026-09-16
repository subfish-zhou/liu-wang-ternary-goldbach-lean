import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0311
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_7591 : PrimeGap 7589 7591 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_7591 :
    (7591 : ℕ).Prime ∧ logScale (7591 : ℚ) = 12 ∧
      (89347186108 : ℤ) = ⌊logCenter (7591 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7591 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7591 : Reach 7591 74988012380687 159364986575 := by
  have hr := row_7591
  have hl := log_bounds hr.1
    (by change logScale (7591 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7589) (T := 74898665194579) (U := 159343992636)
    (by norm_num) (by norm_num) hr.1 gap_7591
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7589

theorem gap_7603 : PrimeGap 7591 7603 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 71, 2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7603 :
    (7603 : ℕ).Prime ∧ logScale (7603 : ℚ) = 12 ∧
      (89362981821 : ℤ) = ⌊logCenter (7603 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7603 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7603 : Reach 7603 75077375362508 159385950136 := by
  have hr := row_7603
  have hl := log_bounds hr.1
    (by change logScale (7603 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7591) (T := 74988012380687) (U := 159364986575)
    (by norm_num) (by norm_num) hr.1 gap_7603
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7591

theorem gap_7607 : PrimeGap 7603 7607 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7607 :
    (7607 : ℕ).Prime ∧ logScale (7607 : ℚ) = 12 ∧
      (89368241518 : ℤ) = ⌊logCenter (7607 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7607 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7607 : Reach 7607 75166743604026 159406905428 := by
  have hr := row_7607
  have hl := log_bounds hr.1
    (by change logScale (7607 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7603) (T := 75077375362508) (U := 159385950136)
    (by norm_num) (by norm_num) hr.1 gap_7607
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7603

theorem gap_7621 : PrimeGap 7607 7621 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 23, 2, 5, 2, 3, 2, 19, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7621 :
    (7621 : ℕ).Prime ∧ logScale (7621 : ℚ) = 12 ∧
      (89386628705 : ℤ) = ⌊logCenter (7621 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7621 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7621 : Reach 7621 75256130232731 159427824970 := by
  have hr := row_7621
  have hl := log_bounds hr.1
    (by change logScale (7621 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7607) (T := 75166743604026) (U := 159406905428)
    (by norm_num) (by norm_num) hr.1 gap_7621
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7607

theorem gap_7639 : PrimeGap 7621 7639 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 29, 2, 3, 2, 13, 2, 17, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7639 :
    (7639 : ℕ).Prime ∧ logScale (7639 : ℚ) = 12 ∧
      (89410219804 : ℤ) = ⌊logCenter (7639 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7639 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7639 : Reach 7639 75345540452535 159448697951 := by
  have hr := row_7639
  have hl := log_bounds hr.1
    (by change logScale (7639 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7621) (T := 75256130232731) (U := 159427824970)
    (by norm_num) (by norm_num) hr.1 gap_7639
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7621

theorem gap_7643 : PrimeGap 7639 7643 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7643 :
    (7643 : ℕ).Prime ∧ logScale (7643 : ℚ) = 12 ∧
      (89415454721 : ℤ) = ⌊logCenter (7643 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7643 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7643 : Reach 7643 75434955907256 159469562738 := by
  have hr := row_7643
  have hl := log_bounds hr.1
    (by change logScale (7643 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7639) (T := 75345540452535) (U := 159448697951)
    (by norm_num) (by norm_num) hr.1 gap_7643
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7639

theorem gap_7649 : PrimeGap 7643 7649 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7649 :
    (7649 : ℕ).Prime ∧ logScale (7649 : ℚ) = 12 ∧
      (89423301962 : ℤ) = ⌊logCenter (7649 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7649 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7649 : Reach 7649 75524379209218 159490413884 := by
  have hr := row_7649
  have hl := log_bounds hr.1
    (by change logScale (7649 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7643) (T := 75434955907256) (U := 159469562738)
    (by norm_num) (by norm_num) hr.1 gap_7649
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7643

theorem gap_7669 : PrimeGap 7649 7669 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 47, 2, 79, 2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7669 :
    (7669 : ℕ).Prime ∧ logScale (7669 : ℚ) = 12 ∧
      (89449415046 : ℤ) = ⌊logCenter (7669 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7669 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7669 : Reach 7669 75613828624264 159511213365 := by
  have hr := row_7669
  have hl := log_bounds hr.1
    (by change logScale (7669 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7649) (T := 75524379209218) (U := 159490413884)
    (by norm_num) (by norm_num) hr.1 gap_7669
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7649

#print axioms reach_7669

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
