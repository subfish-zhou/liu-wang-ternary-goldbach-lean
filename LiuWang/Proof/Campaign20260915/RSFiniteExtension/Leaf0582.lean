import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0581
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_13649 : PrimeGap 13633 13649 :=
  (primeGap_of_factors (ds := [2, 3, 2, 13, 2, 23, 2, 3, 2, 7, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13649 :
    (13649 : ℕ).Prime ∧ logScale (13649 : ℚ) = 13 ∧
      (95214215344 : ℤ) = ⌊logCenter (13649 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13649 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13649 : Reach 13649 134954853240446 169712231551 := by
  have hr := row_13649
  have hl := log_bounds hr.1
    (by change logScale (13649 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13633) (T := 134859639025102) (U := 169699797509)
    (by norm_num) (by norm_num) hr.1 gap_13649
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13633

theorem gap_13669 : PrimeGap 13649 13669 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 19, 2, 13, 2, 3, 2, 79, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13669 :
    (13669 : ℕ).Prime ∧ logScale (13669 : ℚ) = 13 ∧
      (95228857707 : ℤ) = ⌊logCenter (13669 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13669 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13669 : Reach 13669 135050082098153 169724648308 := by
  have hr := row_13669
  have hl := log_bounds hr.1
    (by change logScale (13669 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13649) (T := 134954853240446) (U := 169712231551)
    (by norm_num) (by norm_num) hr.1 gap_13669
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13649

theorem gap_13679 : PrimeGap 13669 13679 :=
  (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13679 :
    (13679 : ℕ).Prime ∧ logScale (13679 : ℚ) = 13 ∧
      (95236170857 : ℤ) = ⌊logCenter (13679 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13679 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13679 : Reach 13679 135145318269010 169737056895 := by
  have hr := row_13679
  have hl := log_bounds hr.1
    (by change logScale (13679 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13669) (T := 135050082098153) (U := 169724648308)
    (by norm_num) (by norm_num) hr.1 gap_13679
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13669

theorem gap_13681 : PrimeGap 13679 13681 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_13681 :
    (13681 : ℕ).Prime ∧ logScale (13681 : ℚ) = 13 ∧
      (95237632845 : ℤ) = ⌊logCenter (13681 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13681 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13681 : Reach 13681 135240555901855 169749464575 := by
  have hr := row_13681
  have hl := log_bounds hr.1
    (by change logScale (13681 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13679) (T := 135145318269010) (U := 169737056895)
    (by norm_num) (by norm_num) hr.1 gap_13681
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13679

theorem gap_13687 : PrimeGap 13681 13687 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13687 :
    (13687 : ℕ).Prime ∧ logScale (13687 : ℚ) = 13 ∧
      (95242017528 : ℤ) = ⌊logCenter (13687 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13687 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13687 : Reach 13687 135335797919383 169761867722 := by
  have hr := row_13687
  have hl := log_bounds hr.1
    (by change logScale (13687 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13681) (T := 135240555901855) (U := 169749464575)
    (by norm_num) (by norm_num) hr.1 gap_13687
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13681

theorem gap_13691 : PrimeGap 13687 13691 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13691 :
    (13691 : ℕ).Prime ∧ logScale (13691 : ℚ) = 13 ∧
      (95244939582 : ℤ) = ⌊logCenter (13691 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13691 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13691 : Reach 13691 135431042858965 169774268151 := by
  have hr := row_13691
  have hl := log_bounds hr.1
    (by change logScale (13691 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13687) (T := 135335797919383) (U := 169761867722)
    (by norm_num) (by norm_num) hr.1 gap_13691
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13687

theorem gap_13693 : PrimeGap 13691 13693 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_13693 :
    (13693 : ℕ).Prime ∧ logScale (13693 : ℚ) = 13 ∧
      (95246400289 : ℤ) = ⌊logCenter (13693 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13693 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13693 : Reach 13693 135526289259254 169786667674 := by
  have hr := row_13693
  have hl := log_bounds hr.1
    (by change logScale (13693 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13691) (T := 135431042858965) (U := 169774268151)
    (by norm_num) (by norm_num) hr.1 gap_13693
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13691

theorem gap_13697 : PrimeGap 13693 13697 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13697 :
    (13697 : ℕ).Prime ∧ logScale (13697 : ℚ) = 13 ∧
      (95249321063 : ℤ) = ⌊logCenter (13697 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13697 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13697 : Reach 13697 135621538580317 169799064481 := by
  have hr := row_13697
  have hl := log_bounds hr.1
    (by change logScale (13697 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13693) (T := 135526289259254) (U := 169786667674)
    (by norm_num) (by norm_num) hr.1 gap_13697
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13693

#print axioms reach_13697

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
