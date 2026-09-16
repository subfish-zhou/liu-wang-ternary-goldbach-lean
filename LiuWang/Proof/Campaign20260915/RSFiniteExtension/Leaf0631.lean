import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0630
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_14737 : PrimeGap 14731 14737 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14737 :
    (14737 : ℕ).Prime ∧ logScale (14737 : ℚ) = 13 ∧
      (95981166138 : ℤ) = ⌊logCenter (14737 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14737 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14737 : Reach 14737 145662169973381 171057718004 := by
  have hr := row_14737
  have hl := log_bounds hr.1
    (by change logScale (14737 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14731) (T := 145566188807243) (U := 171046110640)
    (by norm_num) (by norm_num) hr.1 gap_14737
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14731

theorem gap_14741 : PrimeGap 14737 14741 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14741 :
    (14741 : ℕ).Prime ∧ logScale (14741 : ℚ) = 13 ∧
      (95983880026 : ℤ) = ⌊logCenter (14741 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14741 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14741 : Reach 14741 145758153853407 171069323006 := by
  have hr := row_14741
  have hl := log_bounds hr.1
    (by change logScale (14741 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14737) (T := 145662169973381) (U := 171057718004)
    (by norm_num) (by norm_num) hr.1 gap_14741
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14737

theorem gap_14747 : PrimeGap 14741 14747 :=
  (primeGap_of_factors (ds := [2, 23, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14747 :
    (14747 : ℕ).Prime ∧ logScale (14747 : ℚ) = 13 ∧
      (95987949478 : ℤ) = ⌊logCenter (14747 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14747 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14747 : Reach 14747 145854141802885 171080924073 := by
  have hr := row_14747
  have hl := log_bounds hr.1
    (by change logScale (14747 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14741) (T := 145758153853407) (U := 171069323006)
    (by norm_num) (by norm_num) hr.1 gap_14747
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14741

theorem gap_14753 : PrimeGap 14747 14753 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14753 :
    (14753 : ℕ).Prime ∧ logScale (14753 : ℚ) = 13 ∧
      (95992017275 : ℤ) = ⌊logCenter (14753 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14753 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14753 : Reach 14753 145950133820160 171092521208 := by
  have hr := row_14753
  have hl := log_bounds hr.1
    (by change logScale (14753 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14747) (T := 145854141802885) (U := 171080924073)
    (by norm_num) (by norm_num) hr.1 gap_14753
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14747

theorem gap_14759 : PrimeGap 14753 14759 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14759 :
    (14759 : ℕ).Prime ∧ logScale (14759 : ℚ) = 13 ∧
      (95996083418 : ℤ) = ⌊logCenter (14759 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14759 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14759 : Reach 14759 146046129903578 171104114414 := by
  have hr := row_14759
  have hl := log_bounds hr.1
    (by change logScale (14759 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14753) (T := 145950133820160) (U := 171092521208)
    (by norm_num) (by norm_num) hr.1 gap_14759
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14753

theorem gap_14767 : PrimeGap 14759 14767 :=
  (primeGap_of_factors (ds := [2, 29, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14767 :
    (14767 : ℕ).Prime ∧ logScale (14767 : ℚ) = 13 ∧
      (96001502370 : ℤ) = ⌊logCenter (14767 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14767 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14767 : Reach 14767 146142131405948 171115702124 := by
  have hr := row_14767
  have hl := log_bounds hr.1
    (by change logScale (14767 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14759) (T := 146046129903578) (U := 171104114414)
    (by norm_num) (by norm_num) hr.1 gap_14767
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14759

theorem gap_14771 : PrimeGap 14767 14771 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14771 :
    (14771 : ℕ).Prime ∧ logScale (14771 : ℚ) = 13 ∧
      (96004210746 : ℤ) = ⌊logCenter (14771 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14771 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14771 : Reach 14771 146238135616694 171127287480 := by
  have hr := row_14771
  have hl := log_bounds hr.1
    (by change logScale (14771 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14767) (T := 146142131405948) (U := 171115702124)
    (by norm_num) (by norm_num) hr.1 gap_14771
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14767

theorem gap_14779 : PrimeGap 14771 14779 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_14779 :
    (14779 : ℕ).Prime ∧ logScale (14779 : ℚ) = 13 ∧
      (96009625298 : ℤ) = ⌊logCenter (14779 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (14779 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_14779 : Reach 14779 146334145241992 171138867348 := by
  have hr := row_14779
  have hl := log_bounds hr.1
    (by change logScale (14779 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 14771) (T := 146238135616694) (U := 171127287480)
    (by norm_num) (by norm_num) hr.1 gap_14779
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_14771

#print axioms reach_14779

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
