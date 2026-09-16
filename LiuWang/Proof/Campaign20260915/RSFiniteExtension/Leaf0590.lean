import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block058
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_13709 : PrimeGap 13697 13709 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 71, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13709 :
    (13709 : ℕ).Prime ∧ logScale (13709 : ℚ) = 13 ∧
      (95258078270 : ℤ) = ⌊logCenter (13709 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13709 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13709 : Reach 13709 135716796658587 169811451341 := by
  have hr := row_13709
  have hl := log_bounds hr.1
    (by change logScale (13709 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13697) (T := 135621538580317) (U := 169799064481)
    (by norm_num) (by norm_num) hr.1 gap_13709
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13697

theorem gap_13711 : PrimeGap 13709 13711 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_13711 :
    (13711 : ℕ).Prime ∧ logScale (13711 : ℚ) = 13 ∧
      (95259537059 : ℤ) = ⌊logCenter (13711 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13711 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13711 : Reach 13711 135812056195646 169823837297 := by
  have hr := row_13711
  have hl := log_bounds hr.1
    (by change logScale (13711 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13709) (T := 135716796658587) (U := 169811451341)
    (by norm_num) (by norm_num) hr.1 gap_13711
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13709

theorem gap_13721 : PrimeGap 13711 13721 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13721 :
    (13721 : ℕ).Prime ∧ logScale (13721 : ℚ) = 13 ∧
      (95266827815 : ℤ) = ⌊logCenter (13721 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13721 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13721 : Reach 13721 135907323023461 169836215128 := by
  have hr := row_13721
  have hl := log_bounds hr.1
    (by change logScale (13721 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13711) (T := 135812056195646) (U := 169823837297)
    (by norm_num) (by norm_num) hr.1 gap_13721
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13711

theorem gap_13723 : PrimeGap 13721 13723 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_13723 :
    (13723 : ℕ).Prime ∧ logScale (13723 : ℚ) = 13 ∧
      (95268285328 : ℤ) = ⌊logCenter (13723 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13723 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13723 : Reach 13723 136002591308789 169848592057 := by
  have hr := row_13723
  have hl := log_bounds hr.1
    (by change logScale (13723 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13721) (T := 135907323023461) (U := 169836215128)
    (by norm_num) (by norm_num) hr.1 gap_13723
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13721

theorem gap_13729 : PrimeGap 13723 13729 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13729 :
    (13729 : ℕ).Prime ∧ logScale (13729 : ℚ) = 13 ∧
      (95272656595 : ℤ) = ⌊logCenter (13729 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13729 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13729 : Reach 13729 136097863965384 169860964478 := by
  have hr := row_13729
  have hl := log_bounds hr.1
    (by change logScale (13729 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13723) (T := 136002591308789) (U := 169848592057)
    (by norm_num) (by norm_num) hr.1 gap_13729
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13723

theorem gap_13751 : PrimeGap 13729 13751 :=
  (primeGap_of_factors (ds := [2, 3, 2, 31, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 59, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13751 :
    (13751 : ℕ).Prime ∧ logScale (13751 : ℚ) = 13 ∧
      (95288668243 : ℤ) = ⌊logCenter (13751 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13751 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13751 : Reach 13751 136193152633627 169873318003 := by
  have hr := row_13751
  have hl := log_bounds hr.1
    (by change logScale (13751 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13729) (T := 136097863965384) (U := 169860964478)
    (by norm_num) (by norm_num) hr.1 gap_13751
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13729

theorem gap_13757 : PrimeGap 13751 13757 :=
  (primeGap_of_factors (ds := [2, 17, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13757 :
    (13757 : ℕ).Prime ∧ logScale (13757 : ℚ) = 13 ∧
      (95293030610 : ℤ) = ⌊logCenter (13757 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13757 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13757 : Reach 13757 136288445664237 169885667038 := by
  have hr := row_13757
  have hl := log_bounds hr.1
    (by change logScale (13757 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13751) (T := 136193152633627) (U := 169873318003)
    (by norm_num) (by norm_num) hr.1 gap_13757
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13751

theorem gap_13759 : PrimeGap 13757 13759 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_13759 :
    (13759 : ℕ).Prime ∧ logScale (13759 : ℚ) = 13 ∧
      (95294484310 : ℤ) = ⌊logCenter (13759 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13759 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13759 : Reach 13759 136383740148547 169898015175 := by
  have hr := row_13759
  have hl := log_bounds hr.1
    (by change logScale (13759 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13757) (T := 136288445664237) (U := 169885667038)
    (by norm_num) (by norm_num) hr.1 gap_13759
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13757

#print axioms reach_13759

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
