import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper022
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block023

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_5749 : UpperReach 5749 56676965407253 := by
  have hr := row_5749
  have hl := log_bounds hr.1
    (by change logScale (5749 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5743) (H := 56590397595152) (u := 86567812025)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5743

theorem upper_reach_5779 : UpperReach 5779 56763585266660 := by
  have hr := row_5779
  have hl := log_bounds hr.1
    (by change logScale (5779 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5749) (H := 56676965407253) (u := 86619859331)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 73, 2, 3, 2, 29, 2, 23, 2, 3, 2, 53, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5749

theorem upper_reach_5783 : UpperReach 5783 56850212045286 := by
  have hr := row_5783
  have hl := log_bounds hr.1
    (by change logScale (5783 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5779) (H := 56763585266660) (u := 86626778550)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5779

theorem upper_reach_5791 : UpperReach 5791 56936852648003 := by
  have hr := row_5791
  have hl := log_bounds hr.1
    (by change logScale (5791 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5783) (H := 56850212045286) (u := 86640602641)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5783

theorem upper_reach_5801 : UpperReach 5801 57023510504002 := by
  have hr := row_5801
  have hl := log_bounds hr.1
    (by change logScale (5801 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5791) (H := 56936852648003) (u := 86657855923)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5791

theorem upper_reach_5807 : UpperReach 5807 57110178697700 := by
  have hr := row_5807
  have hl := log_bounds hr.1
    (by change logScale (5807 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5801) (H := 57023510504002) (u := 86668193622)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5801

theorem upper_reach_5813 : UpperReach 5813 57196857218421 := by
  have hr := row_5813
  have hl := log_bounds hr.1
    (by change logScale (5813 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5807) (H := 57110178697700) (u := 86678520645)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 37, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5807

theorem upper_reach_5821 : UpperReach 5821 57283549491938 := by
  have hr := row_5821
  have hl := log_bounds hr.1
    (by change logScale (5821 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5813) (H := 57196857218421) (u := 86692273441)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5813

theorem upper_reach_5827 : UpperReach 5827 57370252067654 := by
  have hr := row_5827
  have hl := log_bounds hr.1
    (by change logScale (5827 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5821) (H := 57283549491938) (u := 86702575640)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5821

theorem upper_reach_5839 : UpperReach 5839 57456975215981 := by
  have hr := row_5839
  have hl := log_bounds hr.1
    (by change logScale (5839 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5827) (H := 57370252067654) (u := 86723148251)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 19, 2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5827

theorem upper_reach_5843 : UpperReach 5843 57543705212451 := by
  have hr := row_5843
  have hl := log_bounds hr.1
    (by change logScale (5843 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5839) (H := 57456975215981) (u := 86729996394)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5839

theorem upper_reach_5849 : UpperReach 5849 57630445472350 := by
  have hr := row_5849
  have hl := log_bounds hr.1
    (by change logScale (5849 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5843) (H := 57543705212451) (u := 86740259823)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5843

theorem upper_reach_5851 : UpperReach 5851 57717189151052 := by
  have hr := row_5851
  have hl := log_bounds hr.1
    (by change logScale (5851 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5849) (H := 57630445472350) (u := 86743678626)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5849

theorem upper_reach_5857 : UpperReach 5857 57803943079157 := by
  have hr := row_5857
  have hl := log_bounds hr.1
    (by change logScale (5857 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5851) (H := 57717189151052) (u := 86753928029)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5851

theorem upper_reach_5861 : UpperReach 5861 57890703834366 := by
  have hr := row_5861
  have hl := log_bounds hr.1
    (by change logScale (5861 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5857) (H := 57803943079157) (u := 86760755133)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5857

theorem upper_reach_5867 : UpperReach 5867 57977474821500 := by
  have hr := row_5867
  have hl := log_bounds hr.1
    (by change logScale (5867 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5861) (H := 57890703834366) (u := 86770987058)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5861

theorem upper_reach_5869 : UpperReach 5869 58064249216950 := by
  have hr := row_5869
  have hl := log_bounds hr.1
    (by change logScale (5869 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5867) (H := 57977474821500) (u := 86774395374)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5867

theorem upper_reach_5879 : UpperReach 5879 58151040636578 := by
  have hr := row_5879
  have hl := log_bounds hr.1
    (by change logScale (5879 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5869) (H := 58064249216950) (u := 86791419552)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5869

theorem upper_reach_5881 : UpperReach 5881 58237835457567 := by
  have hr := row_5881
  have hl := log_bounds hr.1
    (by change logScale (5881 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5879) (H := 58151040636578) (u := 86794820913)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5879

theorem upper_reach_5897 : UpperReach 5897 58324657447871 := by
  have hr := row_5897
  have hl := log_bounds hr.1
    (by change logScale (5897 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5881) (H := 58237835457567) (u := 86821990228)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 7, 2, 3, 2, 43, 2, 71, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5881

theorem upper_reach_5903 : UpperReach 5903 58411489607668 := by
  have hr := row_5903
  have hl := log_bounds hr.1
    (by change logScale (5903 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5897) (H := 58324657447871) (u := 86832159721)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 17, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5897

theorem upper_reach_5923 : UpperReach 5923 58498355591275 := by
  have hr := row_5923
  have hl := log_bounds hr.1
    (by change logScale (5923 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5903) (H := 58411489607668) (u := 86865983531)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 19, 2, 23, 2, 3, 2, 5, 2, 61, 2, 3, 2, 31, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5903

theorem upper_reach_5927 : UpperReach 5927 58585228325937 := by
  have hr := row_5927
  have hl := log_bounds hr.1
    (by change logScale (5927 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5923) (H := 58498355591275) (u := 86872734586)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5923

theorem upper_reach_5939 : UpperReach 5939 58672121286461 := by
  have hr := row_5939
  have hl := log_bounds hr.1
    (by change logScale (5939 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5927) (H := 58585228325937) (u := 86892960448)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5927

#print axioms upper_reach_5939

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
