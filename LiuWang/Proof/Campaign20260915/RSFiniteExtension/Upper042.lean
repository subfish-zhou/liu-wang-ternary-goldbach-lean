import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper041
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block042

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_9833 : UpperReach 9833 97487800213042 := by
  have hr := row_9833
  have hl := log_bounds hr.1
    (by change logScale (9833 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9829) (H := 97395865219452) (u := 91934993514)
    (by norm_num) (by norm_num) hr.1 gap_9833 hl.2
    (by norm_num) upper_reach_9829

theorem upper_reach_9839 : UpperReach 9839 97579741306672 := by
  have hr := row_9839
  have hl := log_bounds hr.1
    (by change logScale (9839 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9833) (H := 97487800213042) (u := 91941093554)
    (by norm_num) (by norm_num) hr.1 gap_9839 hl.2
    (by norm_num) upper_reach_9833

theorem upper_reach_9851 : UpperReach 9851 97671694589232 := by
  have hr := row_9851
  have hl := log_bounds hr.1
    (by change logScale (9851 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9839) (H := 97579741306672) (u := 91953282484)
    (by norm_num) (by norm_num) hr.1 gap_9851 hl.2
    (by norm_num) upper_reach_9839

theorem upper_reach_9857 : UpperReach 9857 97763653960690 := by
  have hr := row_9857
  have hl := log_bounds hr.1
    (by change logScale (9857 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9851) (H := 97671694589232) (u := 91959371382)
    (by norm_num) (by norm_num) hr.1 gap_9857 hl.2
    (by norm_num) upper_reach_9851

theorem upper_reach_9859 : UpperReach 9859 97855615360957 := by
  have hr := row_9859
  have hl := log_bounds hr.1
    (by change logScale (9859 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9857) (H := 97763653960690) (u := 91961400191)
    (by norm_num) (by norm_num) hr.1 gap_9859 hl.2
    (by norm_num) upper_reach_9857

theorem upper_reach_9871 : UpperReach 9871 97947588925443 := by
  have hr := row_9871
  have hl := log_bounds hr.1
    (by change logScale (9871 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9859) (H := 97855615360957) (u := 91973564410)
    (by norm_num) (by norm_num) hr.1 gap_9871 hl.2
    (by norm_num) upper_reach_9859

theorem upper_reach_9883 : UpperReach 9883 98039574639368 := by
  have hr := row_9883
  have hl := log_bounds hr.1
    (by change logScale (9883 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9871) (H := 97947588925443) (u := 91985713849)
    (by norm_num) (by norm_num) hr.1 gap_9883 hl.2
    (by norm_num) upper_reach_9871

theorem upper_reach_9887 : UpperReach 9887 98131564399829 := by
  have hr := row_9887
  have hl := log_bounds hr.1
    (by change logScale (9887 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9883) (H := 98039574639368) (u := 91989760385)
    (by norm_num) (by norm_num) hr.1 gap_9887 hl.2
    (by norm_num) upper_reach_9883

theorem upper_reach_9901 : UpperReach 9901 98223568310282 := by
  have hr := row_9901
  have hl := log_bounds hr.1
    (by change logScale (9901 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9887) (H := 98131564399829) (u := 92003910377)
    (by norm_num) (by norm_num) hr.1 gap_9901 hl.2
    (by norm_num) upper_reach_9887

theorem upper_reach_9907 : UpperReach 9907 98315578278893 := by
  have hr := row_9907
  have hl := log_bounds hr.1
    (by change logScale (9907 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9901) (H := 98223568310282) (u := 92009968535)
    (by norm_num) (by norm_num) hr.1 gap_9907 hl.2
    (by norm_num) upper_reach_9901

theorem upper_reach_9923 : UpperReach 9923 98407604384674 := by
  have hr := row_9923
  have hl := log_bounds hr.1
    (by change logScale (9923 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9907) (H := 98315578278893) (u := 92026105705)
    (by norm_num) (by norm_num) hr.1 gap_9923 hl.2
    (by norm_num) upper_reach_9907

theorem upper_reach_9929 : UpperReach 9929 98499636535186 := by
  have hr := row_9929
  have hl := log_bounds hr.1
    (by change logScale (9929 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9923) (H := 98407604384674) (u := 92032150436)
    (by norm_num) (by norm_num) hr.1 gap_9929 hl.2
    (by norm_num) upper_reach_9923

theorem upper_reach_9931 : UpperReach 9931 98591670699797 := by
  have hr := row_9931
  have hl := log_bounds hr.1
    (by change logScale (9931 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9929) (H := 98499636535186) (u := 92034164535)
    (by norm_num) (by norm_num) hr.1 gap_9931 hl.2
    (by norm_num) upper_reach_9929

theorem upper_reach_9941 : UpperReach 9941 98683714928821 := by
  have hr := row_9941
  have hl := log_bounds hr.1
    (by change logScale (9941 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9931) (H := 98591670699797) (u := 92044228948)
    (by norm_num) (by norm_num) hr.1 gap_9941 hl.2
    (by norm_num) upper_reach_9931

theorem upper_reach_9949 : UpperReach 9949 98775767202089 := by
  have hr := row_9949
  have hl := log_bounds hr.1
    (by change logScale (9949 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9941) (H := 98683714928821) (u := 92052273192)
    (by norm_num) (by norm_num) hr.1 gap_9949 hl.2
    (by norm_num) upper_reach_9941

theorem upper_reach_9967 : UpperReach 9967 98867837551280 := by
  have hr := row_9967
  have hl := log_bounds hr.1
    (by change logScale (9967 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9949) (H := 98775767202089) (u := 92070349115)
    (by norm_num) (by norm_num) hr.1 gap_9967 hl.2
    (by norm_num) upper_reach_9949

theorem upper_reach_9973 : UpperReach 9973 98959913918526 := by
  have hr := row_9973
  have hl := log_bounds hr.1
    (by change logScale (9973 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9967) (H := 98867837551280) (u := 92076367170)
    (by norm_num) (by norm_num) hr.1 gap_9973 hl.2
    (by norm_num) upper_reach_9967

theorem upper_reach_10007 : UpperReach 10007 99052024319839 := by
  have hr := row_10007
  have hl := log_bounds hr.1
    (by change logScale (10007 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9973) (H := 98959913918526) (u := 92110401237)
    (by norm_num) (by norm_num) hr.1 gap_10007 hl.2
    (by norm_num) upper_reach_9973

theorem upper_reach_10009 : UpperReach 10009 99144136719553 := by
  have hr := row_10009
  have hl := log_bounds hr.1
    (by change logScale (10009 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10007) (H := 99052024319839) (u := 92112399638)
    (by norm_num) (by norm_num) hr.1 gap_10009 hl.2
    (by norm_num) upper_reach_10007

theorem upper_reach_10037 : UpperReach 10037 99236277055033 := by
  have hr := row_10037
  have hl := log_bounds hr.1
    (by change logScale (10037 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10009) (H := 99144136719553) (u := 92140335404)
    (by norm_num) (by norm_num) hr.1 gap_10037 hl.2
    (by norm_num) upper_reach_10009

theorem upper_reach_10039 : UpperReach 10039 99328419382942 := by
  have hr := row_10039
  have hl := log_bounds hr.1
    (by change logScale (10039 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10037) (H := 99236277055033) (u := 92142327833)
    (by norm_num) (by norm_num) hr.1 gap_10039 hl.2
    (by norm_num) upper_reach_10037

theorem upper_reach_10061 : UpperReach 10061 99420583601407 := by
  have hr := row_10061
  have hl := log_bounds hr.1
    (by change logScale (10061 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10039) (H := 99328419382942) (u := 92164218389)
    (by norm_num) (by norm_num) hr.1 gap_10061 hl.2
    (by norm_num) upper_reach_10039

theorem upper_reach_10067 : UpperReach 10067 99512753781716 := by
  have hr := row_10067
  have hl := log_bounds hr.1
    (by change logScale (10067 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10061) (H := 99420583601407) (u := 92170180233)
    (by norm_num) (by norm_num) hr.1 gap_10067 hl.2
    (by norm_num) upper_reach_10061

theorem upper_reach_10069 : UpperReach 10069 99604925948517 := by
  have hr := row_10069
  have hl := log_bounds hr.1
    (by change logScale (10069 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10067) (H := 99512753781716) (u := 92172166725)
    (by norm_num) (by norm_num) hr.1 gap_10069 hl.2
    (by norm_num) upper_reach_10067

#print axioms upper_reach_10069

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
