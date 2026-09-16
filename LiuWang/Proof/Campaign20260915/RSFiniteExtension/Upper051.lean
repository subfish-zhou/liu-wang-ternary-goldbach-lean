import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper050
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block051

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_11927 : UpperReach 11927 117559824557613 := by
  have hr := row_11927
  have hl := log_bounds hr.1
    (by change logScale (11927 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11923) (H := 117465958957406) (u := 93865600131)
    (by norm_num) (by norm_num) hr.1 gap_11927 hl.2
    (by norm_num) upper_reach_11923

theorem upper_reach_11933 : UpperReach 11933 117653695187158 := by
  have hr := row_11933
  have hl := log_bounds hr.1
    (by change logScale (11933 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11927) (H := 117559824557613) (u := 93870629469)
    (by norm_num) (by norm_num) hr.1 gap_11933 hl.2
    (by norm_num) upper_reach_11927

theorem upper_reach_11939 : UpperReach 11939 117747570843513 := by
  have hr := row_11939
  have hl := log_bounds hr.1
    (by change logScale (11939 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11933) (H := 117653695187158) (u := 93875656279)
    (by norm_num) (by norm_num) hr.1 gap_11939 hl.2
    (by norm_num) upper_reach_11933

theorem upper_reach_11941 : UpperReach 11941 117841448174910 := by
  have hr := row_11941
  have hl := log_bounds hr.1
    (by change logScale (11941 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11939) (H := 117747570843513) (u := 93877331321)
    (by norm_num) (by norm_num) hr.1 gap_11941 hl.2
    (by norm_num) upper_reach_11939

theorem upper_reach_11953 : UpperReach 11953 117935335550670 := by
  have hr := row_11953
  have hl := log_bounds hr.1
    (by change logScale (11953 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11941) (H := 117841448174910) (u := 93887375684)
    (by norm_num) (by norm_num) hr.1 gap_11953 hl.2
    (by norm_num) upper_reach_11941

theorem upper_reach_11959 : UpperReach 11959 118029227944831 := by
  have hr := row_11959
  have hl := log_bounds hr.1
    (by change logScale (11959 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11953) (H := 117935335550670) (u := 93892394085)
    (by norm_num) (by norm_num) hr.1 gap_11959 hl.2
    (by norm_num) upper_reach_11953

theorem upper_reach_11969 : UpperReach 11969 118123128697401 := by
  have hr := row_11969
  have hl := log_bounds hr.1
    (by change logScale (11969 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11959) (H := 118029227944831) (u := 93900752494)
    (by norm_num) (by norm_num) hr.1 gap_11969 hl.2
    (by norm_num) upper_reach_11959

theorem upper_reach_11971 : UpperReach 11971 118217031120815 := by
  have hr := row_11971
  have hl := log_bounds hr.1
    (by change logScale (11971 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11969) (H := 118123128697401) (u := 93902423338)
    (by norm_num) (by norm_num) hr.1 gap_11971 hl.2
    (by norm_num) upper_reach_11969

theorem upper_reach_11981 : UpperReach 11981 118310941894263 := by
  have hr := row_11981
  have hl := log_bounds hr.1
    (by change logScale (11981 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11971) (H := 118217031120815) (u := 93910773372)
    (by norm_num) (by norm_num) hr.1 gap_11981 hl.2
    (by norm_num) upper_reach_11971

theorem upper_reach_11987 : UpperReach 11987 118404857674387 := by
  have hr := row_11987
  have hl := log_bounds hr.1
    (by change logScale (11987 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11981) (H := 118310941894263) (u := 93915780048)
    (by norm_num) (by norm_num) hr.1 gap_11987 hl.2
    (by norm_num) upper_reach_11981

theorem upper_reach_12007 : UpperReach 12007 118498790125349 := by
  have hr := row_12007
  have hl := log_bounds hr.1
    (by change logScale (12007 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11987) (H := 118404857674387) (u := 93932450886)
    (by norm_num) (by norm_num) hr.1 gap_12007 hl.2
    (by norm_num) upper_reach_11987

theorem upper_reach_12011 : UpperReach 12011 118592725907146 := by
  have hr := row_12011
  have hl := log_bounds hr.1
    (by change logScale (12011 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12007) (H := 118498790125349) (u := 93935781721)
    (by norm_num) (by norm_num) hr.1 gap_12011 hl.2
    (by norm_num) upper_reach_12007

theorem upper_reach_12037 : UpperReach 12037 118686683312372 := by
  have hr := row_12037
  have hl := log_bounds hr.1
    (by change logScale (12037 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12011) (H := 118592725907146) (u := 93957405150)
    (by norm_num) (by norm_num) hr.1 gap_12037 hl.2
    (by norm_num) upper_reach_12011

theorem upper_reach_12041 : UpperReach 12041 118780644040133 := by
  have hr := row_12041
  have hl := log_bounds hr.1
    (by change logScale (12041 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12037) (H := 118686683312372) (u := 93960727685)
    (by norm_num) (by norm_num) hr.1 gap_12041 hl.2
    (by norm_num) upper_reach_12037

theorem upper_reach_12043 : UpperReach 12043 118874606428747 := by
  have hr := row_12043
  have hl := log_bounds hr.1
    (by change logScale (12043 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12041) (H := 118780644040133) (u := 93962388538)
    (by norm_num) (by norm_num) hr.1 gap_12043 hl.2
    (by norm_num) upper_reach_12041

theorem upper_reach_12049 : UpperReach 12049 118968573798268 := by
  have hr := row_12049
  have hl := log_bounds hr.1
    (by change logScale (12049 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12043) (H := 118874606428747) (u := 93967369445)
    (by norm_num) (by norm_num) hr.1 gap_12049 hl.2
    (by norm_num) upper_reach_12043

theorem upper_reach_12071 : UpperReach 12071 119062559409917 := by
  have hr := row_12071
  have hl := log_bounds hr.1
    (by change logScale (12071 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12049) (H := 118968573798268) (u := 93985611573)
    (by norm_num) (by norm_num) hr.1 gap_12071 hl.2
    (by norm_num) upper_reach_12049

theorem upper_reach_12073 : UpperReach 12073 119156546678292 := by
  have hr := row_12073
  have hl := log_bounds hr.1
    (by change logScale (12073 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12071) (H := 119062559409917) (u := 93987268299)
    (by norm_num) (by norm_num) hr.1 gap_12073 hl.2
    (by norm_num) upper_reach_12071

theorem upper_reach_12097 : UpperReach 12097 119250553806003 := by
  have hr := row_12097
  have hl := log_bounds hr.1
    (by change logScale (12097 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12073) (H := 119156546678292) (u := 94007127635)
    (by norm_num) (by norm_num) hr.1 gap_12097 hl.2
    (by norm_num) upper_reach_12073

theorem upper_reach_12101 : UpperReach 12101 119344564239773 := by
  have hr := row_12101
  have hl := log_bounds hr.1
    (by change logScale (12101 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12097) (H := 119250553806003) (u := 94010433694)
    (by norm_num) (by norm_num) hr.1 gap_12101 hl.2
    (by norm_num) upper_reach_12097

theorem upper_reach_12107 : UpperReach 12107 119438579630582 := by
  have hr := row_12107
  have hl := log_bounds hr.1
    (by change logScale (12107 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12101) (H := 119344564239773) (u := 94015390733)
    (by norm_num) (by norm_num) hr.1 gap_12107 hl.2
    (by norm_num) upper_reach_12101

theorem upper_reach_12109 : UpperReach 12109 119532596673191 := by
  have hr := row_12109
  have hl := log_bounds hr.1
    (by change logScale (12109 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12107) (H := 119438579630582) (u := 94017042533)
    (by norm_num) (by norm_num) hr.1 gap_12109 hl.2
    (by norm_num) upper_reach_12107

theorem upper_reach_12113 : UpperReach 12113 119626617018583 := by
  have hr := row_12113
  have hl := log_bounds hr.1
    (by change logScale (12113 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12109) (H := 119532596673191) (u := 94020345316)
    (by norm_num) (by norm_num) hr.1 gap_12113 hl.2
    (by norm_num) upper_reach_12109

theorem upper_reach_12119 : UpperReach 12119 119720642316104 := by
  have hr := row_12119
  have hl := log_bounds hr.1
    (by change logScale (12119 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12113) (H := 119626617018583) (u := 94025297445)
    (by norm_num) (by norm_num) hr.1 gap_12119 hl.2
    (by norm_num) upper_reach_12113

#print axioms upper_reach_12119

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
