import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper032
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block033

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_7883 : UpperReach 7883 77853562839042 := by
  have hr := row_7883
  have hl := log_bounds hr.1
    (by change logScale (7883 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7879) (H := 77763838200787) (u := 89724638179)
    (by norm_num) (by norm_num) hr.1 gap_7883 hl.2
    (by norm_num) upper_reach_7879

theorem upper_reach_7901 : UpperReach 7901 77943310285213 := by
  have hr := row_7901
  have hl := log_bounds hr.1
    (by change logScale (7901 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7883) (H := 77853562839042) (u := 89747446095)
    (by norm_num) (by norm_num) hr.1 gap_7901 hl.2
    (by norm_num) upper_reach_7883

theorem upper_reach_7907 : UpperReach 7907 78033065322478 := by
  have hr := row_7907
  have hl := log_bounds hr.1
    (by change logScale (7907 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7901) (H := 77943310285213) (u := 89755037189)
    (by norm_num) (by norm_num) hr.1 gap_7907 hl.2
    (by norm_num) upper_reach_7901

theorem upper_reach_7919 : UpperReach 7919 78122835524664 := by
  have hr := row_7919
  have hl := log_bounds hr.1
    (by change logScale (7919 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7907) (H := 78033065322478) (u := 89770202110)
    (by norm_num) (by norm_num) hr.1 gap_7919 hl.2
    (by norm_num) upper_reach_7907

theorem upper_reach_7927 : UpperReach 7927 78212615824037 := by
  have hr := row_7927
  have hl := log_bounds hr.1
    (by change logScale (7927 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7919) (H := 78122835524664) (u := 89780299297)
    (by norm_num) (by norm_num) hr.1 gap_7927 hl.2
    (by norm_num) upper_reach_7919

theorem upper_reach_7933 : UpperReach 7933 78302403689614 := by
  have hr := row_7933
  have hl := log_bounds hr.1
    (by change logScale (7933 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7927) (H := 78212615824037) (u := 89787865501)
    (by norm_num) (by norm_num) hr.1 gap_7933 hl.2
    (by norm_num) upper_reach_7927

theorem upper_reach_7937 : UpperReach 7937 78392196596149 := by
  have hr := row_7937
  have hl := log_bounds hr.1
    (by change logScale (7937 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7933) (H := 78302403689614) (u := 89792906459)
    (by norm_num) (by norm_num) hr.1 gap_7937 hl.2
    (by norm_num) upper_reach_7933

theorem upper_reach_7949 : UpperReach 7949 78482004610329 := by
  have hr := row_7949
  have hl := log_bounds hr.1
    (by change logScale (7949 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7937) (H := 78392196596149) (u := 89808014104)
    (by norm_num) (by norm_num) hr.1 gap_7949 hl.2
    (by norm_num) upper_reach_7937

theorem upper_reach_7951 : UpperReach 7951 78571815140232 := by
  have hr := row_7951
  have hl := log_bounds hr.1
    (by change logScale (7951 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7949) (H := 78482004610329) (u := 89810529827)
    (by norm_num) (by norm_num) hr.1 gap_7951 hl.2
    (by norm_num) upper_reach_7949

theorem upper_reach_7963 : UpperReach 7963 78661640751199 := by
  have hr := row_7963
  have hl := log_bounds hr.1
    (by change logScale (7963 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7951) (H := 78571815140232) (u := 89825610891)
    (by norm_num) (by norm_num) hr.1 gap_7963 hl.2
    (by norm_num) upper_reach_7951

theorem upper_reach_7993 : UpperReach 7993 78751503965620 := by
  have hr := row_7993
  have hl := log_bounds hr.1
    (by change logScale (7993 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7963) (H := 78661640751199) (u := 89863214345)
    (by norm_num) (by norm_num) hr.1 gap_7993 hl.2
    (by norm_num) upper_reach_7963

theorem upper_reach_8009 : UpperReach 8009 78841387177547 := by
  have hr := row_8009
  have hl := log_bounds hr.1
    (by change logScale (8009 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7993) (H := 78751503965620) (u := 89883211851)
    (by norm_num) (by norm_num) hr.1 gap_8009 hl.2
    (by norm_num) upper_reach_7993

theorem upper_reach_8011 : UpperReach 8011 78931272886353 := by
  have hr := row_8011
  have hl := log_bounds hr.1
    (by change logScale (8011 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 8009) (H := 78841387177547) (u := 89885708730)
    (by norm_num) (by norm_num) hr.1 gap_8011 hl.2
    (by norm_num) upper_reach_8009

theorem upper_reach_8017 : UpperReach 8017 79021166082058 := by
  have hr := row_8017
  have hl := log_bounds hr.1
    (by change logScale (8017 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 8011) (H := 78931272886353) (u := 89893195629)
    (by norm_num) (by norm_num) hr.1 gap_8017 hl.2
    (by norm_num) upper_reach_8011

theorem upper_reach_8039 : UpperReach 8039 79111086681866 := by
  have hr := row_8039
  have hl := log_bounds hr.1
    (by change logScale (8039 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 8017) (H := 79021166082058) (u := 89920599732)
    (by norm_num) (by norm_num) hr.1 gap_8039 hl.2
    (by norm_num) upper_reach_8017

theorem upper_reach_8053 : UpperReach 8053 79201024681628 := by
  have hr := row_8053
  have hl := log_bounds hr.1
    (by change logScale (8053 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 8039) (H := 79111086681866) (u := 89937999686)
    (by norm_num) (by norm_num) hr.1 gap_8053 hl.2
    (by norm_num) upper_reach_8039

theorem upper_reach_8059 : UpperReach 8059 79290970129255 := by
  have hr := row_8059
  have hl := log_bounds hr.1
    (by change logScale (8059 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 8053) (H := 79201024681628) (u := 89945447551)
    (by norm_num) (by norm_num) hr.1 gap_8059 hl.2
    (by norm_num) upper_reach_8053

theorem upper_reach_8069 : UpperReach 8069 79380927977678 := by
  have hr := row_8069
  have hl := log_bounds hr.1
    (by change logScale (8069 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 8059) (H := 79290970129255) (u := 89957848347)
    (by norm_num) (by norm_num) hr.1 gap_8069 hl.2
    (by norm_num) upper_reach_8059

theorem upper_reach_8081 : UpperReach 8081 79470900686785 := by
  have hr := row_8081
  have hl := log_bounds hr.1
    (by change logScale (8081 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 8069) (H := 79380927977678) (u := 89972709031)
    (by norm_num) (by norm_num) hr.1 gap_8081 hl.2
    (by norm_num) upper_reach_8069

theorem upper_reach_8087 : UpperReach 8087 79560880817960 := by
  have hr := row_8087
  have hl := log_bounds hr.1
    (by change logScale (8087 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 8081) (H := 79470900686785) (u := 89980131099)
    (by norm_num) (by norm_num) hr.1 gap_8087 hl.2
    (by norm_num) upper_reach_8081

theorem upper_reach_8089 : UpperReach 8089 79650863421934 := by
  have hr := row_8089
  have hl := log_bounds hr.1
    (by change logScale (8089 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 8087) (H := 79560880817960) (u := 89982603898)
    (by norm_num) (by norm_num) hr.1 gap_8089 hl.2
    (by norm_num) upper_reach_8087

theorem upper_reach_8093 : UpperReach 8093 79740850969673 := by
  have hr := row_8093
  have hl := log_bounds hr.1
    (by change logScale (8093 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 8089) (H := 79650863421934) (u := 89987547663)
    (by norm_num) (by norm_num) hr.1 gap_8093 hl.2
    (by norm_num) upper_reach_8089

theorem upper_reach_8101 : UpperReach 8101 79830848397616 := by
  have hr := row_8101
  have hl := log_bounds hr.1
    (by change logScale (8101 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 8093) (H := 79740850969673) (u := 89997427867)
    (by norm_num) (by norm_num) hr.1 gap_8101 hl.2
    (by norm_num) upper_reach_8093

theorem upper_reach_8111 : UpperReach 8111 79920858162101 := by
  have hr := row_8111
  have hl := log_bounds hr.1
    (by change logScale (8111 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 8101) (H := 79830848397616) (u := 90009764409)
    (by norm_num) (by norm_num) hr.1 gap_8111 hl.2
    (by norm_num) upper_reach_8101

#print axioms upper_reach_8111

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
