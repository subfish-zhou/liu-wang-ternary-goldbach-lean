import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper008
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block009

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_2909 : UpperReach 2909 28604382186089 := by
  have hr := row_2909
  have hl := log_bounds hr.1
    (by change logScale (2909 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2903) (H := 28524626539457) (u := 79755646556)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2903

theorem upper_reach_2917 : UpperReach 2917 28684165295835 := by
  have hr := row_2917
  have hl := log_bounds hr.1
    (by change logScale (2917 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2909) (H := 28604382186089) (u := 79783109670)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 41, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2909

theorem upper_reach_2927 : UpperReach 2927 28763982628749 := by
  have hr := row_2927
  have hl := log_bounds hr.1
    (by change logScale (2927 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2917) (H := 28684165295835) (u := 79817332838)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 23, 2, 37, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2917

theorem upper_reach_2939 : UpperReach 2939 28843840875460 := by
  have hr := row_2939
  have hl := log_bounds hr.1
    (by change logScale (2939 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2927) (H := 28763982628749) (u := 79858246635)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 29, 2, 3, 2, 7, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2927

theorem upper_reach_2953 : UpperReach 2953 28923746644324 := by
  have hr := row_2953
  have hl := log_bounds hr.1
    (by change logScale (2953 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2939) (H := 28843840875460) (u := 79905768788)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 17, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2939

theorem upper_reach_2957 : UpperReach 2957 29003665949569 := by
  have hr := row_2957
  have hl := log_bounds hr.1
    (by change logScale (2957 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2953) (H := 28923746644324) (u := 79919305169)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2953

theorem upper_reach_2963 : UpperReach 2963 29083605525092 := by
  have hr := row_2963
  have hl := log_bounds hr.1
    (by change logScale (2963 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2957) (H := 29003665949569) (u := 79939575447)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2957

theorem upper_reach_2969 : UpperReach 2969 29163565329887 := by
  have hr := row_2969
  have hl := log_bounds hr.1
    (by change logScale (2969 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2963) (H := 29083605525092) (u := 79959804719)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2963

theorem upper_reach_2971 : UpperReach 2971 29243531868689 := by
  have hr := row_2971
  have hl := log_bounds hr.1
    (by change logScale (2971 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2969) (H := 29163565329887) (u := 79966538726)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2969

theorem upper_reach_2999 : UpperReach 2999 29323592210523 := by
  have hr := row_2999
  have hl := log_bounds hr.1
    (by change logScale (2999 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2971) (H := 29243531868689) (u := 80060341758)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 13, 2, 3, 2, 11, 2, 19, 2, 3, 2, 29, 2, 7, 2, 3, 2, 41, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2971

theorem upper_reach_3001 : UpperReach 3001 29403659219024 := by
  have hr := row_3001
  have hl := log_bounds hr.1
    (by change logScale (3001 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2999) (H := 29323592210523) (u := 80067008425)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2999

theorem upper_reach_3011 : UpperReach 3011 29483759494356 := by
  have hr := row_3011
  have hl := log_bounds hr.1
    (by change logScale (3011 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3001) (H := 29403659219024) (u := 80100275256)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 31, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3001

theorem upper_reach_3019 : UpperReach 3019 29563886303700 := by
  have hr := row_3019
  have hl := log_bounds hr.1
    (by change logScale (3019 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3011) (H := 29483759494356) (u := 80126809268)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 23, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3011

theorem upper_reach_3023 : UpperReach 3023 29644026353695 := by
  have hr := row_3023
  have hl := log_bounds hr.1
    (by change logScale (3023 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3019) (H := 29563886303700) (u := 80140049919)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3019

theorem upper_reach_3037 : UpperReach 3037 29724212608392 := by
  have hr := row_3037
  have hl := log_bounds hr.1
    (by change logScale (3037 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3023) (H := 29644026353695) (u := 80186254621)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3023

theorem upper_reach_3041 : UpperReach 3041 29804412025316 := by
  have hr := row_3041
  have hl := log_bounds hr.1
    (by change logScale (3041 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3037) (H := 29724212608392) (u := 80199416848)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3037

theorem upper_reach_3049 : UpperReach 3049 29884637714833 := by
  have hr := row_3049
  have hl := log_bounds hr.1
    (by change logScale (3049 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3041) (H := 29804412025316) (u := 80225689441)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 17, 2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3041

theorem upper_reach_3061 : UpperReach 3061 29964902684269 := by
  have hr := row_3061
  have hl := log_bounds hr.1
    (by change logScale (3061 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3049) (H := 29884637714833) (u := 80264969360)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 43, 2, 5, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3049

theorem upper_reach_3067 : UpperReach 3067 30045187235957 := by
  have hr := row_3067
  have hl := log_bounds hr.1
    (by change logScale (3067 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3061) (H := 29964902684269) (u := 80284551612)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3061

theorem upper_reach_3079 : UpperReach 3079 30125510837483 := by
  have hr := row_3079
  have hl := log_bounds hr.1
    (by change logScale (3079 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3067) (H := 30045187235957) (u := 80323601450)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 37, 2, 7, 2, 3, 2, 17, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3067

theorem upper_reach_3083 : UpperReach 3083 30205847421809 := by
  have hr := row_3083
  have hl := log_bounds hr.1
    (by change logScale (3083 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3079) (H := 30125510837483) (u := 80336584250)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3079

theorem upper_reach_3089 : UpperReach 3089 30286203448785 := by
  have hr := row_3089
  have hl := log_bounds hr.1
    (by change logScale (3089 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3083) (H := 30205847421809) (u := 80356026900)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3083

theorem upper_reach_3109 : UpperReach 3109 30366624012932 := by
  have hr := row_3109
  have hl := log_bounds hr.1
    (by change logScale (3109 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3089) (H := 30286203448785) (u := 80420564071)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 5, 2, 19, 2, 3, 2, 7, 2, 29, 2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3089

theorem upper_reach_3119 : UpperReach 3119 30447076690145 := by
  have hr := row_3119
  have hl := log_bounds hr.1
    (by change logScale (3119 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3109) (H := 30366624012932) (u := 80452677137)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3109

#print axioms upper_reach_3119

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
