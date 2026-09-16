import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper013
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block014

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_3911 : UpperReach 3911 38366338653703 := by
  have hr := row_3911
  have hl := log_bounds hr.1
    (by change logScale (3911 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3907) (H := 38283623169909) (u := 82715483718)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3907

theorem upper_reach_3917 : UpperReach 3917 38449069467087 := by
  have hr := row_3917
  have hl := log_bounds hr.1
    (by change logScale (3917 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3911) (H := 38366338653703) (u := 82730813308)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3911

theorem upper_reach_3919 : UpperReach 3919 38531805385116 := by
  have hr := row_3919
  have hl := log_bounds hr.1
    (by change logScale (3919 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3917) (H := 38449069467087) (u := 82735917953)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3917

theorem upper_reach_3923 : UpperReach 3923 38614551504625 := by
  have hr := row_3923
  have hl := log_bounds hr.1
    (by change logScale (3923 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3919) (H := 38531805385116) (u := 82746119433)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3919

theorem upper_reach_3929 : UpperReach 3929 38697312906867 := by
  have hr := row_3929
  have hl := log_bounds hr.1
    (by change logScale (3929 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3923) (H := 38614551504625) (u := 82761402166)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3923

theorem upper_reach_3931 : UpperReach 3931 38780079398168 := by
  have hr := row_3931
  have hl := log_bounds hr.1
    (by change logScale (3931 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3929) (H := 38697312906867) (u := 82766491225)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3929

theorem upper_reach_3943 : UpperReach 3943 38862876369554 := by
  have hr := row_3943
  have hl := log_bounds hr.1
    (by change logScale (3943 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3931) (H := 38780079398168) (u := 82796971310)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 31, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3931

theorem upper_reach_3947 : UpperReach 3947 38945683480358 := by
  have hr := row_3947
  have hl := log_bounds hr.1
    (by change logScale (3947 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3943) (H := 38862876369554) (u := 82807110728)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3943

theorem upper_reach_3967 : UpperReach 3967 39028541134610 := by
  have hr := row_3967
  have hl := log_bounds hr.1
    (by change logScale (3967 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3947) (H := 38945683480358) (u := 82857654176)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 59, 2, 5, 2, 3, 2, 37, 2, 17, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3947

theorem upper_reach_3989 : UpperReach 3989 39111454093176 := by
  have hr := row_3989
  have hl := log_bounds hr.1
    (by change logScale (3989 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3967) (H := 39028541134610) (u := 82912958490)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 29, 2, 3, 2, 41, 2, 23, 2, 3, 2, 7, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3967

theorem upper_reach_4001 : UpperReach 4001 39194397089311 := by
  have hr := row_4001
  have hl := log_bounds hr.1
    (by change logScale (4001 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3989) (H := 39111454093176) (u := 82942996059)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3989

theorem upper_reach_4003 : UpperReach 4003 39277345082948 := by
  have hr := row_4003
  have hl := log_bounds hr.1
    (by change logScale (4003 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4001) (H := 39194397089311) (u := 82947993561)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4001

theorem upper_reach_4007 : UpperReach 4007 39360303064101 := by
  have hr := row_4007
  have hl := log_bounds hr.1
    (by change logScale (4007 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4003) (H := 39277345082948) (u := 82957981077)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4003

theorem upper_reach_4013 : UpperReach 4013 39443276007851 := by
  have hr := row_4013
  have hl := log_bounds hr.1
    (by change logScale (4013 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4007) (H := 39360303064101) (u := 82972943674)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 19, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4007

theorem upper_reach_4019 : UpperReach 4019 39526263891842 := by
  have hr := row_4019
  have hl := log_bounds hr.1
    (by change logScale (4019 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4013) (H := 39443276007851) (u := 82987883915)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4013

theorem upper_reach_4021 : UpperReach 4021 39609256750958 := by
  have hr := row_4021
  have hl := log_bounds hr.1
    (by change logScale (4021 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4019) (H := 39526263891842) (u := 82992859040)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4019

theorem upper_reach_4027 : UpperReach 4027 39692264520613 := by
  have hr := row_4027
  have hl := log_bounds hr.1
    (by change logScale (4027 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4021) (H := 39609256750958) (u := 83007769579)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4021

theorem upper_reach_4049 : UpperReach 4049 39775326772820 := by
  have hr := row_4049
  have hl := log_bounds hr.1
    (by change logScale (4049 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4027) (H := 39692264520613) (u := 83062252131)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 29, 2, 37, 2, 3, 2, 11, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4027

theorem upper_reach_4051 : UpperReach 4051 39858393963299 := by
  have hr := row_4051
  have hl := log_bounds hr.1
    (by change logScale (4051 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4049) (H := 39775326772820) (u := 83067190403)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4049

theorem upper_reach_4057 : UpperReach 4057 39941475953978 := by
  have hr := row_4057
  have hl := log_bounds hr.1
    (by change logScale (4057 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4051) (H := 39858393963299) (u := 83081990603)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4051

theorem upper_reach_4073 : UpperReach 4073 40024597305101 := by
  have hr := row_4073
  have hl := log_bounds hr.1
    (by change logScale (4073 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4057) (H := 39941475953978) (u := 83121351047)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 31, 2, 17, 2, 3, 2, 7, 2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4057

theorem upper_reach_4079 : UpperReach 4079 40107733376541 := by
  have hr := row_4079
  have hl := log_bounds hr.1
    (by change logScale (4079 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4073) (H := 40024597305101) (u := 83136071364)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4073

theorem upper_reach_4091 : UpperReach 4091 40190898823767 := by
  have hr := row_4091
  have hl := log_bounds hr.1
    (by change logScale (4091 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4079) (H := 40107733376541) (u := 83165447150)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 5, 2, 61, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4079

theorem upper_reach_4093 : UpperReach 4093 40274069158579 := by
  have hr := row_4093
  have hl := log_bounds hr.1
    (by change logScale (4093 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4091) (H := 40190898823767) (u := 83170334736)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4091

#print axioms upper_reach_4093

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
