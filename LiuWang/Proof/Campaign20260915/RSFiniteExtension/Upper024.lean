import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper023
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block024

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_5953 : UpperReach 5953 58759037792237 := by
  have hr := row_5953
  have hl := log_bounds hr.1
    (by change logScale (5953 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5939) (H := 58672121286461) (u := 86916505700)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 13, 2, 3, 2, 5, 2, 19, 2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5939

theorem upper_reach_5981 : UpperReach 5981 58846001222852 := by
  have hr := row_5981
  have hl := log_bounds hr.1
    (by change logScale (5981 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5953) (H := 58759037792237) (u := 86963430539)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 59, 2, 3, 2, 67, 2, 5, 2, 3, 2, 47, 2, 7, 2, 3, 2, 5, 2, 43, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5953

theorem upper_reach_5987 : UpperReach 5987 58932974680206 := by
  have hr := row_5987
  have hl := log_bounds hr.1
    (by change logScale (5987 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5981) (H := 58846001222852) (u := 86973457278)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 31, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5981

theorem upper_reach_6007 : UpperReach 6007 59019981487599 := by
  have hr := row_6007
  have hl := log_bounds hr.1
    (by change logScale (6007 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5987) (H := 58932974680206) (u := 87006807317)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 53, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5987

theorem upper_reach_6011 : UpperReach 6011 59106994951674 := by
  have hr := row_6011
  have hl := log_bounds hr.1
    (by change logScale (6011 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6007) (H := 59019981487599) (u := 87013463999)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6007

theorem upper_reach_6029 : UpperReach 6029 59194038316103 := by
  have hr := row_6029
  have hl := log_bounds hr.1
    (by change logScale (6029 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6011) (H := 59106994951674) (u := 87043364353)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 11, 2, 13, 2, 3, 2, 19, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6011

theorem upper_reach_6037 : UpperReach 6037 59281094940935 := by
  have hr := row_6037
  have hl := log_bounds hr.1
    (by change logScale (6037 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6029) (H := 59194038316103) (u := 87056624756)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 37, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6029

theorem upper_reach_6043 : UpperReach 6043 59368161499543 := by
  have hr := row_6043
  have hl := log_bounds hr.1
    (by change logScale (6043 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6037) (H := 59281094940935) (u := 87066558532)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6037

theorem upper_reach_6047 : UpperReach 6047 59455234675190 := by
  have hr := row_6047
  have hl := log_bounds hr.1
    (by change logScale (6047 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6043) (H := 59368161499543) (u := 87073175571)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6043

theorem upper_reach_6053 : UpperReach 6053 59542317768193 := by
  have hr := row_6053
  have hl := log_bounds hr.1
    (by change logScale (6053 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6047) (H := 59455234675190) (u := 87083092927)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 23, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6047

theorem upper_reach_6067 : UpperReach 6067 59629423963517 := by
  have hr := row_6067
  have hl := log_bounds hr.1
    (by change logScale (6067 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6053) (H := 59542317768193) (u := 87106195248)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 73, 2, 11, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6053

theorem upper_reach_6073 : UpperReach 6073 59716540043520 := by
  have hr := row_6073
  have hl := log_bounds hr.1
    (by change logScale (6073 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6067) (H := 59629423963517) (u := 87116079927)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6067

theorem upper_reach_6079 : UpperReach 6079 59803665998442 := by
  have hr := row_6079
  have hl := log_bounds hr.1
    (by change logScale (6079 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6073) (H := 59716540043520) (u := 87125954846)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 59, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6073

theorem upper_reach_6089 : UpperReach 6089 59890808389922 := by
  have hr := row_6089
  have hl := log_bounds hr.1
    (by change logScale (6089 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6079) (H := 59803665998442) (u := 87142391404)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6079

theorem upper_reach_6091 : UpperReach 6091 59977954065475 := by
  have hr := row_6091
  have hl := log_bounds hr.1
    (by change logScale (6091 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6089) (H := 59890808389922) (u := 87145675477)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6089

theorem upper_reach_6101 : UpperReach 6101 60065116145231 := by
  have hr := row_6101
  have hl := log_bounds hr.1
    (by change logScale (6101 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6091) (H := 59977954065475) (u := 87162079680)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6091

theorem upper_reach_6113 : UpperReach 6113 60152297874576 := by
  have hr := row_6113
  have hl := log_bounds hr.1
    (by change logScale (6113 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6101) (H := 60065116145231) (u := 87181729269)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 17, 2, 3, 2, 31, 2, 41, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6101

theorem upper_reach_6121 : UpperReach 6121 60239492682229 := by
  have hr := row_6121
  have hl := log_bounds hr.1
    (by change logScale (6121 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6113) (H := 60152297874576) (u := 87194807577)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 29, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6113

theorem upper_reach_6131 : UpperReach 6131 60326703813751 := by
  have hr := row_6131
  have hl := log_bounds hr.1
    (by change logScale (6131 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6121) (H := 60239492682229) (u := 87211131446)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6121

theorem upper_reach_6133 : UpperReach 6133 60413918206852 := by
  have hr := row_6133
  have hl := log_bounds hr.1
    (by change logScale (6133 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6131) (H := 60326703813751) (u := 87214393025)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6131

theorem upper_reach_6143 : UpperReach 6143 60501148891908 := by
  have hr := row_6143
  have hl := log_bounds hr.1
    (by change logScale (6143 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6133) (H := 60413918206852) (u := 87230684980)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 17, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6133

theorem upper_reach_6151 : UpperReach 6151 60588392591444 := by
  have hr := row_6151
  have hl := log_bounds hr.1
    (by change logScale (6151 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6143) (H := 60501148891908) (u := 87243699460)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6143

theorem upper_reach_6163 : UpperReach 6163 60675655780998 := by
  have hr := row_6163
  have hl := log_bounds hr.1
    (by change logScale (6163 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6151) (H := 60588392591444) (u := 87263189478)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 47, 2, 3, 2, 61, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6151

theorem upper_reach_6173 : UpperReach 6173 60762935183266 := by
  have hr := row_6173
  have hl := log_bounds hr.1
    (by change logScale (6173 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6163) (H := 60675655780998) (u := 87279402192)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 31, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6163

#print axioms upper_reach_6173

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
