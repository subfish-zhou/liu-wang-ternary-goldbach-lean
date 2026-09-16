import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper003
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_1993 : UpperReach 1993 19246394052011 := by
  have hr := row_1993
  have hl := log_bounds hr.1
    (by change logScale (1993 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1987) (H := 19170420088759) (u := 75973963176)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1987

theorem upper_reach_1997 : UpperReach 1997 19322388065395 := by
  have hr := row_1997
  have hl := log_bounds hr.1
    (by change logScale (1997 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1993) (H := 19246394052011) (u := 75994013308)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1993

theorem upper_reach_1999 : UpperReach 1999 19398392088789 := by
  have hr := row_1999
  have hl := log_bounds hr.1
    (by change logScale (1999 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1997) (H := 19322388065395) (u := 76004023318)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1997

theorem upper_reach_2003 : UpperReach 2003 19474416102195 := by
  have hr := row_2003
  have hl := log_bounds hr.1
    (by change logScale (2003 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1999) (H := 19398392088789) (u := 76024013330)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1999

theorem upper_reach_2011 : UpperReach 2011 19550479976142 := by
  have hr := row_2011
  have hl := log_bounds hr.1
    (by change logScale (2011 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2003) (H := 19474416102195) (u := 76063873871)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2003

theorem upper_reach_2017 : UpperReach 2017 19626573641571 := by
  have hr := row_2017
  have hl := log_bounds hr.1
    (by change logScale (2017 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2011) (H := 19550479976142) (u := 76093665353)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2011

theorem upper_reach_2027 : UpperReach 2027 19702716763085 := by
  have hr := row_2027
  have hl := log_bounds hr.1
    (by change logScale (2027 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2017) (H := 19626573641571) (u := 76143121438)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 43, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2017

theorem upper_reach_2029 : UpperReach 2029 19778869746533 := by
  have hr := row_2029
  have hl := log_bounds hr.1
    (by change logScale (2029 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2027) (H := 19702716763085) (u := 76152983372)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2027

theorem upper_reach_2039 : UpperReach 2039 19855071894288 := by
  have hr := row_2039
  have hl := log_bounds hr.1
    (by change logScale (2039 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2029) (H := 19778869746533) (u := 76202147679)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 19, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2029

theorem upper_reach_2053 : UpperReach 2053 19931342468505 := by
  have hr := row_2053
  have hl := log_bounds hr.1
    (by change logScale (2053 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2039) (H := 19855071894288) (u := 76270574141)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 13, 2, 3, 2, 5, 2, 23, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2039

theorem upper_reach_2063 : UpperReach 2063 20007661633683 := by
  have hr := row_2063
  have hl := log_bounds hr.1
    (by change logScale (2063 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2053) (H := 19931342468505) (u := 76319165102)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 29, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2053

theorem upper_reach_2069 : UpperReach 2069 20084009840507 := by
  have hr := row_2069
  have hl := log_bounds hr.1
    (by change logScale (2069 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2063) (H := 20007661633683) (u := 76348206748)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2063

theorem upper_reach_2081 : UpperReach 2081 20160415878818 := by
  have hr := row_2081
  have hl := log_bounds hr.1
    (by change logScale (2081 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2069) (H := 20084009840507) (u := 76406038235)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 19, 2, 3, 2, 5, 2, 31, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2069

theorem upper_reach_2083 : UpperReach 2083 20236831523278 := by
  have hr := row_2083
  have hl := log_bounds hr.1
    (by change logScale (2083 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2081) (H := 20160415878818) (u := 76415644384)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2081

theorem upper_reach_2087 : UpperReach 2087 20313266352396 := by
  have hr := row_2087
  have hl := log_bounds hr.1
    (by change logScale (2087 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2083) (H := 20236831523278) (u := 76434829042)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2083

theorem upper_reach_2089 : UpperReach 2089 20389710760058 := by
  have hr := row_2089
  have hl := log_bounds hr.1
    (by change logScale (2089 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2087) (H := 20313266352396) (u := 76444407586)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2087

theorem upper_reach_2099 : UpperReach 2099 20466202923303 := by
  have hr := row_2099
  have hl := log_bounds hr.1
    (by change logScale (2099 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2089) (H := 20389710760058) (u := 76492163169)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2089

theorem upper_reach_2111 : UpperReach 2111 20542752093828 := by
  have hr := row_2111
  have hl := log_bounds hr.1
    (by change logScale (2111 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2099) (H := 20466202923303) (u := 76549170449)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2099

theorem upper_reach_2113 : UpperReach 2113 20619310734051 := by
  have hr := row_2113
  have hl := log_bounds hr.1
    (by change logScale (2113 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2111) (H := 20542752093828) (u := 76558640147)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2111

theorem upper_reach_2129 : UpperReach 2129 20695944810747 := by
  have hr := row_2129
  have hl := log_bounds hr.1
    (by change logScale (2129 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2113) (H := 20619310734051) (u := 76634076620)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 29, 2, 13, 2, 3, 2, 11, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2113

theorem upper_reach_2131 : UpperReach 2131 20772588277115 := by
  have hr := row_2131
  have hl := log_bounds hr.1
    (by change logScale (2131 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2129) (H := 20695944810747) (u := 76643466292)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2129

theorem upper_reach_2137 : UpperReach 2137 20849259859715 := by
  have hr := row_2137
  have hl := log_bounds hr.1
    (by change logScale (2137 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2131) (H := 20772588277115) (u := 76671582524)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2131

theorem upper_reach_2141 : UpperReach 2141 20925950142648 := by
  have hr := row_2141
  have hl := log_bounds hr.1
    (by change logScale (2141 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2137) (H := 20849259859715) (u := 76690282857)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2137

theorem upper_reach_2143 : UpperReach 2143 21002649762650 := by
  have hr := row_2143
  have hl := log_bounds hr.1
    (by change logScale (2143 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2141) (H := 20925950142648) (u := 76699619926)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2141

#print axioms upper_reach_2143

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
