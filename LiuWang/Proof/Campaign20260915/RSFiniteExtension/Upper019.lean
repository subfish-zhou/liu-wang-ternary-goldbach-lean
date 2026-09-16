import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper018
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block019

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_4943 : UpperReach 4943 48435987621323 := by
  have hr := row_4943
  have hl := log_bounds hr.1
    (by change logScale (4943 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4937) (H := 48350930344146) (u := 85057277101)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4937

theorem upper_reach_4951 : UpperReach 4951 48521061069921 := by
  have hr := row_4951
  have hl := log_bounds hr.1
    (by change logScale (4951 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4943) (H := 48435987621323) (u := 85073448522)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4943

theorem upper_reach_4957 : UpperReach 4957 48606146629946 := by
  have hr := row_4957
  have hl := log_bounds hr.1
    (by change logScale (4957 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4951) (H := 48521061069921) (u := 85085559949)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4951

theorem upper_reach_4967 : UpperReach 4967 48691252343141 := by
  have hr := row_4967
  have hl := log_bounds hr.1
    (by change logScale (4967 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4957) (H := 48606146629946) (u := 85105713119)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4957

theorem upper_reach_4969 : UpperReach 4969 48776362082101 := by
  have hr := row_4969
  have hl := log_bounds hr.1
    (by change logScale (4969 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4967) (H := 48691252343141) (u := 85109738884)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4967

theorem upper_reach_4973 : UpperReach 4973 48861479867732 := by
  have hr := row_4973
  have hl := log_bounds hr.1
    (by change logScale (4973 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4969) (H := 48776362082101) (u := 85117785555)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4969

theorem upper_reach_4987 : UpperReach 4987 48946625765832 := by
  have hr := row_4987
  have hl := log_bounds hr.1
    (by change logScale (4987 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4973) (H := 48861479867732) (u := 85145898024)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 13, 2, 17, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4973

theorem upper_reach_4993 : UpperReach 4993 49031783687981 := by
  have hr := row_4993
  have hl := log_bounds hr.1
    (by change logScale (4993 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4987) (H := 48946625765832) (u := 85157922073)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4987

theorem upper_reach_4999 : UpperReach 4999 49116953619739 := by
  have hr := row_4999
  have hl := log_bounds hr.1
    (by change logScale (4999 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4993) (H := 49031783687981) (u := 85169931682)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 19, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4993

theorem upper_reach_5003 : UpperReach 5003 49202131549898 := by
  have hr := row_5003
  have hl := log_bounds hr.1
    (by change logScale (5003 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4999) (H := 49116953619739) (u := 85177930083)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4999

theorem upper_reach_5009 : UpperReach 5009 49287321465676 := by
  have hr := row_5009
  have hl := log_bounds hr.1
    (by change logScale (5009 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5003) (H := 49202131549898) (u := 85189915702)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5003

theorem upper_reach_5011 : UpperReach 5011 49372515373470 := by
  have hr := row_5011
  have hl := log_bounds hr.1
    (by change logScale (5011 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5009) (H := 49287321465676) (u := 85193907718)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5009

theorem upper_reach_5021 : UpperReach 5021 49457729217475 := by
  have hr := row_5021
  have hl := log_bounds hr.1
    (by change logScale (5021 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5011) (H := 49372515373470) (u := 85213843929)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 29, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5011

theorem upper_reach_5023 : UpperReach 5023 49542947043957 := by
  have hr := row_5023
  have hl := log_bounds hr.1
    (by change logScale (5023 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5021) (H := 49457729217475) (u := 85217826406)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5021

theorem upper_reach_5039 : UpperReach 5039 49628196673288 := by
  have hr := row_5039
  have hl := log_bounds hr.1
    (by change logScale (5039 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5023) (H := 49542947043957) (u := 85249629255)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 47, 2, 3, 2, 7, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5023

theorem upper_reach_5051 : UpperReach 5051 49713470088557 := by
  have hr := row_5051
  have hl := log_bounds hr.1
    (by change logScale (5051 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5039) (H := 49628196673288) (u := 85273415193)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 71, 2, 3, 2, 5, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5039

theorem upper_reach_5059 : UpperReach 5059 49798759329744 := by
  have hr := row_5059
  have hl := log_bounds hr.1
    (by change logScale (5059 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5051) (H := 49713470088557) (u := 85289241111)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 31, 2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5051

theorem upper_reach_5077 : UpperReach 5077 49884084087938 := by
  have hr := row_5077
  have hl := log_bounds hr.1
    (by change logScale (5077 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5059) (H := 49798759329744) (u := 85324758118)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 61, 2, 5, 2, 3, 2, 37, 2, 11, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5059

theorem upper_reach_5081 : UpperReach 5081 49969416721698 := by
  have hr := row_5081
  have hl := log_bounds hr.1
    (by change logScale (5081 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5077) (H := 49884084087938) (u := 85332633684)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5077

theorem upper_reach_5087 : UpperReach 5087 50054761157191 := by
  have hr := row_5087
  have hl := log_bounds hr.1
    (by change logScale (5087 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5081) (H := 49969416721698) (u := 85344435417)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5081

theorem upper_reach_5099 : UpperReach 5099 50140129154446 := by
  have hr := row_5099
  have hl := log_bounds hr.1
    (by change logScale (5099 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5087) (H := 50054761157191) (u := 85367997179)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5087

theorem upper_reach_5101 : UpperReach 5101 50225501073270 := by
  have hr := row_5101
  have hl := log_bounds hr.1
    (by change logScale (5101 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5099) (H := 50140129154446) (u := 85371918748)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5099

theorem upper_reach_5107 : UpperReach 5107 50310884747581 := by
  have hr := row_5107
  have hl := log_bounds hr.1
    (by change logScale (5107 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5101) (H := 50225501073270) (u := 85383674235)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5101

theorem upper_reach_5113 : UpperReach 5113 50396280163576 := by
  have hr := row_5113
  have hl := log_bounds hr.1
    (by change logScale (5113 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5107) (H := 50310884747581) (u := 85395415919)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 19, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5107

#print axioms upper_reach_5113

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
