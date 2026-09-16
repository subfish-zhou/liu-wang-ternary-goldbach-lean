import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper002
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_1787 : UpperReach 1787 17435468008301 := by
  have hr := row_1787
  have hl := log_bounds hr.1
    (by change logScale (1787 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1783) (H := 17360585073100) (u := 74882935125)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1783

theorem upper_reach_1789 : UpperReach 1789 17510362129186 := by
  have hr := row_1789
  have hl := log_bounds hr.1
    (by change logScale (1789 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1787) (H := 17435468008301) (u := 74894120809)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1787

theorem upper_reach_1801 : UpperReach 1801 17585323102687 := by
  have hr := row_1801
  have hl := log_bounds hr.1
    (by change logScale (1801 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1789) (H := 17510362129186) (u := 74960973425)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1789

theorem upper_reach_1811 : UpperReach 1811 17660339447315 := by
  have hr := row_1811
  have hl := log_bounds hr.1
    (by change logScale (1811 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1801) (H := 17585323102687) (u := 75016344552)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1801

theorem upper_reach_1823 : UpperReach 1823 17735421835111 := by
  have hr := row_1823
  have hl := log_bounds hr.1
    (by change logScale (1823 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1811) (H := 17660339447315) (u := 75082387720)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 23, 2, 17, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1811

theorem upper_reach_1831 : UpperReach 1831 17810548010607 := by
  have hr := row_1831
  have hl := log_bounds hr.1
    (by change logScale (1831 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1823) (H := 17735421835111) (u := 75126175420)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 31, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1823

theorem upper_reach_1847 : UpperReach 1847 17885761190458 := by
  have hr := row_1847
  have hl := log_bounds hr.1
    (by change logScale (1847 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1831) (H := 17810548010607) (u := 75213179775)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 19, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1831

theorem upper_reach_1861 : UpperReach 1861 17961049883074 := by
  have hr := row_1861
  have hl := log_bounds hr.1
    (by change logScale (1861 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1847) (H := 17885761190458) (u := 75288692540)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 43, 2, 3, 2, 17, 2, 5, 2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1847

theorem upper_reach_1867 : UpperReach 1867 18036370764559 := by
  have hr := row_1867
  have hl := log_bounds hr.1
    (by change logScale (1867 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1861) (H := 17961049883074) (u := 75320881409)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1861

theorem upper_reach_1871 : UpperReach 1871 18111713047871 := by
  have hr := row_1871
  have hl := log_bounds hr.1
    (by change logScale (1871 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1867) (H := 18036370764559) (u := 75342283236)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1867

theorem upper_reach_1873 : UpperReach 1873 18187066014945 := by
  have hr := row_1873
  have hl := log_bounds hr.1
    (by change logScale (1873 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1871) (H := 18111713047871) (u := 75352966998)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1871

theorem upper_reach_1877 : UpperReach 1877 18262440315360 := by
  have hr := row_1877
  have hl := log_bounds hr.1
    (by change logScale (1877 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1873) (H := 18187066014945) (u := 75374300339)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1873

theorem upper_reach_1879 : UpperReach 1879 18337825265404 := by
  have hr := row_1879
  have hl := log_bounds hr.1
    (by change logScale (1879 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1877) (H := 18262440315360) (u := 75384949968)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1877

theorem upper_reach_1889 : UpperReach 1889 18413263294129 := by
  have hr := row_1889
  have hl := log_bounds hr.1
    (by change logScale (1889 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1879) (H := 18337825265404) (u := 75438028649)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1879

theorem upper_reach_1901 : UpperReach 1901 18488764647603 := by
  have hr := row_1901
  have hl := log_bounds hr.1
    (by change logScale (1901 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1889) (H := 18413263294129) (u := 75501353398)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 31, 2, 3, 2, 5, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1889

theorem upper_reach_1907 : UpperReach 1907 18564297513708 := by
  have hr := row_1907
  have hl := log_bounds hr.1
    (by change logScale (1907 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1901) (H := 18488764647603) (u := 75532866029)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1901

theorem upper_reach_1913 : UpperReach 1913 18639861793452 := by
  have hr := row_1913
  have hl := log_bounds hr.1
    (by change logScale (1913 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1907) (H := 18564297513708) (u := 75564279668)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 23, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1907

theorem upper_reach_1931 : UpperReach 1931 18715519726326 := by
  have hr := row_1931
  have hl := log_bounds hr.1
    (by change logScale (1931 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1913) (H := 18639861793452) (u := 75657932798)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 19, 2, 17, 2, 3, 2, 5, 2, 41, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1913

theorem upper_reach_1933 : UpperReach 1933 18791188011168 := by
  have hr := row_1933
  have hl := log_bounds hr.1
    (by change logScale (1933 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1931) (H := 18715519726326) (u := 75668284766)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1931

theorem upper_reach_1949 : UpperReach 1949 18866938728213 := by
  have hr := row_1949
  have hl := log_bounds hr.1
    (by change logScale (1949 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1933) (H := 18791188011168) (u := 75750716969)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 13, 2, 7, 2, 3, 2, 29, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1933

theorem upper_reach_1951 : UpperReach 1951 18942699701669 := by
  have hr := row_1951
  have hl := log_bounds hr.1
    (by change logScale (1951 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1949) (H := 18866938728213) (u := 75760973380)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1949

theorem upper_reach_1973 : UpperReach 1973 19018572806779 := by
  have hr := row_1973
  have hl := log_bounds hr.1
    (by change logScale (1973 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1951) (H := 18942699701669) (u := 75873105034)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 19, 2, 3, 2, 37, 2, 13, 2, 3, 2, 7, 2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1951

theorem upper_reach_1979 : UpperReach 1979 19094476276284 := by
  have hr := row_1979
  have hl := log_bounds hr.1
    (by change logScale (1979 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1973) (H := 19018572806779) (u := 75903469429)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1973

theorem upper_reach_1987 : UpperReach 1987 19170420088759 := by
  have hr := row_1987
  have hl := log_bounds hr.1
    (by change logScale (1987 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1979) (H := 19094476276284) (u := 75943812399)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1979

#print axioms upper_reach_1987

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
