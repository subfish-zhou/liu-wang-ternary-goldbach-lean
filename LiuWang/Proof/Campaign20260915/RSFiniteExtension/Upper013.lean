import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper012
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block013

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_3701 : UpperReach 3701 36387445081969 := by
  have hr := row_3701
  have hl := log_bounds hr.1
    (by change logScale (3701 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3697) (H := 36305281498598) (u := 82163583295)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3697

theorem upper_reach_3709 : UpperReach 3709 36469630257791 := by
  have hr := row_3709
  have hl := log_bounds hr.1
    (by change logScale (3709 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3701) (H := 36387445081969) (u := 82185175746)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3701

theorem upper_reach_3719 : UpperReach 3719 36551842358777 := by
  have hr := row_3719
  have hl := log_bounds hr.1
    (by change logScale (3719 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3709) (H := 36469630257791) (u := 82212100910)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 47, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3709

theorem upper_reach_3727 : UpperReach 3727 36634075947819 := by
  have hr := row_3727
  have hl := log_bounds hr.1
    (by change logScale (3727 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3719) (H := 36551842358777) (u := 82233588966)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 61, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3719

theorem upper_reach_3733 : UpperReach 3733 36716325622655 := by
  have hr := row_3733
  have hl := log_bounds hr.1
    (by change logScale (3733 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3727) (H := 36634075947819) (u := 82249674760)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3727

theorem upper_reach_3739 : UpperReach 3739 36798591357452 := by
  have hr := row_3739
  have hl := log_bounds hr.1
    (by change logScale (3739 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3733) (H := 36716325622655) (u := 82265734721)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 37, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3733

theorem upper_reach_3761 : UpperReach 3761 36880915759084 := by
  have hr := row_3761
  have hl := log_bounds hr.1
    (by change logScale (3761 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3739) (H := 36798591357452) (u := 82324401556)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 19, 2, 5, 2, 3, 2, 23, 2, 11, 2, 3, 2, 5, 2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3739

theorem upper_reach_3767 : UpperReach 3767 36963256101208 := by
  have hr := row_3767
  have hl := log_bounds hr.1
    (by change logScale (3767 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3761) (H := 36880915759084) (u := 82340342048)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 53, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3761

theorem upper_reach_3769 : UpperReach 3769 37045601751188 := by
  have hr := row_3769
  have hl := log_bounds hr.1
    (by change logScale (3769 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3767) (H := 36963256101208) (u := 82345649904)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3767

theorem upper_reach_3779 : UpperReach 3779 37127973898268 := by
  have hr := row_3779
  have hl := log_bounds hr.1
    (by change logScale (3779 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3769) (H := 37045601751188) (u := 82372147004)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3769

theorem upper_reach_3793 : UpperReach 3793 37210383023732 := by
  have hr := row_3793
  have hl := log_bounds hr.1
    (by change logScale (3793 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3779) (H := 37127973898268) (u := 82409125388)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 19, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3779

theorem upper_reach_3797 : UpperReach 3797 37292802689381 := by
  have hr := row_3797
  have hl := log_bounds hr.1
    (by change logScale (3797 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3793) (H := 37210383023732) (u := 82419665573)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3793

theorem upper_reach_3803 : UpperReach 3803 37375238144507 := by
  have hr := row_3803
  have hl := log_bounds hr.1
    (by change logScale (3803 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3797) (H := 37292802689381) (u := 82435455050)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 29, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3797

theorem upper_reach_3821 : UpperReach 3821 37457720819028 := by
  have hr := row_3821
  have hl := log_bounds hr.1
    (by change logScale (3821 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3803) (H := 37375238144507) (u := 82482674445)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 13, 2, 37, 2, 3, 2, 5, 2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3803

theorem upper_reach_3823 : UpperReach 3823 37540208726412 := by
  have hr := row_3823
  have hl := log_bounds hr.1
    (by change logScale (3823 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3821) (H := 37457720819028) (u := 82487907308)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3821

theorem upper_reach_3833 : UpperReach 3833 37622722757113 := by
  have hr := row_3833
  have hl := log_bounds hr.1
    (by change logScale (3833 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3823) (H := 37540208726412) (u := 82514030625)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 43, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3823

theorem upper_reach_3847 : UpperReach 3847 37705273246187 := by
  have hr := row_3847
  have hl := log_bounds hr.1
    (by change logScale (3847 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3833) (H := 37622722757113) (u := 82550488998)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 11, 2, 23, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3833

theorem upper_reach_3851 : UpperReach 3851 37787834127572 := by
  have hr := row_3851
  have hl := log_bounds hr.1
    (by change logScale (3851 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3847) (H := 37705273246187) (u := 82560881309)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3847

theorem upper_reach_3853 : UpperReach 3853 37870400201065 := by
  have hr := row_3853
  have hl := log_bounds hr.1
    (by change logScale (3853 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3851) (H := 37787834127572) (u := 82566073417)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3851

theorem upper_reach_3863 : UpperReach 3863 37952992194739 := by
  have hr := row_3863
  have hl := log_bounds hr.1
    (by change logScale (3863 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3853) (H := 37870400201065) (u := 82591993598)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 17, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3853

theorem upper_reach_3877 : UpperReach 3877 38035620364163 := by
  have hr := row_3877
  have hl := log_bounds hr.1
    (by change logScale (3877 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3863) (H := 37952992194739) (u := 82628169348)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 53, 2, 7, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3863

theorem upper_reach_3881 : UpperReach 3881 38118258845524 := by
  have hr := row_3881
  have hl := log_bounds hr.1
    (by change logScale (3881 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3877) (H := 38035620364163) (u := 82638481285)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3877

theorem upper_reach_3889 : UpperReach 3889 38200917918912 := by
  have hr := row_3889
  have hl := log_bounds hr.1
    (by change logScale (3889 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3881) (H := 38118258845524) (u := 82659073312)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3881

theorem upper_reach_3907 : UpperReach 3907 38283623169909 := by
  have hr := row_3907
  have hl := log_bounds hr.1
    (by change logScale (3907 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3889) (H := 38200917918912) (u := 82705250921)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 17, 2, 5, 2, 3, 2, 7, 2, 47, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3889

#print axioms upper_reach_3907

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
