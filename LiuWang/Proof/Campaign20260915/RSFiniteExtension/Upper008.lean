import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper007
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block008

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_2719 : UpperReach 2719 26698019760444 := by
  have hr := row_2719
  have hl := log_bounds hr.1
    (by change logScale (2719 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2713) (H := 26618939565951) (u := 79080194417)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2713

theorem upper_reach_2729 : UpperReach 2729 26777136665698 := by
  have hr := row_2729
  have hl := log_bounds hr.1
    (by change logScale (2729 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2719) (H := 26698019760444) (u := 79116905178)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2719

theorem upper_reach_2731 : UpperReach 2731 26856260896960 := by
  have hr := row_2731
  have hl := log_bounds hr.1
    (by change logScale (2731 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2729) (H := 26777136665698) (u := 79124231186)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2729

theorem upper_reach_2741 : UpperReach 2741 26935421677970 := by
  have hr := row_2741
  have hl := log_bounds hr.1
    (by change logScale (2741 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2731) (H := 26856260896960) (u := 79160780934)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2731

theorem upper_reach_2749 : UpperReach 2749 27014611602899 := by
  have hr := row_2749
  have hl := log_bounds hr.1
    (by change logScale (2749 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2741) (H := 26935421677970) (u := 79189924853)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 13, 2, 3, 2, 41, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2741

theorem upper_reach_2753 : UpperReach 2753 27093816067997 := by
  have hr := row_2753
  have hl := log_bounds hr.1
    (by change logScale (2753 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2749) (H := 27014611602899) (u := 79204465022)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2749

theorem upper_reach_2767 : UpperReach 2767 27173071257842 := by
  have hr := row_2767
  have hl := log_bounds hr.1
    (by change logScale (2767 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2753) (H := 27093816067997) (u := 79255189769)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 31, 2, 11, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2753

theorem upper_reach_2777 : UpperReach 2777 27252362522762 := by
  have hr := row_2777
  have hl := log_bounds hr.1
    (by change logScale (2777 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2767) (H := 27173071257842) (u := 79291264844)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 17, 2, 47, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2767

theorem upper_reach_2789 : UpperReach 2789 27331696906685 := by
  have hr := row_2789
  have hl := log_bounds hr.1
    (by change logScale (2789 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2777) (H := 27252362522762) (u := 79334383847)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2777

theorem upper_reach_2791 : UpperReach 2791 27411038459067 := by
  have hr := row_2791
  have hl := log_bounds hr.1
    (by change logScale (2791 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2789) (H := 27331696906685) (u := 79341552306)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2789

theorem upper_reach_2797 : UpperReach 2797 27490401486046 := by
  have hr := row_2797
  have hl := log_bounds hr.1
    (by change logScale (2797 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2791) (H := 27411038459067) (u := 79363026903)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2791

theorem upper_reach_2801 : UpperReach 2801 27569778803846 := by
  have hr := row_2801
  have hl := log_bounds hr.1
    (by change logScale (2801 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2797) (H := 27490401486046) (u := 79377317724)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2797

theorem upper_reach_2803 : UpperReach 2803 27649163259405 := by
  have hr := row_2803
  have hl := log_bounds hr.1
    (by change logScale (2803 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2801) (H := 27569778803846) (u := 79384455483)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2801

theorem upper_reach_2819 : UpperReach 2819 27728604634363 := by
  have hr := row_2819
  have hl := log_bounds hr.1
    (by change logScale (2819 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2803) (H := 27649163259405) (u := 79441374882)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 53, 2, 3, 2, 29, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2803

theorem upper_reach_2833 : UpperReach 2833 27808095549408 := by
  have hr := row_2833
  have hl := log_bounds hr.1
    (by change logScale (2833 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2819) (H := 27728604634363) (u := 79490914969)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 19, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2819

theorem upper_reach_2837 : UpperReach 2837 27887600573803 := by
  have hr := row_2837
  have hl := log_bounds hr.1
    (by change logScale (2837 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2833) (H := 27808095549408) (u := 79505024319)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2833

theorem upper_reach_2843 : UpperReach 2843 27967126724966 := by
  have hr := row_2843
  have hl := log_bounds hr.1
    (by change logScale (2843 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2837) (H := 27887600573803) (u := 79526151087)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 17, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2837

theorem upper_reach_2851 : UpperReach 2851 28046680975902 := by
  have hr := row_2851
  have hl := log_bounds hr.1
    (by change logScale (2851 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2843) (H := 27967126724966) (u := 79554250860)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2843

theorem upper_reach_2857 : UpperReach 2857 28126256249971 := by
  have hr := row_2857
  have hl := log_bounds hr.1
    (by change logScale (2857 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2851) (H := 28046680975902) (u := 79575273993)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2851

theorem upper_reach_2861 : UpperReach 2861 28205845514948 := by
  have hr := row_2861
  have hl := log_bounds hr.1
    (by change logScale (2861 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2857) (H := 28126256249971) (u := 79589264901)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2857

theorem upper_reach_2879 : UpperReach 2879 28285497497901 := by
  have hr := row_2879
  have hl := log_bounds hr.1
    (by change logScale (2879 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2861) (H := 28205845514948) (u := 79651982877)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 47, 2, 19, 2, 3, 2, 13, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2861

theorem upper_reach_2887 : UpperReach 2887 28365177229745 := by
  have hr := row_2887
  have hl := log_bounds hr.1
    (by change logScale (2887 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2879) (H := 28285497497901) (u := 79679731768)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 43, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2879

theorem upper_reach_2897 : UpperReach 2897 28444891539770 := by
  have hr := row_2897
  have hl := log_bounds hr.1
    (by change logScale (2897 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2887) (H := 28365177229745) (u := 79714309949)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2887

theorem upper_reach_2903 : UpperReach 2903 28524626539457 := by
  have hr := row_2903
  have hl := log_bounds hr.1
    (by change logScale (2903 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2897) (H := 28444891539770) (u := 79734999611)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2897

#print axioms upper_reach_2903

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
