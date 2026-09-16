import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper017
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block018

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_4723 : UpperReach 4723 46399694587269 := by
  have hr := row_4723
  have hl := log_bounds hr.1
    (by change logScale (4723 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4721) (H := 46315092592526) (u := 84601994667)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4721

theorem upper_reach_4729 : UpperReach 4729 46484309277740 := by
  have hr := row_4729
  have hl := log_bounds hr.1
    (by change logScale (4729 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4723) (H := 46399694587269) (u := 84614690395)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 29, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4723

theorem upper_reach_4733 : UpperReach 4733 46568932423083 := by
  have hr := row_4733
  have hl := log_bounds hr.1
    (by change logScale (4733 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4729) (H := 46484309277740) (u := 84623145267)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4729

theorem upper_reach_4751 : UpperReach 4751 46653593527139 := by
  have hr := row_4751
  have hl := log_bounds hr.1
    (by change logScale (4751 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4733) (H := 46568932423083) (u := 84661103980)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 47, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4733

theorem upper_reach_4759 : UpperReach 4759 46738271455595 := by
  have hr := row_4759
  have hl := log_bounds hr.1
    (by change logScale (4759 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4751) (H := 46653593527139) (u := 84677928380)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 67, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4751

theorem upper_reach_4783 : UpperReach 4783 46822999688076 := by
  have hr := row_4783
  have hl := log_bounds hr.1
    (by change logScale (4783 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4759) (H := 46738271455595) (u := 84728232405)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 5, 2, 3, 2, 19, 2, 13, 2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4759

theorem upper_reach_4787 : UpperReach 4787 46907736280014 := by
  have hr := row_4787
  have hl := log_bounds hr.1
    (by change logScale (4787 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4783) (H := 46822999688076) (u := 84736591862)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4783

theorem upper_reach_4789 : UpperReach 4789 46992477049062 := by
  have hr := row_4789
  have hl := log_bounds hr.1
    (by change logScale (4789 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4787) (H := 46907736280014) (u := 84740768972)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4787

theorem upper_reach_4793 : UpperReach 4793 47077226167098 := by
  have hr := row_4793
  have hl := log_bounds hr.1
    (by change logScale (4793 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4789) (H := 46992477049062) (u := 84749117960)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4789

theorem upper_reach_4799 : UpperReach 4799 47161987795561 := by
  have hr := row_4799
  have hl := log_bounds hr.1
    (by change logScale (4799 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4793) (H := 47077226167098) (u := 84761628387)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4793

theorem upper_reach_4801 : UpperReach 4801 47246753590691 := by
  have hr := row_4801
  have hl := log_bounds hr.1
    (by change logScale (4801 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4799) (H := 47161987795561) (u := 84765795054)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4799

theorem upper_reach_4813 : UpperReach 4813 47331544349428 := by
  have hr := row_4813
  have hl := log_bounds hr.1
    (by change logScale (4813 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4801) (H := 47246753590691) (u := 84790758661)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 11, 2, 3, 2, 17, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4801

theorem upper_reach_4817 : UpperReach 4817 47416343415539 := by
  have hr := row_4817
  have hl := log_bounds hr.1
    (by change logScale (4817 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4813) (H := 47331544349428) (u := 84799066035)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4813

theorem upper_reach_4831 : UpperReach 4831 47501171503229 := by
  have hr := row_4831
  have hl := log_bounds hr.1
    (by change logScale (4831 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4817) (H := 47416343415539) (u := 84828087614)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 61, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4817

theorem upper_reach_4861 : UpperReach 4861 47586061497844 := by
  have hr := row_4861
  have hl := log_bounds hr.1
    (by change logScale (4861 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4831) (H := 47501171503229) (u := 84889994539)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 7, 2, 3, 2, 47, 2, 29, 2, 3, 2, 37, 2, 13, 2, 3, 2, 23, 2, 5, 2, 3, 2, 43, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4831

theorem upper_reach_4871 : UpperReach 4871 47670972043226 := by
  have hr := row_4871
  have hl := log_bounds hr.1
    (by change logScale (4871 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4861) (H := 47586061497844) (u := 84910545306)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 31, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4861

theorem upper_reach_4877 : UpperReach 4877 47755894898827 := by
  have hr := row_4877
  have hl := log_bounds hr.1
    (by change logScale (4877 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4871) (H := 47670972043226) (u := 84922855525)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4871

theorem upper_reach_4889 : UpperReach 4889 47840842329497 := by
  have hr := row_4889
  have hl := log_bounds hr.1
    (by change logScale (4889 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4877) (H := 47755894898827) (u := 84947430594)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 19, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4877

theorem upper_reach_4903 : UpperReach 4903 47925818354958 := by
  have hr := row_4903
  have hl := log_bounds hr.1
    (by change logScale (4903 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4889) (H := 47840842329497) (u := 84976025385)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 67, 2, 3, 2, 5, 2, 59, 2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4889

theorem upper_reach_4909 : UpperReach 4909 48010806610343 := by
  have hr := row_4909
  have hl := log_bounds hr.1
    (by change logScale (4909 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4903) (H := 47925818354958) (u := 84988255309)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4903

theorem upper_reach_4919 : UpperReach 4919 48095815215755 := by
  have hr := row_4919
  have hl := log_bounds hr.1
    (by change logScale (4919 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4909) (H := 48010806610343) (u := 85008605336)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 17, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4909

theorem upper_reach_4931 : UpperReach 4931 48180848186662 := by
  have hr := row_4931
  have hl := log_bounds hr.1
    (by change logScale (4931 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4919) (H := 48095815215755) (u := 85032970831)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4919

theorem upper_reach_4933 : UpperReach 4933 48265885212719 := by
  have hr := row_4933
  have hl := log_bounds hr.1
    (by change logScale (4933 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4931) (H := 48180848186662) (u := 85037025981)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4931

theorem upper_reach_4937 : UpperReach 4937 48350930344146 := by
  have hr := row_4937
  have hl := log_bounds hr.1
    (by change logScale (4937 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4933) (H := 48265885212719) (u := 85045131351)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4933

#print axioms upper_reach_4937

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
