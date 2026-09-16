import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper045
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block046

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_10733 : UpperReach 10733 106356900801905 := by
  have hr := row_10733
  have hl := log_bounds hr.1
    (by change logScale (10733 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10729) (H := 106264090017998) (u := 92810783831)
    (by norm_num) (by norm_num) hr.1 gap_10733 hl.2
    (by norm_num) upper_reach_10729

theorem upper_reach_10739 : UpperReach 10739 106449717174485 := by
  have hr := row_10739
  have hl := log_bounds hr.1
    (by change logScale (10739 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10733) (H := 106356900801905) (u := 92816372504)
    (by norm_num) (by norm_num) hr.1 gap_10739 hl.2
    (by norm_num) upper_reach_10733

theorem upper_reach_10753 : UpperReach 10753 106542546575171 := by
  have hr := row_10753
  have hl := log_bounds hr.1
    (by change logScale (10753 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10739) (H := 106449717174485) (u := 92829400610)
    (by norm_num) (by norm_num) hr.1 gap_10753 hl.2
    (by norm_num) upper_reach_10739

theorem upper_reach_10771 : UpperReach 10771 106635392701376 := by
  have hr := row_10771
  have hl := log_bounds hr.1
    (by change logScale (10771 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10753) (H := 106542546575171) (u := 92846126129)
    (by norm_num) (by norm_num) hr.1 gap_10771 hl.2
    (by norm_num) upper_reach_10753

theorem upper_reach_10781 : UpperReach 10781 106728248107463 := by
  have hr := row_10781
  have hl := log_bounds hr.1
    (by change logScale (10781 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10771) (H := 106635392701376) (u := 92855406011)
    (by norm_num) (by norm_num) hr.1 gap_10781 hl.2
    (by norm_num) upper_reach_10771

theorem upper_reach_10789 : UpperReach 10789 106821110931260 := by
  have hr := row_10789
  have hl := log_bounds hr.1
    (by change logScale (10789 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10781) (H := 106728248107463) (u := 92862823721)
    (by norm_num) (by norm_num) hr.1 gap_10789 hl.2
    (by norm_num) upper_reach_10781

theorem upper_reach_10799 : UpperReach 10799 106913983019464 := by
  have hr := row_10799
  have hl := log_bounds hr.1
    (by change logScale (10799 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10789) (H := 106821110931260) (u := 92872088128)
    (by norm_num) (by norm_num) hr.1 gap_10799 hl.2
    (by norm_num) upper_reach_10789

theorem upper_reach_10831 : UpperReach 10831 107006884696224 := by
  have hr := row_10831
  have hl := log_bounds hr.1
    (by change logScale (10831 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10799) (H := 106913983019464) (u := 92901676684)
    (by norm_num) (by norm_num) hr.1 gap_10831 hl.2
    (by norm_num) upper_reach_10799

theorem upper_reach_10837 : UpperReach 10837 107099791911105 := by
  have hr := row_10837
  have hl := log_bounds hr.1
    (by change logScale (10837 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10831) (H := 107006884696224) (u := 92907214805)
    (by norm_num) (by norm_num) hr.1 gap_10837 hl.2
    (by norm_num) upper_reach_10831

theorem upper_reach_10847 : UpperReach 10847 107192708349377 := by
  have hr := row_10847
  have hl := log_bounds hr.1
    (by change logScale (10847 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10837) (H := 107099791911105) (u := 92916438196)
    (by norm_num) (by norm_num) hr.1 gap_10847 hl.2
    (by norm_num) upper_reach_10837

theorem upper_reach_10853 : UpperReach 10853 107285630317603 := by
  have hr := row_10853
  have hl := log_bounds hr.1
    (by change logScale (10853 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10847) (H := 107192708349377) (u := 92921968150)
    (by norm_num) (by norm_num) hr.1 gap_10853 hl.2
    (by norm_num) upper_reach_10847

theorem upper_reach_10859 : UpperReach 10859 107378557812727 := by
  have hr := row_10859
  have hl := log_bounds hr.1
    (by change logScale (10859 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10853) (H := 107285630317603) (u := 92927495048)
    (by norm_num) (by norm_num) hr.1 gap_10859 hl.2
    (by norm_num) upper_reach_10853

theorem upper_reach_10861 : UpperReach 10861 107471487149472 := by
  have hr := row_10861
  have hl := log_bounds hr.1
    (by change logScale (10861 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10859) (H := 107378557812727) (u := 92929336669)
    (by norm_num) (by norm_num) hr.1 gap_10861 hl.2
    (by norm_num) upper_reach_10859

theorem upper_reach_10867 : UpperReach 10867 107564422009044 := by
  have hr := row_10867
  have hl := log_bounds hr.1
    (by change logScale (10867 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10861) (H := 107471487149472) (u := 92934859496)
    (by norm_num) (by norm_num) hr.1 gap_10867 hl.2
    (by norm_num) upper_reach_10861

theorem upper_reach_10883 : UpperReach 10883 107657371581263 := by
  have hr := row_10883
  have hl := log_bounds hr.1
    (by change logScale (10883 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10867) (H := 107564422009044) (u := 92949572143)
    (by norm_num) (by norm_num) hr.1 gap_10883 hl.2
    (by norm_num) upper_reach_10867

theorem upper_reach_10889 : UpperReach 10889 107750326665148 := by
  have hr := row_10889
  have hl := log_bounds hr.1
    (by change logScale (10889 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10883) (H := 107657371581263) (u := 92955083809)
    (by norm_num) (by norm_num) hr.1 gap_10889 hl.2
    (by norm_num) upper_reach_10883

theorem upper_reach_10891 : UpperReach 10891 107843283585580 := by
  have hr := row_10891
  have hl := log_bounds hr.1
    (by change logScale (10891 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10889) (H := 107750326665148) (u := 92956920356)
    (by norm_num) (by norm_num) hr.1 gap_10891 hl.2
    (by norm_num) upper_reach_10889

theorem upper_reach_10903 : UpperReach 10903 107936251518219 := by
  have hr := row_10903
  have hl := log_bounds hr.1
    (by change logScale (10903 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10891) (H := 107843283585580) (u := 92967932563)
    (by norm_num) (by norm_num) hr.1 gap_10903 hl.2
    (by norm_num) upper_reach_10891

theorem upper_reach_10909 : UpperReach 10909 108029224952417 := by
  have hr := row_10909
  have hl := log_bounds hr.1
    (by change logScale (10909 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10903) (H := 107936251518219) (u := 92973434122)
    (by norm_num) (by norm_num) hr.1 gap_10909 hl.2
    (by norm_num) upper_reach_10903

theorem upper_reach_10937 : UpperReach 10937 108122224020612 := by
  have hr := row_10937
  have hl := log_bounds hr.1
    (by change logScale (10937 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10909) (H := 108029224952417) (u := 92999068119)
    (by norm_num) (by norm_num) hr.1 gap_10937 hl.2
    (by norm_num) upper_reach_10909

theorem upper_reach_10939 : UpperReach 10939 108215224917295 := by
  have hr := row_10939
  have hl := log_bounds hr.1
    (by change logScale (10939 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10937) (H := 108122224020612) (u := 93000896607)
    (by norm_num) (by norm_num) hr.1 gap_10939 hl.2
    (by norm_num) upper_reach_10937

theorem upper_reach_10949 : UpperReach 10949 108308234951405 := by
  have hr := row_10949
  have hl := log_bounds hr.1
    (by change logScale (10949 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10939) (H := 108215224917295) (u := 93010034034)
    (by norm_num) (by norm_num) hr.1 gap_10949 hl.2
    (by norm_num) upper_reach_10939

theorem upper_reach_10957 : UpperReach 10957 108401252289451 := by
  have hr := row_10957
  have hl := log_bounds hr.1
    (by change logScale (10957 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10949) (H := 108308234951405) (u := 93017337970)
    (by norm_num) (by norm_num) hr.1 gap_10957 hl.2
    (by norm_num) upper_reach_10949

theorem upper_reach_10973 : UpperReach 10973 108494284219383 := by
  have hr := row_10973
  have hl := log_bounds hr.1
    (by change logScale (10973 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10957) (H := 108401252289451) (u := 93031929856)
    (by norm_num) (by norm_num) hr.1 gap_10973 hl.2
    (by norm_num) upper_reach_10957

#print axioms upper_reach_10973

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
