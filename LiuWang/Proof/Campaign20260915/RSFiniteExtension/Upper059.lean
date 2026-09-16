import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper058
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block059

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_13709 : UpperReach 13709 135716796851516 := by
  have hr := row_13709
  have hl := log_bounds hr.1
    (by change logScale (13709 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13697) (H := 135621538773170) (u := 95258078270)
    (by norm_num) (by norm_num) hr.1 gap_13709 hl.2
    (by norm_num) upper_reach_13697

theorem upper_reach_13711 : UpperReach 13711 135812056388651 := by
  have hr := row_13711
  have hl := log_bounds hr.1
    (by change logScale (13711 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13709) (H := 135716796851516) (u := 95259537059)
    (by norm_num) (by norm_num) hr.1 gap_13711 hl.2
    (by norm_num) upper_reach_13709

theorem upper_reach_13721 : UpperReach 13721 135907323216542 := by
  have hr := row_13721
  have hl := log_bounds hr.1
    (by change logScale (13721 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13711) (H := 135812056388651) (u := 95266827815)
    (by norm_num) (by norm_num) hr.1 gap_13721 hl.2
    (by norm_num) upper_reach_13711

theorem upper_reach_13723 : UpperReach 13723 136002591501946 := by
  have hr := row_13723
  have hl := log_bounds hr.1
    (by change logScale (13723 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13721) (H := 135907323216542) (u := 95268285328)
    (by norm_num) (by norm_num) hr.1 gap_13723 hl.2
    (by norm_num) upper_reach_13721

theorem upper_reach_13729 : UpperReach 13729 136097864158617 := by
  have hr := row_13729
  have hl := log_bounds hr.1
    (by change logScale (13729 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13723) (H := 136002591501946) (u := 95272656595)
    (by norm_num) (by norm_num) hr.1 gap_13729 hl.2
    (by norm_num) upper_reach_13723

theorem upper_reach_13751 : UpperReach 13751 136193152826936 := by
  have hr := row_13751
  have hl := log_bounds hr.1
    (by change logScale (13751 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13729) (H := 136097864158617) (u := 95288668243)
    (by norm_num) (by norm_num) hr.1 gap_13751 hl.2
    (by norm_num) upper_reach_13729

theorem upper_reach_13757 : UpperReach 13757 136288445857622 := by
  have hr := row_13757
  have hl := log_bounds hr.1
    (by change logScale (13757 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13751) (H := 136193152826936) (u := 95293030610)
    (by norm_num) (by norm_num) hr.1 gap_13757 hl.2
    (by norm_num) upper_reach_13751

theorem upper_reach_13759 : UpperReach 13759 136383740342008 := by
  have hr := row_13759
  have hl := log_bounds hr.1
    (by change logScale (13759 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13757) (H := 136288445857622) (u := 95294484310)
    (by norm_num) (by norm_num) hr.1 gap_13759 hl.2
    (by norm_num) upper_reach_13757

theorem upper_reach_13763 : UpperReach 13763 136479037733160 := by
  have hr := row_13763
  have hl := log_bounds hr.1
    (by change logScale (13763 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13759) (H := 136383740342008) (u := 95297391076)
    (by norm_num) (by norm_num) hr.1 gap_13763 hl.2
    (by norm_num) upper_reach_13759

theorem upper_reach_13781 : UpperReach 13781 136574348194310 := by
  have hr := row_13781
  have hl := log_bounds hr.1
    (by change logScale (13781 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13763) (H := 136479037733160) (u := 95310461074)
    (by norm_num) (by norm_num) hr.1 gap_13781 hl.2
    (by norm_num) upper_reach_13763

theorem upper_reach_13789 : UpperReach 13789 136669664458870 := by
  have hr := row_13789
  have hl := log_bounds hr.1
    (by change logScale (13789 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13781) (H := 136574348194310) (u := 95316264484)
    (by norm_num) (by norm_num) hr.1 gap_13789 hl.2
    (by norm_num) upper_reach_13781

theorem upper_reach_13799 : UpperReach 13799 136764987972959 := by
  have hr := row_13799
  have hl := log_bounds hr.1
    (by change logScale (13799 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13789) (H := 136669664458870) (u := 95323514013)
    (by norm_num) (by norm_num) hr.1 gap_13799 hl.2
    (by norm_num) upper_reach_13789

theorem upper_reach_13807 : UpperReach 13807 136860317282890 := by
  have hr := row_13807
  have hl := log_bounds hr.1
    (by change logScale (13807 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13799) (H := 136764987972959) (u := 95329309855)
    (by norm_num) (by norm_num) hr.1 gap_13807 hl.2
    (by norm_num) upper_reach_13799

theorem upper_reach_13829 : UpperReach 13829 136955662514086 := by
  have hr := row_13829
  have hl := log_bounds hr.1
    (by change logScale (13829 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13807) (H := 136860317282890) (u := 95345231120)
    (by norm_num) (by norm_num) hr.1 gap_13829 hl.2
    (by norm_num) upper_reach_13807

theorem upper_reach_13831 : UpperReach 13831 137051009191414 := by
  have hr := row_13831
  have hl := log_bounds hr.1
    (by change logScale (13831 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13829) (H := 136955662514086) (u := 95346677252)
    (by norm_num) (by norm_num) hr.1 gap_13831 hl.2
    (by norm_num) upper_reach_13829

theorem upper_reach_13841 : UpperReach 13841 137146363096265 := by
  have hr := row_13841
  have hl := log_bounds hr.1
    (by change logScale (13841 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13831) (H := 137051009191414) (u := 95353904775)
    (by norm_num) (by norm_num) hr.1 gap_13841 hl.2
    (by norm_num) upper_reach_13831

theorem upper_reach_13859 : UpperReach 13859 137241729997507 := by
  have hr := row_13859
  have hl := log_bounds hr.1
    (by change logScale (13859 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13841) (H := 137146363096265) (u := 95366901166)
    (by norm_num) (by norm_num) hr.1 gap_13859 hl.2
    (by norm_num) upper_reach_13841

theorem upper_reach_13873 : UpperReach 13873 137337106995390 := by
  have hr := row_13873
  have hl := log_bounds hr.1
    (by change logScale (13873 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13859) (H := 137241729997507) (u := 95376997807)
    (by norm_num) (by norm_num) hr.1 gap_13873 hl.2
    (by norm_num) upper_reach_13859

theorem upper_reach_13877 : UpperReach 13877 137432486876155 := by
  have hr := row_13877
  have hl := log_bounds hr.1
    (by change logScale (13877 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13873) (H := 137337106995390) (u := 95379880689)
    (by norm_num) (by norm_num) hr.1 gap_13877 hl.2
    (by norm_num) upper_reach_13873

theorem upper_reach_13879 : UpperReach 13879 137527868198050 := by
  have hr := row_13879
  have hl := log_bounds hr.1
    (by change logScale (13879 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13877) (H := 137432486876155) (u := 95381321819)
    (by norm_num) (by norm_num) hr.1 gap_13879 hl.2
    (by norm_num) upper_reach_13877

theorem upper_reach_13883 : UpperReach 13883 137623252401582 := by
  have hr := row_13883
  have hl := log_bounds hr.1
    (by change logScale (13883 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13879) (H := 137527868198050) (u := 95384203456)
    (by norm_num) (by norm_num) hr.1 gap_13883 hl.2
    (by norm_num) upper_reach_13879

theorem upper_reach_13901 : UpperReach 13901 137718649562213 := by
  have hr := row_13901
  have hl := log_bounds hr.1
    (by change logScale (13901 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13883) (H := 137623252401582) (u := 95397160555)
    (by norm_num) (by norm_num) hr.1 gap_13901 hl.2
    (by norm_num) upper_reach_13883

theorem upper_reach_13903 : UpperReach 13903 137814048161486 := by
  have hr := row_13903
  have hl := log_bounds hr.1
    (by change logScale (13903 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13901) (H := 137718649562213) (u := 95398599197)
    (by norm_num) (by norm_num) hr.1 gap_13903 hl.2
    (by norm_num) upper_reach_13901

theorem upper_reach_13907 : UpperReach 13907 137909449637422 := by
  have hr := row_13907
  have hl := log_bounds hr.1
    (by change logScale (13907 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13903) (H := 137814048161486) (u := 95401475860)
    (by norm_num) (by norm_num) hr.1 gap_13907 hl.2
    (by norm_num) upper_reach_13903

#print axioms upper_reach_13907

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
