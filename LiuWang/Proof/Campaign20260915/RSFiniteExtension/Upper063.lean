import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper062
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block063

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_14657 : UpperReach 14657 144894473078096 := by
  have hr := row_14657
  have hl := log_bounds hr.1
    (by change logScale (14657 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14653) (H := 144798546344894) (u := 95926733126)
    (by norm_num) (by norm_num) hr.1 gap_14657 hl.2
    (by norm_num) upper_reach_14653

theorem upper_reach_14669 : UpperReach 14669 144990407995163 := by
  have hr := row_14669
  have hl := log_bounds hr.1
    (by change logScale (14669 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14657) (H := 144894473078096) (u := 95934916991)
    (by norm_num) (by norm_num) hr.1 gap_14669 hl.2
    (by norm_num) upper_reach_14657

theorem upper_reach_14683 : UpperReach 14683 145086352451614 := by
  have hr := row_14683
  have hl := log_bounds hr.1
    (by change logScale (14683 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14669) (H := 144990407995163) (u := 95944456375)
    (by norm_num) (by norm_num) hr.1 gap_14683 hl.2
    (by norm_num) upper_reach_14669

theorem upper_reach_14699 : UpperReach 14699 145182307799088 := by
  have hr := row_14699
  have hl := log_bounds hr.1
    (by change logScale (14699 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14683) (H := 145086352451614) (u := 95955347398)
    (by norm_num) (by norm_num) hr.1 gap_14699 hl.2
    (by norm_num) upper_reach_14683

theorem upper_reach_14713 : UpperReach 14713 145278272666487 := by
  have hr := row_14713
  have hl := log_bounds hr.1
    (by change logScale (14713 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14699) (H := 145182307799088) (u := 95964867323)
    (by norm_num) (by norm_num) hr.1 gap_14713 hl.2
    (by norm_num) upper_reach_14699

theorem upper_reach_14717 : UpperReach 14717 145374240252200 := by
  have hr := row_14717
  have hl := log_bounds hr.1
    (by change logScale (14717 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14713) (H := 145278272666487) (u := 95967585637)
    (by norm_num) (by norm_num) hr.1 gap_14717 hl.2
    (by norm_num) upper_reach_14713

theorem upper_reach_14723 : UpperReach 14723 145470211914000 := by
  have hr := row_14723
  have hl := log_bounds hr.1
    (by change logScale (14723 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14717) (H := 145374240252200) (u := 95971661724)
    (by norm_num) (by norm_num) hr.1 gap_14723 hl.2
    (by norm_num) upper_reach_14717

theorem upper_reach_14731 : UpperReach 14731 145566189008000 := by
  have hr := row_14731
  have hl := log_bounds hr.1
    (by change logScale (14731 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14723) (H := 145470211914000) (u := 95977093924)
    (by norm_num) (by norm_num) hr.1 gap_14731 hl.2
    (by norm_num) upper_reach_14723

theorem upper_reach_14737 : UpperReach 14737 145662170174214 := by
  have hr := row_14737
  have hl := log_bounds hr.1
    (by change logScale (14737 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14731) (H := 145566189008000) (u := 95981166138)
    (by norm_num) (by norm_num) hr.1 gap_14737 hl.2
    (by norm_num) upper_reach_14731

theorem upper_reach_14741 : UpperReach 14741 145758154054316 := by
  have hr := row_14741
  have hl := log_bounds hr.1
    (by change logScale (14741 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14737) (H := 145662170174214) (u := 95983880026)
    (by norm_num) (by norm_num) hr.1 gap_14741 hl.2
    (by norm_num) upper_reach_14737

theorem upper_reach_14747 : UpperReach 14747 145854142003870 := by
  have hr := row_14747
  have hl := log_bounds hr.1
    (by change logScale (14747 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14741) (H := 145758154054316) (u := 95987949478)
    (by norm_num) (by norm_num) hr.1 gap_14747 hl.2
    (by norm_num) upper_reach_14741

theorem upper_reach_14753 : UpperReach 14753 145950134021221 := by
  have hr := row_14753
  have hl := log_bounds hr.1
    (by change logScale (14753 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14747) (H := 145854142003870) (u := 95992017275)
    (by norm_num) (by norm_num) hr.1 gap_14753 hl.2
    (by norm_num) upper_reach_14747

theorem upper_reach_14759 : UpperReach 14759 146046130104715 := by
  have hr := row_14759
  have hl := log_bounds hr.1
    (by change logScale (14759 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14753) (H := 145950134021221) (u := 95996083418)
    (by norm_num) (by norm_num) hr.1 gap_14759 hl.2
    (by norm_num) upper_reach_14753

theorem upper_reach_14767 : UpperReach 14767 146142131607161 := by
  have hr := row_14767
  have hl := log_bounds hr.1
    (by change logScale (14767 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14759) (H := 146046130104715) (u := 96001502370)
    (by norm_num) (by norm_num) hr.1 gap_14767 hl.2
    (by norm_num) upper_reach_14759

theorem upper_reach_14771 : UpperReach 14771 146238135817983 := by
  have hr := row_14771
  have hl := log_bounds hr.1
    (by change logScale (14771 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14767) (H := 146142131607161) (u := 96004210746)
    (by norm_num) (by norm_num) hr.1 gap_14771 hl.2
    (by norm_num) upper_reach_14767

theorem upper_reach_14779 : UpperReach 14779 146334145443357 := by
  have hr := row_14779
  have hl := log_bounds hr.1
    (by change logScale (14779 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14771) (H := 146238135817983) (u := 96009625298)
    (by norm_num) (by norm_num) hr.1 gap_14779 hl.2
    (by norm_num) upper_reach_14771

theorem upper_reach_14783 : UpperReach 14783 146430157774908 := by
  have hr := row_14783
  have hl := log_bounds hr.1
    (by change logScale (14783 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14779) (H := 146334145443357) (u := 96012331475)
    (by norm_num) (by norm_num) hr.1 gap_14783 hl.2
    (by norm_num) upper_reach_14779

theorem upper_reach_14797 : UpperReach 14797 146526179572315 := by
  have hr := row_14797
  have hl := log_bounds hr.1
    (by change logScale (14797 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14783) (H := 146430157774908) (u := 96021797331)
    (by norm_num) (by norm_num) hr.1 gap_14797 hl.2
    (by norm_num) upper_reach_14783

theorem upper_reach_14813 : UpperReach 14813 146622212176883 := by
  have hr := row_14813
  have hl := log_bounds hr.1
    (by change logScale (14813 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14797) (H := 146526179572315) (u := 96032604492)
    (by norm_num) (by norm_num) hr.1 gap_14813 hl.2
    (by norm_num) upper_reach_14797

theorem upper_reach_14821 : UpperReach 14821 146718250180654 := by
  have hr := row_14821
  have hl := log_bounds hr.1
    (by change logScale (14821 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14813) (H := 146622212176883) (u := 96038003695)
    (by norm_num) (by norm_num) hr.1 gap_14821 hl.2
    (by norm_num) upper_reach_14813

theorem upper_reach_14827 : UpperReach 14827 146814292231916 := by
  have hr := row_14827
  have hl := log_bounds hr.1
    (by change logScale (14827 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14821) (H := 146718250180654) (u := 96042051186)
    (by norm_num) (by norm_num) hr.1 gap_14827 hl.2
    (by norm_num) upper_reach_14821

theorem upper_reach_14831 : UpperReach 14831 146910336980595 := by
  have hr := row_14831
  have hl := log_bounds hr.1
    (by change logScale (14831 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14827) (H := 146814292231916) (u := 96044748603)
    (by norm_num) (by norm_num) hr.1 gap_14831 hl.2
    (by norm_num) upper_reach_14827

theorem upper_reach_14843 : UpperReach 14843 147006389817163 := by
  have hr := row_14843
  have hl := log_bounds hr.1
    (by change logScale (14843 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14831) (H := 146910336980595) (u := 96052836492)
    (by norm_num) (by norm_num) hr.1 gap_14843 hl.2
    (by norm_num) upper_reach_14831

theorem upper_reach_14851 : UpperReach 14851 147102448042025 := by
  have hr := row_14851
  have hl := log_bounds hr.1
    (by change logScale (14851 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14843) (H := 147006389817163) (u := 96058224786)
    (by norm_num) (by norm_num) hr.1 gap_14851 hl.2
    (by norm_num) upper_reach_14843

#print axioms upper_reach_14851

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
