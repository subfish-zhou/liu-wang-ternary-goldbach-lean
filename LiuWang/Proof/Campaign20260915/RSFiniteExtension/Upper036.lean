import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper035
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block036

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_8581 : UpperReach 8581 84345245623166 := by
  have hr := row_8581
  have hl := log_bounds hr.1
    (by change logScale (8581 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8573) (H := 84254672565766) (u := 90573057324)
    (by norm_num) (by norm_num) hr.1 gap_8581 hl.2
    (by norm_num) upper_reach_8573

theorem upper_reach_8597 : UpperReach 8597 84435837309049 := by
  have hr := row_8597
  have hl := log_bounds hr.1
    (by change logScale (8597 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8581) (H := 84345245623166) (u := 90591685807)
    (by norm_num) (by norm_num) hr.1 gap_8597 hl.2
    (by norm_num) upper_reach_8581

theorem upper_reach_8599 : UpperReach 8599 84526431321055 := by
  have hr := row_8599
  have hl := log_bounds hr.1
    (by change logScale (8599 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8597) (H := 84435837309049) (u := 90594011930)
    (by norm_num) (by norm_num) hr.1 gap_8599 hl.2
    (by norm_num) upper_reach_8597

theorem upper_reach_8609 : UpperReach 8609 84617036955563 := by
  have hr := row_8609
  have hl := log_bounds hr.1
    (by change logScale (8609 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8599) (H := 84526431321055) (u := 90605634432)
    (by norm_num) (by norm_num) hr.1 gap_8609 hl.2
    (by norm_num) upper_reach_8599

theorem upper_reach_8623 : UpperReach 8623 84707658838914 := by
  have hr := row_8623
  have hl := log_bounds hr.1
    (by change logScale (8623 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8609) (H := 84617036955563) (u := 90621883275)
    (by norm_num) (by norm_num) hr.1 gap_8623 hl.2
    (by norm_num) upper_reach_8609

theorem upper_reach_8627 : UpperReach 8627 84798285359946 := by
  have hr := row_8627
  have hl := log_bounds hr.1
    (by change logScale (8627 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8623) (H := 84707658838914) (u := 90626520956)
    (by norm_num) (by norm_num) hr.1 gap_8627 hl.2
    (by norm_num) upper_reach_8623

theorem upper_reach_8629 : UpperReach 8629 84888914199013 := by
  have hr := row_8629
  have hl := log_bounds hr.1
    (by change logScale (8629 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8627) (H := 84798285359946) (u := 90628838991)
    (by norm_num) (by norm_num) hr.1 gap_8629 hl.2
    (by norm_num) upper_reach_8627

theorem upper_reach_8641 : UpperReach 8641 84979556935013 := by
  have hr := row_8641
  have hl := log_bounds hr.1
    (by change logScale (8641 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8629) (H := 84888914199013) (u := 90642735924)
    (by norm_num) (by norm_num) hr.1 gap_8641 hl.2
    (by norm_num) upper_reach_8629

theorem upper_reach_8647 : UpperReach 8647 85070206612244 := by
  have hr := row_8647
  have hl := log_bounds hr.1
    (by change logScale (8647 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8641) (H := 84979556935013) (u := 90649677155)
    (by norm_num) (by norm_num) hr.1 gap_8647 hl.2
    (by norm_num) upper_reach_8641

theorem upper_reach_8663 : UpperReach 8663 85160874775905 := by
  have hr := row_8663
  have hl := log_bounds hr.1
    (by change logScale (8663 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8647) (H := 85070206612244) (u := 90668163585)
    (by norm_num) (by norm_num) hr.1 gap_8663 hl.2
    (by norm_num) upper_reach_8647

theorem upper_reach_8669 : UpperReach 8669 85251549863175 := by
  have hr := row_8669
  have hl := log_bounds hr.1
    (by change logScale (8669 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8663) (H := 85160874775905) (u := 90675087194)
    (by norm_num) (by norm_num) hr.1 gap_8669 hl.2
    (by norm_num) upper_reach_8663

theorem upper_reach_8677 : UpperReach 8677 85342234174475 := by
  have hr := row_8677
  have hl := log_bounds hr.1
    (by change logScale (8677 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8669) (H := 85251549863175) (u := 90684311224)
    (by norm_num) (by norm_num) hr.1 gap_8677 hl.2
    (by norm_num) upper_reach_8669

theorem upper_reach_8681 : UpperReach 8681 85432923094601 := by
  have hr := row_8681
  have hl := log_bounds hr.1
    (by change logScale (8681 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8677) (H := 85342234174475) (u := 90688920050)
    (by norm_num) (by norm_num) hr.1 gap_8681 hl.2
    (by norm_num) upper_reach_8677

theorem upper_reach_8689 : UpperReach 8689 85523621226011 := by
  have hr := row_8689
  have hl := log_bounds hr.1
    (by change logScale (8689 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8681) (H := 85432923094601) (u := 90698131334)
    (by norm_num) (by norm_num) hr.1 gap_8689 hl.2
    (by norm_num) upper_reach_8681

theorem upper_reach_8693 : UpperReach 8693 85614323959883 := by
  have hr := row_8693
  have hl := log_bounds hr.1
    (by change logScale (8693 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8689) (H := 85523621226011) (u := 90702733796)
    (by norm_num) (by norm_num) hr.1 gap_8693 hl.2
    (by norm_num) upper_reach_8689

theorem upper_reach_8699 : UpperReach 8699 85705033593480 := by
  have hr := row_8699
  have hl := log_bounds hr.1
    (by change logScale (8699 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8693) (H := 85614323959883) (u := 90709633521)
    (by norm_num) (by norm_num) hr.1 gap_8699 hl.2
    (by norm_num) upper_reach_8693

theorem upper_reach_8707 : UpperReach 8707 85795752419310 := by
  have hr := row_8707
  have hl := log_bounds hr.1
    (by change logScale (8707 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8699) (H := 85705033593480) (u := 90718825754)
    (by norm_num) (by norm_num) hr.1 gap_8707 hl.2
    (by norm_num) upper_reach_8699

theorem upper_reach_8713 : UpperReach 8713 85886478133774 := by
  have hr := row_8713
  have hl := log_bounds hr.1
    (by change logScale (8713 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8707) (H := 85795752419310) (u := 90725714388)
    (by norm_num) (by norm_num) hr.1 gap_8713 hl.2
    (by norm_num) upper_reach_8707

theorem upper_reach_8719 : UpperReach 8719 85977210732130 := by
  have hr := row_8719
  have hl := log_bounds hr.1
    (by change logScale (8719 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8713) (H := 85886478133774) (u := 90732598280)
    (by norm_num) (by norm_num) hr.1 gap_8719 hl.2
    (by norm_num) upper_reach_8713

theorem upper_reach_8731 : UpperReach 8731 86067957084070 := by
  have hr := row_8731
  have hl := log_bounds hr.1
    (by change logScale (8731 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8719) (H := 85977210732130) (u := 90746351864)
    (by norm_num) (by norm_num) hr.1 gap_8731 hl.2
    (by norm_num) upper_reach_8719

theorem upper_reach_8737 : UpperReach 8737 86158710305715 := by
  have hr := row_8737
  have hl := log_bounds hr.1
    (by change logScale (8737 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8731) (H := 86067957084070) (u := 90753221569)
    (by norm_num) (by norm_num) hr.1 gap_8737 hl.2
    (by norm_num) upper_reach_8731

theorem upper_reach_8741 : UpperReach 8741 86249468104543 := by
  have hr := row_8741
  have hl := log_bounds hr.1
    (by change logScale (8741 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8737) (H := 86158710305715) (u := 90757798752)
    (by norm_num) (by norm_num) hr.1 gap_8741 hl.2
    (by norm_num) upper_reach_8737

theorem upper_reach_8747 : UpperReach 8747 86340232765219 := by
  have hr := row_8747
  have hl := log_bounds hr.1
    (by change logScale (8747 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8741) (H := 86249468104543) (u := 90764660600)
    (by norm_num) (by norm_num) hr.1 gap_8747 hl.2
    (by norm_num) upper_reach_8741

theorem upper_reach_8753 : UpperReach 8753 86431004283038 := by
  have hr := row_8753
  have hl := log_bounds hr.1
    (by change logScale (8753 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8747) (H := 86340232765219) (u := 90771517743)
    (by norm_num) (by norm_num) hr.1 gap_8753 hl.2
    (by norm_num) upper_reach_8747

#print axioms upper_reach_8753

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
