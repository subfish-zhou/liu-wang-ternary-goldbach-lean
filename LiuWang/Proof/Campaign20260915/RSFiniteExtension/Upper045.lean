import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper044
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block045

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_10501 : UpperReach 10501 104131662862197 := by
  have hr := row_10501
  have hl := log_bounds hr.1
    (by change logScale (10501 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10499) (H := 104039070604458) (u := 92592257663)
    (by norm_num) (by norm_num) hr.1 gap_10501 hl.2
    (by norm_num) upper_reach_10499

theorem upper_reach_10513 : UpperReach 10513 104224266540894 := by
  have hr := row_10513
  have hl := log_bounds hr.1
    (by change logScale (10513 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10501) (H := 104131662862197) (u := 92603678621)
    (by norm_num) (by norm_num) hr.1 gap_10513 hl.2
    (by norm_num) upper_reach_10501

theorem upper_reach_10529 : UpperReach 10529 104316885427274 := by
  have hr := row_10529
  have hl := log_bounds hr.1
    (by change logScale (10529 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10513) (H := 104224266540894) (u := 92618886304)
    (by norm_num) (by norm_num) hr.1 gap_10529 hl.2
    (by norm_num) upper_reach_10513

theorem upper_reach_10531 : UpperReach 10531 104409506212990 := by
  have hr := row_10531
  have hl := log_bounds hr.1
    (by change logScale (10531 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10529) (H := 104316885427274) (u := 92620785640)
    (by norm_num) (by norm_num) hr.1 gap_10531 hl.2
    (by norm_num) upper_reach_10529

theorem upper_reach_10559 : UpperReach 10559 104502153551590 := by
  have hr := row_10559
  have hl := log_bounds hr.1
    (by change logScale (10559 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10531) (H := 104409506212990) (u := 92647338524)
    (by norm_num) (by norm_num) hr.1 gap_10559 hl.2
    (by norm_num) upper_reach_10531

theorem upper_reach_10567 : UpperReach 10567 104594808463796 := by
  have hr := row_10567
  have hl := log_bounds hr.1
    (by change logScale (10567 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10559) (H := 104502153551590) (u := 92654912130)
    (by norm_num) (by norm_num) hr.1 gap_10567 hl.2
    (by norm_num) upper_reach_10559

theorem upper_reach_10589 : UpperReach 10589 104687484173892 := by
  have hr := row_10589
  have hl := log_bounds hr.1
    (by change logScale (10589 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10567) (H := 104594808463796) (u := 92675710020)
    (by norm_num) (by norm_num) hr.1 gap_10589 hl.2
    (by norm_num) upper_reach_10567

theorem upper_reach_10597 : UpperReach 10597 104780167436145 := by
  have hr := row_10597
  have hl := log_bounds hr.1
    (by change logScale (10597 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10589) (H := 104687484173892) (u := 92683262177)
    (by norm_num) (by norm_num) hr.1 gap_10597 hl.2
    (by norm_num) upper_reach_10589

theorem upper_reach_10601 : UpperReach 10601 104872854472339 := by
  have hr := row_10601
  have hl := log_bounds hr.1
    (by change logScale (10601 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10597) (H := 104780167436145) (u := 92687036118)
    (by norm_num) (by norm_num) hr.1 gap_10601 hl.2
    (by norm_num) upper_reach_10597

theorem upper_reach_10607 : UpperReach 10607 104965547166776 := by
  have hr := row_10607
  have hl := log_bounds hr.1
    (by change logScale (10607 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10601) (H := 104872854472339) (u := 92692694361)
    (by norm_num) (by norm_num) hr.1 gap_10607 hl.2
    (by norm_num) upper_reach_10601

theorem upper_reach_10613 : UpperReach 10613 105058245516255 := by
  have hr := row_10613
  have hl := log_bounds hr.1
    (by change logScale (10613 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10607) (H := 104965547166776) (u := 92698349403)
    (by norm_num) (by norm_num) hr.1 gap_10613 hl.2
    (by norm_num) upper_reach_10607

theorem upper_reach_10627 : UpperReach 10627 105150957048410 := by
  have hr := row_10627
  have hl := log_bounds hr.1
    (by change logScale (10627 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10613) (H := 105058245516255) (u := 92711532079)
    (by norm_num) (by norm_num) hr.1 gap_10627 hl.2
    (by norm_num) upper_reach_10613

theorem upper_reach_10631 : UpperReach 10631 105243672343855 := by
  have hr := row_10631
  have hl := log_bounds hr.1
    (by change logScale (10631 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10627) (H := 105150957048410) (u := 92715295369)
    (by norm_num) (by norm_num) hr.1 gap_10631 hl.2
    (by norm_num) upper_reach_10627

theorem upper_reach_10639 : UpperReach 10639 105336395161632 := by
  have hr := row_10639
  have hl := log_bounds hr.1
    (by change logScale (10639 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10631) (H := 105243672343855) (u := 92722817701)
    (by norm_num) (by norm_num) hr.1 gap_10639 hl.2
    (by norm_num) upper_reach_10631

theorem upper_reach_10651 : UpperReach 10651 105429129252308 := by
  have hr := row_10651
  have hl := log_bounds hr.1
    (by change logScale (10651 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10639) (H := 105336395161632) (u := 92734090600)
    (by norm_num) (by norm_num) hr.1 gap_10651 hl.2
    (by norm_num) upper_reach_10639

theorem upper_reach_10657 : UpperReach 10657 105521868974672 := by
  have hr := row_10657
  have hl := log_bounds hr.1
    (by change logScale (10657 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10651) (H := 105429129252308) (u := 92739722288)
    (by norm_num) (by norm_num) hr.1 gap_10657 hl.2
    (by norm_num) upper_reach_10651

theorem upper_reach_10663 : UpperReach 10663 105614614325554 := by
  have hr := row_10663
  have hl := log_bounds hr.1
    (by change logScale (10663 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10657) (H := 105521868974672) (u := 92745350806)
    (by norm_num) (by norm_num) hr.1 gap_10663 hl.2
    (by norm_num) upper_reach_10657

theorem upper_reach_10667 : UpperReach 10667 105707363427022 := by
  have hr := row_10667
  have hl := log_bounds hr.1
    (by change logScale (10667 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10663) (H := 105614614325554) (u := 92749101392)
    (by norm_num) (by norm_num) hr.1 gap_10667 hl.2
    (by norm_num) upper_reach_10663

theorem upper_reach_10687 : UpperReach 10687 105800131260349 := by
  have hr := row_10687
  have hl := log_bounds hr.1
    (by change logScale (10687 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10667) (H := 105707363427022) (u := 92767833251)
    (by norm_num) (by norm_num) hr.1 gap_10687 hl.2
    (by norm_num) upper_reach_10667

theorem upper_reach_10691 : UpperReach 10691 105892902835841 := by
  have hr := row_10691
  have hl := log_bounds hr.1
    (by change logScale (10691 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10687) (H := 105800131260349) (u := 92771575416)
    (by norm_num) (by norm_num) hr.1 gap_10691 hl.2
    (by norm_num) upper_reach_10687

theorem upper_reach_10709 : UpperReach 10709 105985691233767 := by
  have hr := row_10709
  have hl := log_bounds hr.1
    (by change logScale (10709 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10691) (H := 105892902835841) (u := 92788397850)
    (by norm_num) (by norm_num) hr.1 gap_10709 hl.2
    (by norm_num) upper_reach_10691

theorem upper_reach_10711 : UpperReach 10711 106078481499106 := by
  have hr := row_10711
  have hl := log_bounds hr.1
    (by change logScale (10711 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10709) (H := 105985691233767) (u := 92790265263)
    (by norm_num) (by norm_num) hr.1 gap_10711 hl.2
    (by norm_num) upper_reach_10709

theorem upper_reach_10723 : UpperReach 10723 106171282961610 := by
  have hr := row_10723
  have hl := log_bounds hr.1
    (by change logScale (10723 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10711) (H := 106078481499106) (u := 92801462428)
    (by norm_num) (by norm_num) hr.1 gap_10723 hl.2
    (by norm_num) upper_reach_10711

theorem upper_reach_10729 : UpperReach 10729 106264090017998 := by
  have hr := row_10729
  have hl := log_bounds hr.1
    (by change logScale (10729 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10723) (H := 106171282961610) (u := 92807056312)
    (by norm_num) (by norm_num) hr.1 gap_10729 hl.2
    (by norm_num) upper_reach_10723

#print axioms upper_reach_10729

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
