import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper040
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block041

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_9629 : UpperReach 9629 95283688865123 := by
  have hr := row_9629
  have hl := log_bounds hr.1
    (by change logScale (9629 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9623) (H := 95191963518509) (u := 91725346538)
    (by norm_num) (by norm_num) hr.1 gap_9629 hl.2
    (by norm_num) upper_reach_9623

theorem upper_reach_9631 : UpperReach 9631 95375416288580 := by
  have hr := row_9631
  have hl := log_bounds hr.1
    (by change logScale (9631 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9629) (H := 95283688865123) (u := 91727423381)
    (by norm_num) (by norm_num) hr.1 gap_9631 hl.2
    (by norm_num) upper_reach_9629

theorem upper_reach_9643 : UpperReach 9643 95467156164047 := by
  have hr := row_9643
  have hl := log_bounds hr.1
    (by change logScale (9643 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9631) (H := 95375416288580) (u := 91739875391)
    (by norm_num) (by norm_num) hr.1 gap_9643 hl.2
    (by norm_num) upper_reach_9631

theorem upper_reach_9649 : UpperReach 9649 95558902259709 := by
  have hr := row_9649
  have hl := log_bounds hr.1
    (by change logScale (9649 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9643) (H := 95467156164047) (u := 91746095586)
    (by norm_num) (by norm_num) hr.1 gap_9649 hl.2
    (by norm_num) upper_reach_9643

theorem upper_reach_9661 : UpperReach 9661 95650660784166 := by
  have hr := row_9661
  have hl := log_bounds hr.1
    (by change logScale (9661 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9649) (H := 95558902259709) (u := 91758524381)
    (by norm_num) (by norm_num) hr.1 gap_9661 hl.2
    (by norm_num) upper_reach_9649

theorem upper_reach_9677 : UpperReach 9677 95742435856357 := by
  have hr := row_9677
  have hl := log_bounds hr.1
    (by change logScale (9677 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9661) (H := 95650660784166) (u := 91775072115)
    (by norm_num) (by norm_num) hr.1 gap_9677 hl.2
    (by norm_num) upper_reach_9661

theorem upper_reach_9679 : UpperReach 9679 95834212995090 := by
  have hr := row_9679
  have hl := log_bounds hr.1
    (by change logScale (9679 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9677) (H := 95742435856357) (u := 91777138657)
    (by norm_num) (by norm_num) hr.1 gap_9679 hl.2
    (by norm_num) upper_reach_9677

theorem upper_reach_9689 : UpperReach 9689 95926000460136 := by
  have hr := row_9689
  have hl := log_bounds hr.1
    (by change logScale (9689 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9679) (H := 95834212995090) (u := 91787464970)
    (by norm_num) (by norm_num) hr.1 gap_9689 hl.2
    (by norm_num) upper_reach_9679

theorem upper_reach_9697 : UpperReach 9697 96017796178561 := by
  have hr := row_9697
  have hl := log_bounds hr.1
    (by change logScale (9697 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9689) (H := 95926000460136) (u := 91795718349)
    (by norm_num) (by norm_num) hr.1 gap_9697 hl.2
    (by norm_num) upper_reach_9689

theorem upper_reach_9719 : UpperReach 9719 96109614558718 := by
  have hr := row_9719
  have hl := log_bounds hr.1
    (by change logScale (9719 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9697) (H := 96017796178561) (u := 91818380081)
    (by norm_num) (by norm_num) hr.1 gap_9719 hl.2
    (by norm_num) upper_reach_9697

theorem upper_reach_9721 : UpperReach 9721 96201434996488 := by
  have hr := row_9721
  have hl := log_bounds hr.1
    (by change logScale (9721 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9719) (H := 96109614558718) (u := 91820437694)
    (by norm_num) (by norm_num) hr.1 gap_9721 hl.2
    (by norm_num) upper_reach_9719

theorem upper_reach_9733 : UpperReach 9733 96293267771054 := by
  have hr := row_9733
  have hl := log_bounds hr.1
    (by change logScale (9733 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9721) (H := 96201434996488) (u := 91832774490)
    (by norm_num) (by norm_num) hr.1 gap_9733 hl.2
    (by norm_num) upper_reach_9721

theorem upper_reach_9739 : UpperReach 9739 96385106708315 := by
  have hr := row_9739
  have hl := log_bounds hr.1
    (by change logScale (9739 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9733) (H := 96293267771054) (u := 91838937185)
    (by norm_num) (by norm_num) hr.1 gap_9739 hl.2
    (by norm_num) upper_reach_9733

theorem upper_reach_9743 : UpperReach 9743 96476949751931 := by
  have hr := row_9743
  have hl := log_bounds hr.1
    (by change logScale (9743 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9739) (H := 96385106708315) (u := 91843043540)
    (by norm_num) (by norm_num) hr.1 gap_9743 hl.2
    (by norm_num) upper_reach_9739

theorem upper_reach_9749 : UpperReach 9749 96568798951919 := by
  have hr := row_9749
  have hl := log_bounds hr.1
    (by change logScale (9749 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9743) (H := 96476949751931) (u := 91849199912)
    (by norm_num) (by norm_num) hr.1 gap_9749 hl.2
    (by norm_num) upper_reach_9743

theorem upper_reach_9767 : UpperReach 9767 96660666598315 := by
  have hr := row_9767
  have hl := log_bounds hr.1
    (by change logScale (9767 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9749) (H := 96568798951919) (u := 91867646320)
    (by norm_num) (by norm_num) hr.1 gap_9767 hl.2
    (by norm_num) upper_reach_9749

theorem upper_reach_9769 : UpperReach 9769 96752536292213 := by
  have hr := row_9769
  have hl := log_bounds hr.1
    (by change logScale (9769 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9767) (H := 96660666598315) (u := 91869693822)
    (by norm_num) (by norm_num) hr.1 gap_9769 hl.2
    (by norm_num) upper_reach_9767

theorem upper_reach_9781 : UpperReach 9781 96844418262328 := by
  have hr := row_9781
  have hl := log_bounds hr.1
    (by change logScale (9781 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9769) (H := 96752536292213) (u := 91881970039)
    (by norm_num) (by norm_num) hr.1 gap_9781 hl.2
    (by norm_num) upper_reach_9769

theorem upper_reach_9787 : UpperReach 9787 96936306364904 := by
  have hr := row_9787
  have hl := log_bounds hr.1
    (by change logScale (9787 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9781) (H := 96844418262328) (u := 91888102500)
    (by norm_num) (by norm_num) hr.1 gap_9787 hl.2
    (by norm_num) upper_reach_9781

theorem upper_reach_9791 : UpperReach 9791 97028198553699 := by
  have hr := row_9791
  have hl := log_bounds hr.1
    (by change logScale (9791 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9787) (H := 96936306364904) (u := 91892188719)
    (by norm_num) (by norm_num) hr.1 gap_9791 hl.2
    (by norm_num) upper_reach_9787

theorem upper_reach_9803 : UpperReach 9803 97120102991143 := by
  have hr := row_9803
  have hl := log_bounds hr.1
    (by change logScale (9803 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9791) (H := 97028198553699) (u := 91904437368)
    (by norm_num) (by norm_num) hr.1 gap_9803 hl.2
    (by norm_num) upper_reach_9791

theorem upper_reach_9811 : UpperReach 9811 97212015586026 := by
  have hr := row_9811
  have hl := log_bounds hr.1
    (by change logScale (9811 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9803) (H := 97120102991143) (u := 91912594807)
    (by norm_num) (by norm_num) hr.1 gap_9811 hl.2
    (by norm_num) upper_reach_9803

theorem upper_reach_9817 : UpperReach 9817 97303934294625 := by
  have hr := row_9817
  have hl := log_bounds hr.1
    (by change logScale (9817 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9811) (H := 97212015586026) (u := 91918708523)
    (by norm_num) (by norm_num) hr.1 gap_9817 hl.2
    (by norm_num) upper_reach_9811

theorem upper_reach_9829 : UpperReach 9829 97395865219452 := by
  have hr := row_9829
  have hl := log_bounds hr.1
    (by change logScale (9829 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9817) (H := 97303934294625) (u := 91930924751)
    (by norm_num) (by norm_num) hr.1 gap_9829 hl.2
    (by norm_num) upper_reach_9817

#print axioms upper_reach_9829

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
