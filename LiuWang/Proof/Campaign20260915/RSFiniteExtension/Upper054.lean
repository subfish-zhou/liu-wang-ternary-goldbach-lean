import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper053
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block054

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_12569 : UpperReach 12569 124337628285169 := by
  have hr := row_12569
  have hl := log_bounds hr.1
    (by change logScale (12569 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12553) (H := 124243238397688) (u := 94389887405)
    (by norm_num) (by norm_num) hr.1 gap_12569 hl.2
    (by norm_num) upper_reach_12553

theorem upper_reach_12577 : UpperReach 12577 124432024535491 := by
  have hr := row_12577
  have hl := log_bounds hr.1
    (by change logScale (12577 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12569) (H := 124337628285169) (u := 94396250246)
    (by norm_num) (by norm_num) hr.1 gap_12577 hl.2
    (by norm_num) upper_reach_12569

theorem upper_reach_12583 : UpperReach 12583 124526425555289 := by
  have hr := row_12583
  have hl := log_bounds hr.1
    (by change logScale (12583 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12577) (H := 124432024535491) (u := 94401019722)
    (by norm_num) (by norm_num) hr.1 gap_12583 hl.2
    (by norm_num) upper_reach_12577

theorem upper_reach_12589 : UpperReach 12589 124620831342288 := by
  have hr := row_12589
  have hl := log_bounds hr.1
    (by change logScale (12589 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12583) (H := 124526425555289) (u := 94405786923)
    (by norm_num) (by norm_num) hr.1 gap_12589 hl.2
    (by norm_num) upper_reach_12583

theorem upper_reach_12601 : UpperReach 12601 124715246656878 := by
  have hr := row_12601
  have hl := log_bounds hr.1
    (by change logScale (12601 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12589) (H := 124620831342288) (u := 94415314514)
    (by norm_num) (by norm_num) hr.1 gap_12601 hl.2
    (by norm_num) upper_reach_12589

theorem upper_reach_12611 : UpperReach 12611 124809669904199 := by
  have hr := row_12611
  have hl := log_bounds hr.1
    (by change logScale (12611 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12601) (H := 124715246656878) (u := 94423247245)
    (by norm_num) (by norm_num) hr.1 gap_12611 hl.2
    (by norm_num) upper_reach_12601

theorem upper_reach_12613 : UpperReach 12613 124904094737312 := by
  have hr := row_12613
  have hl := log_bounds hr.1
    (by change logScale (12613 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12611) (H := 124809669904199) (u := 94424833037)
    (by norm_num) (by norm_num) hr.1 gap_12613 hl.2
    (by norm_num) upper_reach_12611

theorem upper_reach_12619 : UpperReach 12619 124998524326290 := by
  have hr := row_12619
  have hl := log_bounds hr.1
    (by change logScale (12619 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12613) (H := 124904094737312) (u := 94429588902)
    (by norm_num) (by norm_num) hr.1 gap_12619 hl.2
    (by norm_num) upper_reach_12613

theorem upper_reach_12637 : UpperReach 12637 125092968169309 := by
  have hr := row_12637
  have hl := log_bounds hr.1
    (by change logScale (12637 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12619) (H := 124998524326290) (u := 94443842943)
    (by norm_num) (by norm_num) hr.1 gap_12637 hl.2
    (by norm_num) upper_reach_12619

theorem upper_reach_12641 : UpperReach 12641 125187415177136 := by
  have hr := row_12641
  have hl := log_bounds hr.1
    (by change logScale (12641 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12637) (H := 125092968169309) (u := 94447007751)
    (by norm_num) (by norm_num) hr.1 gap_12641 hl.2
    (by norm_num) upper_reach_12637

theorem upper_reach_12647 : UpperReach 12647 125281866930297 := by
  have hr := row_12647
  have hl := log_bounds hr.1
    (by change logScale (12647 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12641) (H := 125187415177136) (u := 94451753085)
    (by norm_num) (by norm_num) hr.1 gap_12647 hl.2
    (by norm_num) upper_reach_12641

theorem upper_reach_12653 : UpperReach 12653 125376323426541 := by
  have hr := row_12653
  have hl := log_bounds hr.1
    (by change logScale (12653 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12647) (H := 125281866930297) (u := 94456496168)
    (by norm_num) (by norm_num) hr.1 gap_12653 hl.2
    (by norm_num) upper_reach_12647

theorem upper_reach_12659 : UpperReach 12659 125470784663619 := by
  have hr := row_12659
  have hl := log_bounds hr.1
    (by change logScale (12659 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12653) (H := 125376323426541) (u := 94461237002)
    (by norm_num) (by norm_num) hr.1 gap_12659 hl.2
    (by norm_num) upper_reach_12653

theorem upper_reach_12671 : UpperReach 12671 125565255375629 := by
  have hr := row_12671
  have hl := log_bounds hr.1
    (by change logScale (12671 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12659) (H := 125470784663619) (u := 94470711934)
    (by norm_num) (by norm_num) hr.1 gap_12671 hl.2
    (by norm_num) upper_reach_12659

theorem upper_reach_12689 : UpperReach 12689 125659740283225 := by
  have hr := row_12689
  have hl := log_bounds hr.1
    (by change logScale (12689 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12671) (H := 125565255375629) (u := 94484907520)
    (by norm_num) (by norm_num) hr.1 gap_12689 hl.2
    (by norm_num) upper_reach_12671

theorem upper_reach_12697 : UpperReach 12697 125754231493507 := by
  have hr := row_12697
  have hl := log_bounds hr.1
    (by change logScale (12697 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12689) (H := 125659740283225) (u := 94491210206)
    (by norm_num) (by norm_num) hr.1 gap_12697 hl.2
    (by norm_num) upper_reach_12689

theorem upper_reach_12703 : UpperReach 12703 125848727428199 := by
  have hr := row_12703
  have hl := log_bounds hr.1
    (by change logScale (12703 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12697) (H := 125754231493507) (u := 94495934616)
    (by norm_num) (by norm_num) hr.1 gap_12703 hl.2
    (by norm_num) upper_reach_12697

theorem upper_reach_12713 : UpperReach 12713 125943231231950 := by
  have hr := row_12713
  have hl := log_bounds hr.1
    (by change logScale (12713 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12703) (H := 125848727428199) (u := 94503803675)
    (by norm_num) (by norm_num) hr.1 gap_12713 hl.2
    (by norm_num) upper_reach_12703

theorem upper_reach_12721 : UpperReach 12721 126037741326493 := by
  have hr := row_12721
  have hl := log_bounds hr.1
    (by change logScale (12721 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12713) (H := 125943231231950) (u := 94510094467)
    (by norm_num) (by norm_num) hr.1 gap_12721 hl.2
    (by norm_num) upper_reach_12713

theorem upper_reach_12739 : UpperReach 12739 126132265560866 := by
  have hr := row_12739
  have hl := log_bounds hr.1
    (by change logScale (12739 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12721) (H := 126037741326493) (u := 94524234297)
    (by norm_num) (by norm_num) hr.1 gap_12739 hl.2
    (by norm_num) upper_reach_12721

theorem upper_reach_12743 : UpperReach 12743 126226792934710 := by
  have hr := row_12743
  have hl := log_bounds hr.1
    (by change logScale (12743 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12739) (H := 126132265560866) (u := 94527373768)
    (by norm_num) (by norm_num) hr.1 gap_12743 hl.2
    (by norm_num) upper_reach_12739

theorem upper_reach_12757 : UpperReach 12757 126321331288947 := by
  have hr := row_12757
  have hl := log_bounds hr.1
    (by change logScale (12757 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12743) (H := 126226792934710) (u := 94538354161)
    (by norm_num) (by norm_num) hr.1 gap_12757 hl.2
    (by norm_num) upper_reach_12743

theorem upper_reach_12763 : UpperReach 12763 126415874345379 := by
  have hr := row_12763
  have hl := log_bounds hr.1
    (by change logScale (12763 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12757) (H := 126321331288947) (u := 94543056356)
    (by norm_num) (by norm_num) hr.1 gap_12763 hl.2
    (by norm_num) upper_reach_12757

theorem upper_reach_12781 : UpperReach 12781 126510431495142 := by
  have hr := row_12781
  have hl := log_bounds hr.1
    (by change logScale (12781 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12763) (H := 126415874345379) (u := 94557149687)
    (by norm_num) (by norm_num) hr.1 gap_12781 hl.2
    (by norm_num) upper_reach_12763

#print axioms upper_reach_12781

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
