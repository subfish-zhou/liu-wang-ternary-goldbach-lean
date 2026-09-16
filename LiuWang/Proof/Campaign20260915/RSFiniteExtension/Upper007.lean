import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper006
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block007

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_2549 : UpperReach 2549 24806208696168 := by
  have hr := row_2549
  have hl := log_bounds hr.1
    (by change logScale (2549 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2543) (H := 24727774132077) (u := 78434564015)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2543

theorem upper_reach_2551 : UpperReach 2551 24884651103396 := by
  have hr := row_2551
  have hl := log_bounds hr.1
    (by change logScale (2551 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2549) (H := 24806208696168) (u := 78442407152)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2549

theorem upper_reach_2557 : UpperReach 2557 24963117003196 := by
  have hr := row_2557
  have hl := log_bounds hr.1
    (by change logScale (2557 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2551) (H := 24884651103396) (u := 78465899724)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2551

theorem upper_reach_2579 : UpperReach 2579 25041668573302 := by
  have hr := row_2579
  have hl := log_bounds hr.1
    (by change logScale (2579 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2557) (H := 24963117003196) (u := 78551570030)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 13, 2, 11, 2, 3, 2, 17, 2, 7, 2, 3, 2, 31, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2557

theorem upper_reach_2591 : UpperReach 2591 25120266565155 := by
  have hr := row_2591
  have hl := log_bounds hr.1
    (by change logScale (2591 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2579) (H := 25041668573302) (u := 78597991777)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 29, 2, 3, 2, 5, 2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2579

theorem upper_reach_2593 : UpperReach 2593 25198872273057 := by
  have hr := row_2593
  have hl := log_bounds hr.1
    (by change logScale (2593 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2591) (H := 25120266565155) (u := 78605707826)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2591

theorem upper_reach_2609 : UpperReach 2609 25277539495955 := by
  have hr := row_2609
  have hl := log_bounds hr.1
    (by change logScale (2609 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2593) (H := 25198872273057) (u := 78667222822)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 23, 2, 3, 2, 19, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2593

theorem upper_reach_2617 : UpperReach 2617 25356237335027 := by
  have hr := row_2617
  have hl := log_bounds hr.1
    (by change logScale (2617 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2609) (H := 25277539495955) (u := 78697838996)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2609

theorem upper_reach_2621 : UpperReach 2621 25434950447107 := by
  have hr := row_2621
  have hl := log_bounds hr.1
    (by change logScale (2621 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2617) (H := 25356237335027) (u := 78713112004)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2617

theorem upper_reach_2633 : UpperReach 2633 25513709238749 := by
  have hr := row_2633
  have hl := log_bounds hr.1
    (by change logScale (2633 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2621) (H := 25434950447107) (u := 78758791566)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 43, 2, 3, 2, 37, 2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2621

theorem upper_reach_2647 : UpperReach 2647 25592521060818 := by
  have hr := row_2647
  have hl := log_bounds hr.1
    (by change logScale (2647 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2633) (H := 25513709238749) (u := 78811821993)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 7, 2, 19, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2633

theorem upper_reach_2657 : UpperReach 2657 25671370590323 := by
  have hr := row_2657
  have hl := log_bounds hr.1
    (by change logScale (2657 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2647) (H := 25592521060818) (u := 78849529429)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2647

theorem upper_reach_2659 : UpperReach 2659 25750227644282 := by
  have hr := row_2659
  have hl := log_bounds hr.1
    (by change logScale (2659 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2657) (H := 25671370590323) (u := 78857053883)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2657

theorem upper_reach_2663 : UpperReach 2663 25829099730187 := by
  have hr := row_2663
  have hl := log_bounds hr.1
    (by change logScale (2663 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2659) (H := 25750227644282) (u := 78872085829)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2659

theorem upper_reach_2671 : UpperReach 2671 25908001812365 := by
  have hr := row_2671
  have hl := log_bounds hr.1
    (by change logScale (2671 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2663) (H := 25829099730187) (u := 78902082102)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 17, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2663

theorem upper_reach_2677 : UpperReach 2677 25986926332847 := by
  have hr := row_2677
  have hl := log_bounds hr.1
    (by change logScale (2677 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2671) (H := 25908001812365) (u := 78924520406)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2671

theorem upper_reach_2683 : UpperReach 2683 26065873241398 := by
  have hr := row_2683
  have hl := log_bounds hr.1
    (by change logScale (2683 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2677) (H := 25986926332847) (u := 78946908475)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2677

theorem upper_reach_2687 : UpperReach 2687 26144835047531 := by
  have hr := row_2687
  have hl := log_bounds hr.1
    (by change logScale (2687 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2683) (H := 26065873241398) (u := 78961806057)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2683

theorem upper_reach_2689 : UpperReach 2689 26223804294141 := by
  have hr := row_2689
  have hl := log_bounds hr.1
    (by change logScale (2689 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2687) (H := 26144835047531) (u := 78969246534)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2687

theorem upper_reach_2693 : UpperReach 2693 26302788405116 := by
  have hr := row_2693
  have hl := log_bounds hr.1
    (by change logScale (2693 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2689) (H := 26223804294141) (u := 78984110899)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2689

theorem upper_reach_2699 : UpperReach 2699 26381794771293 := by
  have hr := row_2699
  have hl := log_bounds hr.1
    (by change logScale (2699 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2693) (H := 26302788405116) (u := 79006366101)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2693

theorem upper_reach_2707 : UpperReach 2707 26460830734236 := by
  have hr := row_2707
  have hl := log_bounds hr.1
    (by change logScale (2707 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2699) (H := 26381794771293) (u := 79035962867)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 37, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2699

theorem upper_reach_2711 : UpperReach 2711 26539881462778 := by
  have hr := row_2711
  have hl := log_bounds hr.1
    (by change logScale (2711 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2707) (H := 26460830734236) (u := 79050728466)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2707

theorem upper_reach_2713 : UpperReach 2713 26618939565951 := by
  have hr := row_2713
  have hl := log_bounds hr.1
    (by change logScale (2713 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2711) (H := 26539881462778) (u := 79058103097)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2711

#print axioms upper_reach_2713

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
