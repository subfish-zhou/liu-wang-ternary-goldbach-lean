import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper021
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block022

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_5557 : UpperReach 5557 54603023623239 := by
  have hr := row_5557
  have hl := log_bounds hr.1
    (by change logScale (5557 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5531) (H := 54516795486462) (u := 86228136701)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 7, 2, 29, 2, 3, 2, 23, 2, 5, 2, 3, 2, 31, 2, 7, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5531

theorem upper_reach_5563 : UpperReach 5563 54689262551384 := by
  have hr := row_5563
  have hl := log_bounds hr.1
    (by change logScale (5563 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5557) (H := 54603023623239) (u := 86238928069)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 67, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5557

theorem upper_reach_5569 : UpperReach 5569 54775512259264 := by
  have hr := row_5569
  have hl := log_bounds hr.1
    (by change logScale (5569 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5563) (H := 54689262551384) (u := 86249707804)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 19, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5563

theorem upper_reach_5573 : UpperReach 5573 54861769147184 := by
  have hr := row_5573
  have hl := log_bounds hr.1
    (by change logScale (5573 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5569) (H := 54775512259264) (u := 86256887844)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5569

theorem upper_reach_5581 : UpperReach 5581 54948040379736 := by
  have hr := row_5581
  have hl := log_bounds hr.1
    (by change logScale (5581 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5573) (H := 54861769147184) (u := 86271232476)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5573

theorem upper_reach_5591 : UpperReach 5591 55034329514191 := by
  have hr := row_5591
  have hl := log_bounds hr.1
    (by change logScale (5591 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5581) (H := 54948040379736) (u := 86289134379)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 37, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5581

theorem upper_reach_5623 : UpperReach 5623 55120675720318 := by
  have hr := row_5623
  have hl := log_bounds hr.1
    (by change logScale (5623 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5591) (H := 55034329514191) (u := 86346206051)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 29, 2, 11, 2, 3, 2, 13, 2, 5, 2, 3, 2, 71, 2, 31, 2, 3, 2, 5, 2, 41, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5591

theorem upper_reach_5639 : UpperReach 5639 55207050340600 := by
  have hr := row_5639
  have hl := log_bounds hr.1
    (by change logScale (5639 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5623) (H := 55120675720318) (u := 86374620206)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 17, 2, 13, 2, 3, 2, 43, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5623

theorem upper_reach_5641 : UpperReach 5641 55293428506982 := by
  have hr := row_5641
  have hl := log_bounds hr.1
    (by change logScale (5641 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5639) (H := 55207050340600) (u := 86378166306)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5639

theorem upper_reach_5647 : UpperReach 5647 55379817304123 := by
  have hr := row_5647
  have hl := log_bounds hr.1
    (by change logScale (5647 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5641) (H := 55293428506982) (u := 86388797065)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5641

theorem upper_reach_5651 : UpperReach 5651 55466213182164 := by
  have hr := row_5651
  have hl := log_bounds hr.1
    (by change logScale (5651 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5647) (H := 55379817304123) (u := 86395877965)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5647

theorem upper_reach_5653 : UpperReach 5653 55552612598775 := by
  have hr := row_5653
  have hl := log_bounds hr.1
    (by change logScale (5653 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5651) (H := 55466213182164) (u := 86399416535)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5651

theorem upper_reach_5657 : UpperReach 5657 55639019088773 := by
  have hr := row_5657
  have hl := log_bounds hr.1
    (by change logScale (5657 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5653) (H := 55552612598775) (u := 86406489922)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5653

theorem upper_reach_5659 : UpperReach 5659 55725429113589 := by
  have hr := row_5659
  have hl := log_bounds hr.1
    (by change logScale (5659 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5657) (H := 55639019088773) (u := 86410024740)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5657

theorem upper_reach_5669 : UpperReach 5669 55811856793777 := by
  have hr := row_5669
  have hl := log_bounds hr.1
    (by change logScale (5669 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5659) (H := 55725429113589) (u := 86427680112)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5659

theorem upper_reach_5683 : UpperReach 5683 55898309139234 := by
  have hr := row_5683
  have hl := log_bounds hr.1
    (by change logScale (5683 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5669) (H := 55811856793777) (u := 86452345381)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 53, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5669

theorem upper_reach_5689 : UpperReach 5689 55984772036926 := by
  have hr := row_5689
  have hl := log_bounds hr.1
    (by change logScale (5689 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5683) (H := 55898309139234) (u := 86462897616)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5683

theorem upper_reach_5693 : UpperReach 5693 56071241963260 := by
  have hr := row_5693
  have hl := log_bounds hr.1
    (by change logScale (5693 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5689) (H := 55984772036926) (u := 86469926258)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5689

theorem upper_reach_5701 : UpperReach 5701 56157725932075 := by
  have hr := row_5701
  have hl := log_bounds hr.1
    (by change logScale (5701 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5693) (H := 56071241963260) (u := 86483968739)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 41, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5693

theorem upper_reach_5711 : UpperReach 5711 56244227426306 := by
  have hr := row_5711
  have hl := log_bounds hr.1
    (by change logScale (5711 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5701) (H := 56157725932075) (u := 86501494155)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5701

theorem upper_reach_5717 : UpperReach 5717 56330739421063 := by
  have hr := row_5717
  have hl := log_bounds hr.1
    (by change logScale (5717 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5711) (H := 56244227426306) (u := 86511994681)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 29, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5711

theorem upper_reach_5737 : UpperReach 5737 56417286338153 := by
  have hr := row_5737
  have hl := log_bounds hr.1
    (by change logScale (5737 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5717) (H := 56330739421063) (u := 86546917014)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 59, 2, 5, 2, 3, 2, 17, 2, 11, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5717

theorem upper_reach_5741 : UpperReach 5741 56503840225099 := by
  have hr := row_5741
  have hl := log_bounds hr.1
    (by change logScale (5741 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5737) (H := 56417286338153) (u := 86553886870)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5737

theorem upper_reach_5743 : UpperReach 5743 56590397595152 := by
  have hr := row_5743
  have hl := log_bounds hr.1
    (by change logScale (5743 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5741) (H := 56503840225099) (u := 86557369977)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5741

#print axioms upper_reach_5743

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
