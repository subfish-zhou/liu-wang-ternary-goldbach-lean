import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper011
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block012

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_3529 : UpperReach 3529 34421231865521 := by
  have hr := row_3529
  have hl := log_bounds hr.1
    (by change logScale (3529 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3527) (H := 34339544167237) (u := 81687698208)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3527

theorem upper_reach_3533 : UpperReach 3533 34502930892041 := by
  have hr := row_3533
  have hl := log_bounds hr.1
    (by change logScale (3533 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3529) (H := 34421231865521) (u := 81699026444)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3529

theorem upper_reach_3539 : UpperReach 3539 34584646886891 := by
  have hr := row_3539
  have hl := log_bounds hr.1
    (by change logScale (3539 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3533) (H := 34502930892041) (u := 81715994774)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3533

theorem upper_reach_3541 : UpperReach 3541 34666368531459 := by
  have hr := row_3541
  have hl := log_bounds hr.1
    (by change logScale (3541 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3539) (H := 34584646886891) (u := 81721644492)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3539

theorem upper_reach_3547 : UpperReach 3547 34748107106054 := by
  have hr := row_3547
  have hl := log_bounds hr.1
    (by change logScale (3547 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3541) (H := 34666368531459) (u := 81738574519)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3541

theorem upper_reach_3557 : UpperReach 3557 34829873833820 := by
  have hr := row_3557
  have hl := log_bounds hr.1
    (by change logScale (3557 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3547) (H := 34748107106054) (u := 81766727690)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 53, 2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3547

theorem upper_reach_3559 : UpperReach 3559 34911646182722 := by
  have hr := row_3559
  have hl := log_bounds hr.1
    (by change logScale (3559 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3557) (H := 34829873833820) (u := 81772348826)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3557

theorem upper_reach_3571 : UpperReach 3571 34993452192245 := by
  have hr := row_3571
  have hl := log_bounds hr.1
    (by change logScale (3571 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3559) (H := 34911646182722) (u := 81806009447)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 5, 2, 3, 2, 43, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3559

theorem upper_reach_3581 : UpperReach 3581 35075286165992 := by
  have hr := row_3581
  have hl := log_bounds hr.1
    (by change logScale (3581 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3571) (H := 34993452192245) (u := 81833973671)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3571

theorem upper_reach_3583 : UpperReach 3583 35157125723212 := by
  have hr := row_3583
  have hl := log_bounds hr.1
    (by change logScale (3583 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3581) (H := 35075286165992) (u := 81839557144)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3581

theorem upper_reach_3593 : UpperReach 3593 35238993151130 := by
  have hr := row_3593
  have hl := log_bounds hr.1
    (by change logScale (3593 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3583) (H := 35157125723212) (u := 81867427842)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 17, 2, 37, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3583

theorem upper_reach_3607 : UpperReach 3607 35320899467986 := by
  have hr := row_3607
  have hl := log_bounds hr.1
    (by change logScale (3607 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3593) (H := 35238993151130) (u := 81906316780)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 59, 2, 13, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3593

theorem upper_reach_3613 : UpperReach 3613 35402822405344 := by
  have hr := row_3613
  have hl := log_bounds hr.1
    (by change logScale (3613 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3607) (H := 35320899467986) (u := 81922937282)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 23, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3607

theorem upper_reach_3617 : UpperReach 3617 35484756407710 := by
  have hr := row_3617
  have hl := log_bounds hr.1
    (by change logScale (3617 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3613) (H := 35402822405344) (u := 81934002290)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3613

theorem upper_reach_3623 : UpperReach 3623 35566706984666 := by
  have hr := row_3623
  have hl := log_bounds hr.1
    (by change logScale (3623 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3617) (H := 35484756407710) (u := 81950576880)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3617

theorem upper_reach_3631 : UpperReach 3631 35648679618427 := by
  have hr := row_3631
  have hl := log_bounds hr.1
    (by change logScale (3631 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3623) (H := 35566706984666) (u := 81972633685)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 19, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3623

theorem upper_reach_3637 : UpperReach 3637 35730668762924 := by
  have hr := row_3637
  have hl := log_bounds hr.1
    (by change logScale (3637 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3631) (H := 35648679618427) (u := 81989144421)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3631

theorem upper_reach_3643 : UpperReach 3643 35812674390941 := by
  have hr := row_3643
  have hl := log_bounds hr.1
    (by change logScale (3643 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3637) (H := 35730668762924) (u := 82005627941)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3637

theorem upper_reach_3659 : UpperReach 3659 35894723842638 := by
  have hr := row_3659
  have hl := log_bounds hr.1
    (by change logScale (3659 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3643) (H := 35812674390941) (u := 82049451621)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 41, 2, 3, 2, 13, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3643

theorem upper_reach_3671 : UpperReach 3671 35976806036520 := by
  have hr := row_3671
  have hl := log_bounds hr.1
    (by change logScale (3671 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3659) (H := 35894723842638) (u := 82082193806)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3659

theorem upper_reach_3673 : UpperReach 3673 36058893677025 := by
  have hr := row_3673
  have hl := log_bounds hr.1
    (by change logScale (3673 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3671) (H := 35976806036520) (u := 82087640429)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3671

theorem upper_reach_3677 : UpperReach 3677 36140992201885 := by
  have hr := row_3677
  have hl := log_bounds hr.1
    (by change logScale (3677 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3673) (H := 36058893677025) (u := 82098524784)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3673

theorem upper_reach_3691 : UpperReach 3691 36223128728962 := by
  have hr := row_3691
  have hl := log_bounds hr.1
    (by change logScale (3691 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3677) (H := 36140992201885) (u := 82136527001)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 13, 2, 3, 2, 29, 2, 5, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3677

theorem upper_reach_3697 : UpperReach 3697 36305281498598 := by
  have hr := row_3697
  have hl := log_bounds hr.1
    (by change logScale (3697 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3691) (H := 36223128728962) (u := 82152769560)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3691

#print axioms upper_reach_3697

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
