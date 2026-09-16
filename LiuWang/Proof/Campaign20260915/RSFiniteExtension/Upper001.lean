import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper000
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_1447 : UpperReach 1447 13891672943947 := by
  have hr := row_1447
  have hl := log_bounds hr.1
    (by change logScale (1447 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1439) (H := 13818900466631) (u := 72772477240)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1439

theorem upper_reach_1451 : UpperReach 1451 13964473026525 := by
  have hr := row_1451
  have hl := log_bounds hr.1
    (by change logScale (1451 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1447) (H := 13891672943947) (u := 72800082502)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1447

theorem upper_reach_1453 : UpperReach 1453 14037286883210 := by
  have hr := row_1453
  have hl := log_bounds hr.1
    (by change logScale (1453 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1451) (H := 13964473026525) (u := 72813856609)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1451

theorem upper_reach_1459 : UpperReach 1459 14110141948745 := by
  have hr := row_1459
  have hl := log_bounds hr.1
    (by change logScale (1459 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1453) (H := 14037286883210) (u := 72855065459)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 31, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1453

theorem upper_reach_1471 : UpperReach 1471 14183078926001 := by
  have hr := row_1471
  have hl := log_bounds hr.1
    (by change logScale (1471 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1459) (H := 14110141948745) (u := 72936977180)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1459

theorem upper_reach_1481 : UpperReach 1481 14256083654193 := by
  have hr := row_1481
  have hl := log_bounds hr.1
    (by change logScale (1481 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1471) (H := 14183078926001) (u := 73004728116)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1471

theorem upper_reach_1483 : UpperReach 1483 14329101877664 := by
  have hr := row_1483
  have hl := log_bounds hr.1
    (by change logScale (1483 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1481) (H := 14256083654193) (u := 73018223395)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1481

theorem upper_reach_1487 : UpperReach 1487 14402147037178 := by
  have hr := row_1487
  have hl := log_bounds hr.1
    (by change logScale (1487 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1483) (H := 14329101877664) (u := 73045159438)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1483

theorem upper_reach_1489 : UpperReach 1489 14475205637554 := by
  have hr := row_1489
  have hl := log_bounds hr.1
    (by change logScale (1489 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1487) (H := 14402147037178) (u := 73058600300)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1487

theorem upper_reach_1493 : UpperReach 1493 14548291065579 := by
  have hr := row_1493
  have hl := log_bounds hr.1
    (by change logScale (1493 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1489) (H := 14475205637554) (u := 73085427949)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1489

theorem upper_reach_1499 : UpperReach 1499 14621416600610 := by
  have hr := row_1499
  have hl := log_bounds hr.1
    (by change logScale (1499 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1493) (H := 14548291065579) (u := 73125534955)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1493

theorem upper_reach_1511 : UpperReach 1511 14694621870282 := by
  have hr := row_1511
  have hl := log_bounds hr.1
    (by change logScale (1511 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1499) (H := 14621416600610) (u := 73205269596)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 19, 2, 3, 2, 5, 2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1499

theorem upper_reach_1523 : UpperReach 1523 14767906243860 := by
  have hr := row_1523
  have hl := log_bounds hr.1
    (by change logScale (1523 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1511) (H := 14694621870282) (u := 73284373502)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 17, 2, 3, 2, 37, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1511

theorem upper_reach_1531 : UpperReach 1531 14841243007866 := by
  have hr := row_1531
  have hl := log_bounds hr.1
    (by change logScale (1531 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1523) (H := 14767906243860) (u := 73336763930)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1523

theorem upper_reach_1543 : UpperReach 1543 14914657846439 := by
  have hr := row_1543
  have hl := log_bounds hr.1
    (by change logScale (1543 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1531) (H := 14841243007866) (u := 73414838497)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 29, 2, 3, 2, 23, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1531

theorem upper_reach_1549 : UpperReach 1549 14988111494893 := by
  have hr := row_1549
  have hl := log_bounds hr.1
    (by change logScale (1549 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1543) (H := 14914657846439) (u := 73453648378)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1543

theorem upper_reach_1553 : UpperReach 1553 15061590933174 := by
  have hr := row_1553
  have hl := log_bounds hr.1
    (by change logScale (1553 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1549) (H := 14988111494893) (u := 73479438205)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1549

theorem upper_reach_1559 : UpperReach 1559 15135108931914 := by
  have hr := row_1559
  have hl := log_bounds hr.1
    (by change logScale (1559 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1553) (H := 15061590933174) (u := 73517998664)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1553

theorem upper_reach_1567 : UpperReach 1567 15208678114387 := by
  have hr := row_1567
  have hl := log_bounds hr.1
    (by change logScale (1567 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1559) (H := 15135108931914) (u := 73569182397)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1559

theorem upper_reach_1571 : UpperReach 1571 15282272790819 := by
  have hr := row_1571
  have hl := log_bounds hr.1
    (by change logScale (1571 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1567) (H := 15208678114387) (u := 73594676356)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1567

theorem upper_reach_1579 : UpperReach 1579 15355918261011 := by
  have hr := row_1579
  have hl := log_bounds hr.1
    (by change logScale (1579 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1571) (H := 15282272790819) (u := 73645470116)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 19, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1571

theorem upper_reach_1583 : UpperReach 1583 15429589031659 := by
  have hr := row_1583
  have hl := log_bounds hr.1
    (by change logScale (1583 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1579) (H := 15355918261011) (u := 73670770572)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1579

theorem upper_reach_1597 : UpperReach 1597 15503347853191 := by
  have hr := row_1597
  have hl := log_bounds hr.1
    (by change logScale (1597 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1583) (H := 15429589031659) (u := 73758821456)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 7, 2, 37, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1583

theorem upper_reach_1601 : UpperReach 1601 15577131690370 := by
  have hr := row_1601
  have hl := log_bounds hr.1
    (by change logScale (1601 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1597) (H := 15503347853191) (u := 73783837103)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1597

#print axioms upper_reach_1601

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
