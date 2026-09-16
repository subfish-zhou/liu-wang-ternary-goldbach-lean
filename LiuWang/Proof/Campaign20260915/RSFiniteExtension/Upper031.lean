import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper030
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block031

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_7489 : UpperReach 7489 73559349025743 := by
  have hr := row_7489
  have hl := log_bounds hr.1
    (by change logScale (7489 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7487) (H := 73470137120136) (u := 89211905531)
    (by norm_num) (by norm_num) hr.1 gap_7489 hl.2
    (by norm_num) upper_reach_7487

theorem upper_reach_7499 : UpperReach 7499 73648574275360 := by
  have hr := row_7499
  have hl := log_bounds hr.1
    (by change logScale (7499 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7489) (H := 73559349025743) (u := 89225249541)
    (by norm_num) (by norm_num) hr.1 gap_7499 hl.2
    (by norm_num) upper_reach_7489

theorem upper_reach_7507 : UpperReach 7507 73737810187380 := by
  have hr := row_7507
  have hl := log_bounds hr.1
    (by change logScale (7507 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7499) (H := 73648574275360) (u := 89235911944)
    (by norm_num) (by norm_num) hr.1 gap_7507 hl.2
    (by norm_num) upper_reach_7499

theorem upper_reach_7517 : UpperReach 7517 73827059411436 := by
  have hr := row_7517
  have hl := log_bounds hr.1
    (by change logScale (7517 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7507) (H := 73737810187380) (u := 89249223980)
    (by norm_num) (by norm_num) hr.1 gap_7517 hl.2
    (by norm_num) upper_reach_7507

theorem upper_reach_7523 : UpperReach 7523 73916316614216 := by
  have hr := row_7523
  have hl := log_bounds hr.1
    (by change logScale (7523 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7517) (H := 73827059411436) (u := 89257202704)
    (by norm_num) (by norm_num) hr.1 gap_7523 hl.2
    (by norm_num) upper_reach_7517

theorem upper_reach_7529 : UpperReach 7529 74005581789359 := by
  have hr := row_7529
  have hl := log_bounds hr.1
    (by change logScale (7529 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7523) (H := 73916316614216) (u := 89265175067)
    (by norm_num) (by norm_num) hr.1 gap_7529 hl.2
    (by norm_num) upper_reach_7523

theorem upper_reach_7537 : UpperReach 7537 74094857584442 := by
  have hr := row_7537
  have hl := log_bounds hr.1
    (by change logScale (7537 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7529) (H := 74005581789359) (u := 89275795007)
    (by norm_num) (by norm_num) hr.1 gap_7537 hl.2
    (by norm_num) upper_reach_7529

theorem upper_reach_7541 : UpperReach 7541 74184138685268 := by
  have hr := row_7541
  have hl := log_bounds hr.1
    (by change logScale (7541 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7537) (H := 74094857584442) (u := 89281100750)
    (by norm_num) (by norm_num) hr.1 gap_7541 hl.2
    (by norm_num) upper_reach_7537

theorem upper_reach_7547 : UpperReach 7547 74273427739435 := by
  have hr := row_7547
  have hl := log_bounds hr.1
    (by change logScale (7547 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7541) (H := 74184138685268) (u := 89289054091)
    (by norm_num) (by norm_num) hr.1 gap_7547 hl.2
    (by norm_num) upper_reach_7541

theorem upper_reach_7549 : UpperReach 7549 74362719443311 := by
  have hr := row_7549
  have hl := log_bounds hr.1
    (by change logScale (7549 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7547) (H := 74273427739435) (u := 89291703800)
    (by norm_num) (by norm_num) hr.1 gap_7549 hl.2
    (by norm_num) upper_reach_7547

theorem upper_reach_7559 : UpperReach 7559 74452024385208 := by
  have hr := row_7559
  have hl := log_bounds hr.1
    (by change logScale (7559 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7549) (H := 74362719443311) (u := 89304941821)
    (by norm_num) (by norm_num) hr.1 gap_7559 hl.2
    (by norm_num) upper_reach_7549

theorem upper_reach_7561 : UpperReach 7561 74541331972608 := by
  have hr := row_7561
  have hl := log_bounds hr.1
    (by change logScale (7561 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7559) (H := 74452024385208) (u := 89307587324)
    (by norm_num) (by norm_num) hr.1 gap_7561 hl.2
    (by norm_num) upper_reach_7559

theorem upper_reach_7573 : UpperReach 7573 74630655418343 := by
  have hr := row_7573
  have hl := log_bounds hr.1
    (by change logScale (7573 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7561) (H := 74541331972608) (u := 89323445659)
    (by norm_num) (by norm_num) hr.1 gap_7573 hl.2
    (by norm_num) upper_reach_7561

theorem upper_reach_7577 : UpperReach 7577 74719984144607 := by
  have hr := row_7577
  have hl := log_bounds hr.1
    (by change logScale (7577 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7573) (H := 74630655418343) (u := 89328726188)
    (by norm_num) (by norm_num) hr.1 gap_7577 hl.2
    (by norm_num) upper_reach_7573

theorem upper_reach_7583 : UpperReach 7583 74809320786438 := by
  have hr := row_7583
  have hl := log_bounds hr.1
    (by change logScale (7583 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7577) (H := 74719984144607) (u := 89336641755)
    (by norm_num) (by norm_num) hr.1 gap_7583 hl.2
    (by norm_num) upper_reach_7577

theorem upper_reach_7589 : UpperReach 7589 74898665337576 := by
  have hr := row_7589
  have hl := log_bounds hr.1
    (by change logScale (7589 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7583) (H := 74809320786438) (u := 89344551062)
    (by norm_num) (by norm_num) hr.1 gap_7589 hl.2
    (by norm_num) upper_reach_7583

theorem upper_reach_7591 : UpperReach 7591 74988012523760 := by
  have hr := row_7591
  have hl := log_bounds hr.1
    (by change logScale (7591 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7589) (H := 74898665337576) (u := 89347186108)
    (by norm_num) (by norm_num) hr.1 gap_7591 hl.2
    (by norm_num) upper_reach_7589

theorem upper_reach_7603 : UpperReach 7603 75077375505657 := by
  have hr := row_7603
  have hl := log_bounds hr.1
    (by change logScale (7603 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7591) (H := 74988012523760) (u := 89362981821)
    (by norm_num) (by norm_num) hr.1 gap_7603 hl.2
    (by norm_num) upper_reach_7591

theorem upper_reach_7607 : UpperReach 7607 75166743747251 := by
  have hr := row_7607
  have hl := log_bounds hr.1
    (by change logScale (7607 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7603) (H := 75077375505657) (u := 89368241518)
    (by norm_num) (by norm_num) hr.1 gap_7607 hl.2
    (by norm_num) upper_reach_7603

theorem upper_reach_7621 : UpperReach 7621 75256130376032 := by
  have hr := row_7621
  have hl := log_bounds hr.1
    (by change logScale (7621 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7607) (H := 75166743747251) (u := 89386628705)
    (by norm_num) (by norm_num) hr.1 gap_7621 hl.2
    (by norm_num) upper_reach_7607

theorem upper_reach_7639 : UpperReach 7639 75345540595912 := by
  have hr := row_7639
  have hl := log_bounds hr.1
    (by change logScale (7639 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7621) (H := 75256130376032) (u := 89410219804)
    (by norm_num) (by norm_num) hr.1 gap_7639 hl.2
    (by norm_num) upper_reach_7621

theorem upper_reach_7643 : UpperReach 7643 75434956050709 := by
  have hr := row_7643
  have hl := log_bounds hr.1
    (by change logScale (7643 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7639) (H := 75345540595912) (u := 89415454721)
    (by norm_num) (by norm_num) hr.1 gap_7643 hl.2
    (by norm_num) upper_reach_7639

theorem upper_reach_7649 : UpperReach 7649 75524379352747 := by
  have hr := row_7649
  have hl := log_bounds hr.1
    (by change logScale (7649 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7643) (H := 75434956050709) (u := 89423301962)
    (by norm_num) (by norm_num) hr.1 gap_7649 hl.2
    (by norm_num) upper_reach_7643

theorem upper_reach_7669 : UpperReach 7669 75613828767869 := by
  have hr := row_7669
  have hl := log_bounds hr.1
    (by change logScale (7669 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7649) (H := 75524379352747) (u := 89449415046)
    (by norm_num) (by norm_num) hr.1 gap_7669 hl.2
    (by norm_num) upper_reach_7649

#print axioms upper_reach_7669

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
