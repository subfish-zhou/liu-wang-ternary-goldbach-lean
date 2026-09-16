import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper061
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block062

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_14437 : UpperReach 14437 142593865850631 := by
  have hr := row_14437
  have hl := log_bounds hr.1
    (by change logScale (14437 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14431) (H := 142498090354243) (u := 95775496312)
    (by norm_num) (by norm_num) hr.1 gap_14437 hl.2
    (by norm_num) upper_reach_14431

theorem upper_reach_14447 : UpperReach 14447 142689648271268 := by
  have hr := row_14447
  have hl := log_bounds hr.1
    (by change logScale (14447 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14437) (H := 142593865850631) (u := 95782420561)
    (by norm_num) (by norm_num) hr.1 gap_14447 hl.2
    (by norm_num) upper_reach_14437

theorem upper_reach_14449 : UpperReach 14449 142785432076180 := by
  have hr := row_14449
  have hl := log_bounds hr.1
    (by change logScale (14449 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14447) (H := 142689648271268) (u := 95783804836)
    (by norm_num) (by norm_num) hr.1 gap_14449 hl.2
    (by norm_num) upper_reach_14447

theorem upper_reach_14461 : UpperReach 14461 142881224182718 := by
  have hr := row_14461
  have hl := log_bounds hr.1
    (by change logScale (14461 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14449) (H := 142785432076180) (u := 95792106462)
    (by norm_num) (by norm_num) hr.1 gap_14461 hl.2
    (by norm_num) upper_reach_14449

theorem upper_reach_14479 : UpperReach 14479 142977028728788 := by
  have hr := row_14479
  have hl := log_bounds hr.1
    (by change logScale (14479 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14461) (H := 142881224182718) (u := 95804545994)
    (by norm_num) (by norm_num) hr.1 gap_14479 hl.2
    (by norm_num) upper_reach_14461

theorem upper_reach_14489 : UpperReach 14489 143072840179028 := by
  have hr := row_14489
  have hl := log_bounds hr.1
    (by change logScale (14489 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14479) (H := 142977028728788) (u := 95811450164)
    (by norm_num) (by norm_num) hr.1 gap_14489 hl.2
    (by norm_num) upper_reach_14479

theorem upper_reach_14503 : UpperReach 14503 143168661287105 := by
  have hr := row_14503
  have hl := log_bounds hr.1
    (by change logScale (14503 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14489) (H := 143072840179028) (u := 95821108001)
    (by norm_num) (by norm_num) hr.1 gap_14503 hl.2
    (by norm_num) upper_reach_14489

theorem upper_reach_14519 : UpperReach 14519 143264493421302 := by
  have hr := row_14519
  have hl := log_bounds hr.1
    (by change logScale (14519 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14503) (H := 143168661287105) (u := 95832134121)
    (by norm_num) (by norm_num) hr.1 gap_14519 hl.2
    (by norm_num) upper_reach_14503

theorem upper_reach_14533 : UpperReach 14533 143360335193390 := by
  have hr := row_14533
  have hl := log_bounds hr.1
    (by change logScale (14533 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14519) (H := 143264493421302) (u := 95841772012)
    (by norm_num) (by norm_num) hr.1 gap_14533 hl.2
    (by norm_num) upper_reach_14519

theorem upper_reach_14537 : UpperReach 14537 143456179717456 := by
  have hr := row_14537
  have hl := log_bounds hr.1
    (by change logScale (14537 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14533) (H := 143360335193390) (u := 95844523990)
    (by norm_num) (by norm_num) hr.1 gap_14537 hl.2
    (by norm_num) upper_reach_14533

theorem upper_reach_14543 : UpperReach 14543 143552028368069 := by
  have hr := row_14543
  have hl := log_bounds hr.1
    (by change logScale (14543 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14537) (H := 143456179717456) (u := 95848650537)
    (by norm_num) (by norm_num) hr.1 gap_14543 hl.2
    (by norm_num) upper_reach_14537

theorem upper_reach_14549 : UpperReach 14549 143647881143528 := by
  have hr := row_14549
  have hl := log_bounds hr.1
    (by change logScale (14549 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14543) (H := 143552028368069) (u := 95852775383)
    (by norm_num) (by norm_num) hr.1 gap_14549 hl.2
    (by norm_num) upper_reach_14543

theorem upper_reach_14551 : UpperReach 14551 143743735293557 := by
  have hr := row_14551
  have hl := log_bounds hr.1
    (by change logScale (14551 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14549) (H := 143647881143528) (u := 95854149953)
    (by norm_num) (by norm_num) hr.1 gap_14551 hl.2
    (by norm_num) upper_reach_14549

theorem upper_reach_14557 : UpperReach 14557 143839593566164 := by
  have hr := row_14557
  have hl := log_bounds hr.1
    (by change logScale (14557 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14551) (H := 143743735293557) (u := 95858272531)
    (by norm_num) (by norm_num) hr.1 gap_14557 hl.2
    (by norm_num) upper_reach_14551

theorem upper_reach_14561 : UpperReach 14561 143935454586213 := by
  have hr := row_14561
  have hl := log_bounds hr.1
    (by change logScale (14561 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14557) (H := 143839593566164) (u := 95861019973)
    (by norm_num) (by norm_num) hr.1 gap_14561 hl.2
    (by norm_num) upper_reach_14557

theorem upper_reach_14563 : UpperReach 14563 144031316979700 := by
  have hr := row_14563
  have hl := log_bounds hr.1
    (by change logScale (14563 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14561) (H := 143935454586213) (u := 95862393411)
    (by norm_num) (by norm_num) hr.1 gap_14563 hl.2
    (by norm_num) upper_reach_14561

theorem upper_reach_14591 : UpperReach 14591 144127198581534 := by
  have hr := row_14591
  have hl := log_bounds hr.1
    (by change logScale (14591 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14563) (H := 144031316979700) (u := 95881601758)
    (by norm_num) (by norm_num) hr.1 gap_14591 hl.2
    (by norm_num) upper_reach_14563

theorem upper_reach_14593 : UpperReach 14593 144223081553982 := by
  have hr := row_14593
  have hl := log_bounds hr.1
    (by change logScale (14593 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14591) (H := 144127198581534) (u := 95882972372)
    (by norm_num) (by norm_num) hr.1 gap_14593 hl.2
    (by norm_num) upper_reach_14591

theorem upper_reach_14621 : UpperReach 14621 144318983695328 := by
  have hr := row_14621
  have hl := log_bounds hr.1
    (by change logScale (14621 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14593) (H := 144223081553982) (u := 95902141270)
    (by norm_num) (by norm_num) hr.1 gap_14621 hl.2
    (by norm_num) upper_reach_14593

theorem upper_reach_14627 : UpperReach 14627 144414889939519 := by
  have hr := row_14627
  have hl := log_bounds hr.1
    (by change logScale (14627 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14621) (H := 144318983695328) (u := 95906244115)
    (by norm_num) (by norm_num) hr.1 gap_14627 hl.2
    (by norm_num) upper_reach_14621

theorem upper_reach_14629 : UpperReach 14629 144510797550950 := by
  have hr := row_14629
  have hl := log_bounds hr.1
    (by change logScale (14629 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14627) (H := 144414889939519) (u := 95907611355)
    (by norm_num) (by norm_num) hr.1 gap_14629 hl.2
    (by norm_num) upper_reach_14627

theorem upper_reach_14633 : UpperReach 14633 144606707896303 := by
  have hr := row_14633
  have hl := log_bounds hr.1
    (by change logScale (14633 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14629) (H := 144510797550950) (u := 95910345277)
    (by norm_num) (by norm_num) hr.1 gap_14633 hl.2
    (by norm_num) upper_reach_14629

theorem upper_reach_14639 : UpperReach 14639 144702622341136 := by
  have hr := row_14639
  have hl := log_bounds hr.1
    (by change logScale (14639 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14633) (H := 144606707896303) (u := 95914444757)
    (by norm_num) (by norm_num) hr.1 gap_14639 hl.2
    (by norm_num) upper_reach_14633

theorem upper_reach_14653 : UpperReach 14653 144798546344894 := by
  have hr := row_14653
  have hl := log_bounds hr.1
    (by change logScale (14653 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14639) (H := 144702622341136) (u := 95924003682)
    (by norm_num) (by norm_num) hr.1 gap_14653 hl.2
    (by norm_num) upper_reach_14639

#print axioms upper_reach_14653

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
