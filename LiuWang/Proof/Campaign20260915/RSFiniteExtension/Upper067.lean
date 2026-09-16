import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper066
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block067

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_15541 : UpperReach 15541 154131894562470 := by
  have hr := row_15541
  have hl := log_bounds hr.1
    (by change logScale (15541 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15527) (H := 154035382192709) (u := 96512369685)
    (by norm_num) (by norm_num) hr.1 gap_15541 hl.2
    (by norm_num) upper_reach_15527

theorem upper_reach_15551 : UpperReach 15551 154228413364754 := by
  have hr := row_15551
  have hl := log_bounds hr.1
    (by change logScale (15551 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15541) (H := 154131894562470) (u := 96518802208)
    (by norm_num) (by norm_num) hr.1 gap_15551 hl.2
    (by norm_num) upper_reach_15541

theorem upper_reach_15559 : UpperReach 15559 154324937310079 := by
  have hr := row_15559
  have hl := log_bounds hr.1
    (by change logScale (15559 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15551) (H := 154228413364754) (u := 96523945249)
    (by norm_num) (by norm_num) hr.1 gap_15559 hl.2
    (by norm_num) upper_reach_15551

theorem upper_reach_15569 : UpperReach 15569 154421467680488 := by
  have hr := row_15569
  have hl := log_bounds hr.1
    (by change logScale (15569 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15559) (H := 154324937310079) (u := 96530370333)
    (by norm_num) (by norm_num) hr.1 gap_15569 hl.2
    (by norm_num) upper_reach_15559

theorem upper_reach_15581 : UpperReach 15581 154518005755552 := by
  have hr := row_15581
  have hl := log_bounds hr.1
    (by change logScale (15581 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15569) (H := 154421467680488) (u := 96538074988)
    (by norm_num) (by norm_num) hr.1 gap_15581 hl.2
    (by norm_num) upper_reach_15569

theorem upper_reach_15583 : UpperReach 15583 154614545114148 := by
  have hr := row_15583
  have hl := log_bounds hr.1
    (by change logScale (15583 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15581) (H := 154518005755552) (u := 96539358520)
    (by norm_num) (by norm_num) hr.1 gap_15583 hl.2
    (by norm_num) upper_reach_15581

theorem upper_reach_15601 : UpperReach 15601 154711096017127 := by
  have hr := row_15601
  have hl := log_bounds hr.1
    (by change logScale (15601 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15583) (H := 154614545114148) (u := 96550902903)
    (by norm_num) (by norm_num) hr.1 gap_15601 hl.2
    (by norm_num) upper_reach_15583

theorem upper_reach_15607 : UpperReach 15607 154807650765274 := by
  have hr := row_15607
  have hl := log_bounds hr.1
    (by change logScale (15607 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15601) (H := 154711096017127) (u := 96554748071)
    (by norm_num) (by norm_num) hr.1 gap_15607 hl.2
    (by norm_num) upper_reach_15601

theorem upper_reach_15619 : UpperReach 15619 154904213199324 := by
  have hr := row_15619
  have hl := log_bounds hr.1
    (by change logScale (15619 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15607) (H := 154807650765274) (u := 96562433974)
    (by norm_num) (by norm_num) hr.1 gap_15619 hl.2
    (by norm_num) upper_reach_15607

theorem upper_reach_15629 : UpperReach 15629 155000782033784 := by
  have hr := row_15629
  have hl := log_bounds hr.1
    (by change logScale (15629 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15619) (H := 154904213199324) (u := 96568834384)
    (by norm_num) (by norm_num) hr.1 gap_15629 hl.2
    (by norm_num) upper_reach_15619

theorem upper_reach_15641 : UpperReach 15641 155097358543332 := by
  have hr := row_15641
  have hl := log_bounds hr.1
    (by change logScale (15641 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15629) (H := 155000782033784) (u := 96576509472)
    (by norm_num) (by norm_num) hr.1 gap_15641 hl.2
    (by norm_num) upper_reach_15629

theorem upper_reach_15643 : UpperReach 15643 155193936331489 := by
  have hr := row_15643
  have hl := log_bounds hr.1
    (by change logScale (15643 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15641) (H := 155097358543332) (u := 96577788081)
    (by norm_num) (by norm_num) hr.1 gap_15643 hl.2
    (by norm_num) upper_reach_15641

theorem upper_reach_15647 : UpperReach 15647 155290516676374 := by
  have hr := row_15647
  have hl := log_bounds hr.1
    (by change logScale (15647 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15643) (H := 155193936331489) (u := 96580344809)
    (by norm_num) (by norm_num) hr.1 gap_15647 hl.2
    (by norm_num) upper_reach_15643

theorem upper_reach_15649 : UpperReach 15649 155387098299377 := by
  have hr := row_15649
  have hl := log_bounds hr.1
    (by change logScale (15649 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15647) (H := 155290516676374) (u := 96581622927)
    (by norm_num) (by norm_num) hr.1 gap_15649 hl.2
    (by norm_num) upper_reach_15647

theorem upper_reach_15661 : UpperReach 15661 155483687587663 := by
  have hr := row_15661
  have hl := log_bounds hr.1
    (by change logScale (15661 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15649) (H := 155387098299377) (u := 96589288210)
    (by norm_num) (by norm_num) hr.1 gap_15661 hl.2
    (by norm_num) upper_reach_15649

theorem upper_reach_15667 : UpperReach 15667 155580280706389 := by
  have hr := row_15667
  have hl := log_bounds hr.1
    (by change logScale (15667 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15661) (H := 155483687587663) (u := 96593118650)
    (by norm_num) (by norm_num) hr.1 gap_15667 hl.2
    (by norm_num) upper_reach_15661

theorem upper_reach_15671 : UpperReach 15671 155676876377926 := by
  have hr := row_15671
  have hl := log_bounds hr.1
    (by change logScale (15671 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15667) (H := 155580280706389) (u := 96595671461)
    (by norm_num) (by norm_num) hr.1 gap_15671 hl.2
    (by norm_num) upper_reach_15667

theorem upper_reach_15679 : UpperReach 15679 155773477153131 := by
  have hr := row_15679
  have hl := log_bounds hr.1
    (by change logScale (15679 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15671) (H := 155676876377926) (u := 96600775129)
    (by norm_num) (by norm_num) hr.1 gap_15679 hl.2
    (by norm_num) upper_reach_15671

theorem upper_reach_15683 : UpperReach 15683 155870080479194 := by
  have hr := row_15683
  have hl := log_bounds hr.1
    (by change logScale (15683 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15679) (H := 155773477153131) (u := 96603325987)
    (by norm_num) (by norm_num) hr.1 gap_15683 hl.2
    (by norm_num) upper_reach_15679

theorem upper_reach_15727 : UpperReach 15727 155966711821831 := by
  have hr := row_15727
  have hl := log_bounds hr.1
    (by change logScale (15727 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15683) (H := 155870080479194) (u := 96631342561)
    (by norm_num) (by norm_num) hr.1 gap_15727 hl.2
    (by norm_num) upper_reach_15683

theorem upper_reach_15731 : UpperReach 15731 156063345707541 := by
  have hr := row_15731
  have hl := log_bounds hr.1
    (by change logScale (15731 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15727) (H := 155966711821831) (u := 96633885634)
    (by norm_num) (by norm_num) hr.1 gap_15731 hl.2
    (by norm_num) upper_reach_15727

theorem upper_reach_15733 : UpperReach 15733 156159980864545 := by
  have hr := row_15733
  have hl := log_bounds hr.1
    (by change logScale (15733 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15731) (H := 156063345707541) (u := 96635156928)
    (by norm_num) (by norm_num) hr.1 gap_15733 hl.2
    (by norm_num) upper_reach_15731

theorem upper_reach_15737 : UpperReach 15737 156256618563653 := by
  have hr := row_15737
  have hl := log_bounds hr.1
    (by change logScale (15737 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15733) (H := 156159980864545) (u := 96637699032)
    (by norm_num) (by norm_num) hr.1 gap_15737 hl.2
    (by norm_num) upper_reach_15733

theorem upper_reach_15739 : UpperReach 15739 156353257533570 := by
  have hr := row_15739
  have hl := log_bounds hr.1
    (by change logScale (15739 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15737) (H := 156256618563653) (u := 96638969841)
    (by norm_num) (by norm_num) hr.1 gap_15739 hl.2
    (by norm_num) upper_reach_15737

#print axioms upper_reach_15739

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
