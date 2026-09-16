import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper057
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block058

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_13469 : UpperReach 13469 133432398752793 := by
  have hr := row_13469
  have hl := log_bounds hr.1
    (by change logScale (13469 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13463) (H := 133337317292475) (u := 95081460242)
    (by norm_num) (by norm_num) hr.1 gap_13469 hl.2
    (by norm_num) upper_reach_13463

theorem upper_reach_13477 : UpperReach 13477 133527486150912 := by
  have hr := row_13477
  have hl := log_bounds hr.1
    (by change logScale (13477 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13469) (H := 133432398752793) (u := 95087398043)
    (by norm_num) (by norm_num) hr.1 gap_13477 hl.2
    (by norm_num) upper_reach_13469

theorem upper_reach_13487 : UpperReach 13487 133622580966329 := by
  have hr := row_13487
  have hl := log_bounds hr.1
    (by change logScale (13487 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13477) (H := 133527486150912) (u := 95094815341)
    (by norm_num) (by norm_num) hr.1 gap_13487 hl.2
    (by norm_num) upper_reach_13477

theorem upper_reach_13499 : UpperReach 13499 133717684675247 := by
  have hr := row_13499
  have hl := log_bounds hr.1
    (by change logScale (13499 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13487) (H := 133622580966329) (u := 95103708842)
    (by norm_num) (by norm_num) hr.1 gap_13499 hl.2
    (by norm_num) upper_reach_13487

theorem upper_reach_13513 : UpperReach 13513 133812798749929 := by
  have hr := row_13513
  have hl := log_bounds hr.1
    (by change logScale (13513 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13499) (H := 133717684675247) (u := 95114074606)
    (by norm_num) (by norm_num) hr.1 gap_13513 hl.2
    (by norm_num) upper_reach_13499

theorem upper_reach_13523 : UpperReach 13523 133907920222155 := by
  have hr := row_13523
  have hl := log_bounds hr.1
    (by change logScale (13523 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13513) (H := 133812798749929) (u := 95121472150)
    (by norm_num) (by norm_num) hr.1 gap_13523 hl.2
    (by norm_num) upper_reach_13513

theorem upper_reach_13537 : UpperReach 13537 134003052041759 := by
  have hr := row_13537
  have hl := log_bounds hr.1
    (by change logScale (13537 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13523) (H := 133907920222155) (u := 95131819528)
    (by norm_num) (by norm_num) hr.1 gap_13537 hl.2
    (by norm_num) upper_reach_13523

theorem upper_reach_13553 : UpperReach 13553 134098195673841 := by
  have hr := row_13553
  have hl := log_bounds hr.1
    (by change logScale (13553 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13537) (H := 134003052041759) (u := 95143632006)
    (by norm_num) (by norm_num) hr.1 gap_13553 hl.2
    (by norm_num) upper_reach_13537

theorem upper_reach_13567 : UpperReach 13567 134193349630408 := by
  have hr := row_13567
  have hl := log_bounds hr.1
    (by change logScale (13567 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13553) (H := 134098195673841) (u := 95153956491)
    (by norm_num) (by norm_num) hr.1 gap_13567 hl.2
    (by norm_num) upper_reach_13553

theorem upper_reach_13577 : UpperReach 13577 134288510955086 := by
  have hr := row_13577
  have hl := log_bounds hr.1
    (by change logScale (13577 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13567) (H := 134193349630408) (u := 95161324602)
    (by norm_num) (by norm_num) hr.1 gap_13577 hl.2
    (by norm_num) upper_reach_13567

theorem upper_reach_13591 : UpperReach 13591 134383682586007 := by
  have hr := row_13591
  have hl := log_bounds hr.1
    (by change logScale (13591 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13577) (H := 134288510955086) (u := 95171630845)
    (by norm_num) (by norm_num) hr.1 gap_13591 hl.2
    (by norm_num) upper_reach_13577

theorem upper_reach_13597 : UpperReach 13597 134478858630640 := by
  have hr := row_13597
  have hl := log_bounds hr.1
    (by change logScale (13597 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13591) (H := 134383682586007) (u := 95176044557)
    (by norm_num) (by norm_num) hr.1 gap_13597 hl.2
    (by norm_num) upper_reach_13591

theorem upper_reach_13613 : UpperReach 13613 134574046435657 := by
  have hr := row_13613
  have hl := log_bounds hr.1
    (by change logScale (13613 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13597) (H := 134478858630640) (u := 95187804941)
    (by norm_num) (by norm_num) hr.1 gap_13613 hl.2
    (by norm_num) upper_reach_13597

theorem upper_reach_13619 : UpperReach 13619 134669238647254 := by
  have hr := row_13619
  have hl := log_bounds hr.1
    (by change logScale (13619 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13613) (H := 134574046435657) (u := 95192211521)
    (by norm_num) (by norm_num) hr.1 gap_13619 hl.2
    (by norm_num) upper_reach_13613

theorem upper_reach_13627 : UpperReach 13627 134764436731273 := by
  have hr := row_13627
  have hl := log_bounds hr.1
    (by change logScale (13627 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13619) (H := 134669238647254) (u := 95198083943)
    (by norm_num) (by norm_num) hr.1 gap_13627 hl.2
    (by norm_num) upper_reach_13619

theorem upper_reach_13633 : UpperReach 13633 134859639217347 := by
  have hr := row_13633
  have hl := log_bounds hr.1
    (by change logScale (13633 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13627) (H := 134764436731273) (u := 95202485998)
    (by norm_num) (by norm_num) hr.1 gap_13633 hl.2
    (by norm_num) upper_reach_13627

theorem upper_reach_13649 : UpperReach 13649 134954853432767 := by
  have hr := row_13649
  have hl := log_bounds hr.1
    (by change logScale (13649 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13633) (H := 134859639217347) (u := 95214215344)
    (by norm_num) (by norm_num) hr.1 gap_13649 hl.2
    (by norm_num) upper_reach_13633

theorem upper_reach_13669 : UpperReach 13669 135050082290550 := by
  have hr := row_13669
  have hl := log_bounds hr.1
    (by change logScale (13669 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13649) (H := 134954853432767) (u := 95228857707)
    (by norm_num) (by norm_num) hr.1 gap_13669 hl.2
    (by norm_num) upper_reach_13649

theorem upper_reach_13679 : UpperReach 13679 135145318461483 := by
  have hr := row_13679
  have hl := log_bounds hr.1
    (by change logScale (13679 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13669) (H := 135050082290550) (u := 95236170857)
    (by norm_num) (by norm_num) hr.1 gap_13679 hl.2
    (by norm_num) upper_reach_13669

theorem upper_reach_13681 : UpperReach 13681 135240556094404 := by
  have hr := row_13681
  have hl := log_bounds hr.1
    (by change logScale (13681 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13679) (H := 135145318461483) (u := 95237632845)
    (by norm_num) (by norm_num) hr.1 gap_13681 hl.2
    (by norm_num) upper_reach_13679

theorem upper_reach_13687 : UpperReach 13687 135335798112008 := by
  have hr := row_13687
  have hl := log_bounds hr.1
    (by change logScale (13687 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13681) (H := 135240556094404) (u := 95242017528)
    (by norm_num) (by norm_num) hr.1 gap_13687 hl.2
    (by norm_num) upper_reach_13681

theorem upper_reach_13691 : UpperReach 13691 135431043051666 := by
  have hr := row_13691
  have hl := log_bounds hr.1
    (by change logScale (13691 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13687) (H := 135335798112008) (u := 95244939582)
    (by norm_num) (by norm_num) hr.1 gap_13691 hl.2
    (by norm_num) upper_reach_13687

theorem upper_reach_13693 : UpperReach 13693 135526289452031 := by
  have hr := row_13693
  have hl := log_bounds hr.1
    (by change logScale (13693 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13691) (H := 135431043051666) (u := 95246400289)
    (by norm_num) (by norm_num) hr.1 gap_13693 hl.2
    (by norm_num) upper_reach_13691

theorem upper_reach_13697 : UpperReach 13697 135621538773170 := by
  have hr := row_13697
  have hl := log_bounds hr.1
    (by change logScale (13697 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13693) (H := 135526289452031) (u := 95249321063)
    (by norm_num) (by norm_num) hr.1 gap_13697 hl.2
    (by norm_num) upper_reach_13693

#print axioms upper_reach_13697

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
