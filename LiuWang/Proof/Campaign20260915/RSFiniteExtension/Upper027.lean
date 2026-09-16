import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper026
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block027

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_6599 : UpperReach 6599 65055836744601 := by
  have hr := row_6599
  have hl := log_bounds hr.1
    (by change logScale (6599 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6581) (H := 64967890010543) (u := 87946733982)
    (by norm_num) (by norm_num) hr.1 gap_6599 hl.2
    (by norm_num) upper_reach_6581

theorem upper_reach_6607 : UpperReach 6607 65143795594366 := by
  have hr := row_6607
  have hl := log_bounds hr.1
    (by change logScale (6607 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6599) (H := 65055836744601) (u := 87958849689)
    (by norm_num) (by norm_num) hr.1 gap_6607 hl.2
    (by norm_num) upper_reach_6599

theorem upper_reach_6619 : UpperReach 6619 65231772590211 := by
  have hr := row_6619
  have hl := log_bounds hr.1
    (by change logScale (6619 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6607) (H := 65143795594366) (u := 87976995769)
    (by norm_num) (by norm_num) hr.1 gap_6619 hl.2
    (by norm_num) upper_reach_6607

theorem upper_reach_6637 : UpperReach 6637 65319776743587 := by
  have hr := row_6637
  have hl := log_bounds hr.1
    (by change logScale (6637 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6619) (H := 65231772590211) (u := 88004153300)
    (by norm_num) (by norm_num) hr.1 gap_6637 hl.2
    (by norm_num) upper_reach_6619

theorem upper_reach_6653 : UpperReach 6653 65407804975229 := by
  have hr := row_6653
  have hl := log_bounds hr.1
    (by change logScale (6653 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6637) (H := 65319776743587) (u := 88028231566)
    (by norm_num) (by norm_num) hr.1 gap_6653 hl.2
    (by norm_num) upper_reach_6637

theorem upper_reach_6659 : UpperReach 6659 65495842221294 := by
  have hr := row_6659
  have hl := log_bounds hr.1
    (by change logScale (6659 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6653) (H := 65407804975229) (u := 88037245989)
    (by norm_num) (by norm_num) hr.1 gap_6659 hl.2
    (by norm_num) upper_reach_6653

theorem upper_reach_6661 : UpperReach 6661 65583882470362 := by
  have hr := row_6661
  have hl := log_bounds hr.1
    (by change logScale (6661 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6659) (H := 65495842221294) (u := 88040248992)
    (by norm_num) (by norm_num) hr.1 gap_6661 hl.2
    (by norm_num) upper_reach_6659

theorem upper_reach_6673 : UpperReach 6673 65671940718535 := by
  have hr := row_6673
  have hl := log_bounds hr.1
    (by change logScale (6673 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6661) (H := 65583882470362) (u := 88058248097)
    (by norm_num) (by norm_num) hr.1 gap_6673 hl.2
    (by norm_num) upper_reach_6661

theorem upper_reach_6679 : UpperReach 6679 65760007954127 := by
  have hr := row_6679
  have hl := log_bounds hr.1
    (by change logScale (6679 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6673) (H := 65671940718535) (u := 88067235516)
    (by norm_num) (by norm_num) hr.1 gap_6679 hl.2
    (by norm_num) upper_reach_6673

theorem upper_reach_6689 : UpperReach 6689 65848090150822 := by
  have hr := row_6689
  have hl := log_bounds hr.1
    (by change logScale (6689 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6679) (H := 65760007954127) (u := 88082196619)
    (by norm_num) (by norm_num) hr.1 gap_6689 hl.2
    (by norm_num) upper_reach_6679

theorem upper_reach_6691 : UpperReach 6691 65936175337054 := by
  have hr := row_6691
  have hl := log_bounds hr.1
    (by change logScale (6691 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6689) (H := 65848090150822) (u := 88085186156)
    (by norm_num) (by norm_num) hr.1 gap_6691 hl.2
    (by norm_num) upper_reach_6689

theorem upper_reach_6701 : UpperReach 6701 66024275457578 := by
  have hr := row_6701
  have hl := log_bounds hr.1
    (by change logScale (6701 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6691) (H := 65936175337054) (u := 88100120448)
    (by norm_num) (by norm_num) hr.1 gap_6701 hl.2
    (by norm_num) upper_reach_6691

theorem upper_reach_6703 : UpperReach 6703 66112378562286 := by
  have hr := row_6703
  have hl := log_bounds hr.1
    (by change logScale (6703 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6701) (H := 66024275457578) (u := 88103104632)
    (by norm_num) (by norm_num) hr.1 gap_6703 hl.2
    (by norm_num) upper_reach_6701

theorem upper_reach_6709 : UpperReach 6709 66200490614206 := by
  have hr := row_6709
  have hl := log_bounds hr.1
    (by change logScale (6709 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6703) (H := 66112378562286) (u := 88112051844)
    (by norm_num) (by norm_num) hr.1 gap_6709 hl.2
    (by norm_num) upper_reach_6703

theorem upper_reach_6719 : UpperReach 6719 66288617560380 := by
  have hr := row_6719
  have hl := log_bounds hr.1
    (by change logScale (6719 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6709) (H := 66200490614206) (u := 88126946098)
    (by norm_num) (by norm_num) hr.1 gap_6719 hl.2
    (by norm_num) upper_reach_6709

theorem upper_reach_6733 : UpperReach 6733 66376765321310 := by
  have hr := row_6733
  have hl := log_bounds hr.1
    (by change logScale (6733 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6719) (H := 66288617560380) (u := 88147760854)
    (by norm_num) (by norm_num) hr.1 gap_6733 hl.2
    (by norm_num) upper_reach_6719

theorem upper_reach_6737 : UpperReach 6737 66464919021364 := by
  have hr := row_6737
  have hl := log_bounds hr.1
    (by change logScale (6737 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6733) (H := 66376765321310) (u := 88153699978)
    (by norm_num) (by norm_num) hr.1 gap_6737 hl.2
    (by norm_num) upper_reach_6733

theorem upper_reach_6761 : UpperReach 6761 66553108282279 := by
  have hr := row_6761
  have hl := log_bounds hr.1
    (by change logScale (6761 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6737) (H := 66464919021364) (u := 88189260839)
    (by norm_num) (by norm_num) hr.1 gap_6761 hl.2
    (by norm_num) upper_reach_6737

theorem upper_reach_6763 : UpperReach 6763 66641300500899 := by
  have hr := row_6763
  have hl := log_bounds hr.1
    (by change logScale (6763 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6761) (H := 66553108282279) (u := 88192218544)
    (by norm_num) (by norm_num) hr.1 gap_6763 hl.2
    (by norm_num) upper_reach_6761

theorem upper_reach_6779 : UpperReach 6779 66729516349718 := by
  have hr := row_6779
  have hl := log_bounds hr.1
    (by change logScale (6779 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6763) (H := 66641300500899) (u := 88215848743)
    (by norm_num) (by norm_num) hr.1 gap_6779 hl.2
    (by norm_num) upper_reach_6763

theorem upper_reach_6781 : UpperReach 6781 66817735148389 := by
  have hr := row_6781
  have hl := log_bounds hr.1
    (by change logScale (6781 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6779) (H := 66729516349718) (u := 88218798595)
    (by norm_num) (by norm_num) hr.1 gap_6781 hl.2
    (by norm_num) upper_reach_6779

theorem upper_reach_6791 : UpperReach 6791 66905968683284 := by
  have hr := row_6791
  have hl := log_bounds hr.1
    (by change logScale (6791 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6781) (H := 66817735148389) (u := 88233534819)
    (by norm_num) (by norm_num) hr.1 gap_6791 hl.2
    (by norm_num) upper_reach_6781

theorem upper_reach_6793 : UpperReach 6793 66994205162820 := by
  have hr := row_6793
  have hl := log_bounds hr.1
    (by change logScale (6793 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6791) (H := 66905968683284) (u := 88236479460)
    (by norm_num) (by norm_num) hr.1 gap_6793 hl.2
    (by norm_num) upper_reach_6791

theorem upper_reach_6803 : UpperReach 6803 67082456352568 := by
  have hr := row_6803
  have hl := log_bounds hr.1
    (by change logScale (6803 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6793) (H := 66994205162820) (u := 88251189672)
    (by norm_num) (by norm_num) hr.1 gap_6803 hl.2
    (by norm_num) upper_reach_6793

#print axioms upper_reach_6803

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
