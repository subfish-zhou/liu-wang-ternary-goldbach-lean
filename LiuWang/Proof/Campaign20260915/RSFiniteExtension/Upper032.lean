import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper031
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block032

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_7673 : UpperReach 7673 75703283397435 := by
  have hr := row_7673
  have hl := log_bounds hr.1
    (by change logScale (7673 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7669) (H := 75613828767869) (u := 89454629490)
    (by norm_num) (by norm_num) hr.1 gap_7673 hl.2
    (by norm_num) upper_reach_7669

theorem upper_reach_7681 : UpperReach 7681 75792748447739 := by
  have hr := row_7681
  have hl := log_bounds hr.1
    (by change logScale (7681 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7673) (H := 75703283397435) (u := 89465050228)
    (by norm_num) (by norm_num) hr.1 gap_7681 hl.2
    (by norm_num) upper_reach_7673

theorem upper_reach_7687 : UpperReach 7687 75882221306477 := by
  have hr := row_7687
  have hl := log_bounds hr.1
    (by change logScale (7687 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7681) (H := 75792748447739) (u := 89472858662)
    (by norm_num) (by norm_num) hr.1 gap_7687 hl.2
    (by norm_num) upper_reach_7681

theorem upper_reach_7691 : UpperReach 7691 75971699367452 := by
  have hr := row_7691
  have hl := log_bounds hr.1
    (by change logScale (7691 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7687) (H := 75882221306477) (u := 89478060899)
    (by norm_num) (by norm_num) hr.1 gap_7691 hl.2
    (by norm_num) upper_reach_7687

theorem upper_reach_7699 : UpperReach 7699 76061187824789 := by
  have hr := row_7699
  have hl := log_bounds hr.1
    (by change logScale (7699 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7691) (H := 75971699367452) (u := 89488457261)
    (by norm_num) (by norm_num) hr.1 gap_7699 hl.2
    (by norm_num) upper_reach_7691

theorem upper_reach_7703 : UpperReach 7703 76150681476257 := by
  have hr := row_7703
  have hl := log_bounds hr.1
    (by change logScale (7703 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7699) (H := 76061187824789) (u := 89493651392)
    (by norm_num) (by norm_num) hr.1 gap_7703 hl.2
    (by norm_num) upper_reach_7699

theorem upper_reach_7717 : UpperReach 7717 76240193285966 := by
  have hr := row_7717
  have hl := log_bounds hr.1
    (by change logScale (7717 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7703) (H := 76150681476257) (u := 89511809633)
    (by norm_num) (by norm_num) hr.1 gap_7717 hl.2
    (by norm_num) upper_reach_7703

theorem upper_reach_7723 : UpperReach 7723 76329712867696 := by
  have hr := row_7723
  have hl := log_bounds hr.1
    (by change logScale (7723 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7717) (H := 76240193285966) (u := 89519581654)
    (by norm_num) (by norm_num) hr.1 gap_7723 hl.2
    (by norm_num) upper_reach_7717

theorem upper_reach_7727 : UpperReach 7727 76419237627420 := by
  have hr := row_7727
  have hl := log_bounds hr.1
    (by change logScale (7727 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7723) (H := 76329712867696) (u := 89524759648)
    (by norm_num) (by norm_num) hr.1 gap_7727 hl.2
    (by norm_num) upper_reach_7723

theorem upper_reach_7741 : UpperReach 7741 76508780489036 := by
  have hr := row_7741
  have hl := log_bounds hr.1
    (by change logScale (7741 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7727) (H := 76419237627420) (u := 89542861540)
    (by norm_num) (by norm_num) hr.1 gap_7741 hl.2
    (by norm_num) upper_reach_7727

theorem upper_reach_7753 : UpperReach 7753 76598338840522 := by
  have hr := row_7753
  have hl := log_bounds hr.1
    (by change logScale (7753 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7741) (H := 76508780489036) (u := 89558351410)
    (by norm_num) (by norm_num) hr.1 gap_7753 hl.2
    (by norm_num) upper_reach_7741

theorem upper_reach_7757 : UpperReach 7757 76687902349971 := by
  have hr := row_7757
  have hl := log_bounds hr.1
    (by change logScale (7757 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7753) (H := 76598338840522) (u := 89563509373)
    (by norm_num) (by norm_num) hr.1 gap_7757 hl.2
    (by norm_num) upper_reach_7753

theorem upper_reach_7759 : UpperReach 7759 76777468437404 := by
  have hr := row_7759
  have hl := log_bounds hr.1
    (by change logScale (7759 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7757) (H := 76687902349971) (u := 89566087357)
    (by norm_num) (by norm_num) hr.1 gap_7759 hl.2
    (by norm_num) upper_reach_7757

theorem upper_reach_7789 : UpperReach 7789 76867073115057 := by
  have hr := row_7789
  have hl := log_bounds hr.1
    (by change logScale (7789 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7759) (H := 76777468437404) (u := 89604677577)
    (by norm_num) (by norm_num) hr.1 gap_7789 hl.2
    (by norm_num) upper_reach_7759

theorem upper_reach_7793 : UpperReach 7793 76956682926840 := by
  have hr := row_7793
  have hl := log_bounds hr.1
    (by change logScale (7793 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7789) (H := 76867073115057) (u := 89609811707)
    (by norm_num) (by norm_num) hr.1 gap_7793 hl.2
    (by norm_num) upper_reach_7789

theorem upper_reach_7817 : UpperReach 7817 77046323488166 := by
  have hr := row_7817
  have hl := log_bounds hr.1
    (by change logScale (7817 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7793) (H := 76956682926840) (u := 89640561250)
    (by norm_num) (by norm_num) hr.1 gap_7817 hl.2
    (by norm_num) upper_reach_7793

theorem upper_reach_7823 : UpperReach 7823 77135971722127 := by
  have hr := row_7823
  have hl := log_bounds hr.1
    (by change logScale (7823 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7817) (H := 77046323488166) (u := 89648233885)
    (by norm_num) (by norm_num) hr.1 gap_7823 hl.2
    (by norm_num) upper_reach_7817

theorem upper_reach_7829 : UpperReach 7829 77225627622840 := by
  have hr := row_7829
  have hl := log_bounds hr.1
    (by change logScale (7829 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7823) (H := 77135971722127) (u := 89655900637)
    (by norm_num) (by norm_num) hr.1 gap_7829 hl.2
    (by norm_num) upper_reach_7823

theorem upper_reach_7841 : UpperReach 7841 77315298839447 := by
  have hr := row_7841
  have hl := log_bounds hr.1
    (by change logScale (7841 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7829) (H := 77225627622840) (u := 89671216531)
    (by norm_num) (by norm_num) hr.1 gap_7841 hl.2
    (by norm_num) upper_reach_7829

theorem upper_reach_7853 : UpperReach 7853 77404985348525 := by
  have hr := row_7853
  have hl := log_bounds hr.1
    (by change logScale (7853 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7841) (H := 77315298839447) (u := 89686509002)
    (by norm_num) (by norm_num) hr.1 gap_7853 hl.2
    (by norm_num) upper_reach_7841

theorem upper_reach_7867 : UpperReach 7867 77494689669313 := by
  have hr := row_7867
  have hl := log_bounds hr.1
    (by change logScale (7867 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7853) (H := 77404985348525) (u := 89704320712)
    (by norm_num) (by norm_num) hr.1 gap_7867 hl.2
    (by norm_num) upper_reach_7853

theorem upper_reach_7873 : UpperReach 7873 77584401613989 := by
  have hr := row_7873
  have hl := log_bounds hr.1
    (by change logScale (7873 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7867) (H := 77494689669313) (u := 89711944600)
    (by norm_num) (by norm_num) hr.1 gap_7873 hl.2
    (by norm_num) upper_reach_7867

theorem upper_reach_7877 : UpperReach 7877 77674118638030 := by
  have hr := row_7877
  have hl := log_bounds hr.1
    (by change logScale (7877 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7873) (H := 77584401613989) (u := 89717023965)
    (by norm_num) (by norm_num) hr.1 gap_7877 hl.2
    (by norm_num) upper_reach_7873

theorem upper_reach_7879 : UpperReach 7879 77763838200787 := by
  have hr := row_7879
  have hl := log_bounds hr.1
    (by change logScale (7879 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7877) (H := 77674118638030) (u := 89719562681)
    (by norm_num) (by norm_num) hr.1 gap_7879 hl.2
    (by norm_num) upper_reach_7877

#print axioms upper_reach_7879

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
