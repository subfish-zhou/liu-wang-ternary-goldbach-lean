import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper049
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block050

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_11701 : UpperReach 11701 115309126619722 := by
  have hr := row_11701
  have hl := log_bounds hr.1
    (by change logScale (11701 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11699) (H := 115215452323808) (u := 93674295838)
    (by norm_num) (by norm_num) hr.1 gap_11701 hl.2
    (by norm_num) upper_reach_11699

theorem upper_reach_11717 : UpperReach 11717 115402814580340 := by
  have hr := row_11717
  have hl := log_bounds hr.1
    (by change logScale (11717 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11701) (H := 115309126619722) (u := 93687960542)
    (by norm_num) (by norm_num) hr.1 gap_11717 hl.2
    (by norm_num) upper_reach_11701

theorem upper_reach_11719 : UpperReach 11719 115496504247734 := by
  have hr := row_11719
  have hl := log_bounds hr.1
    (by change logScale (11719 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11717) (H := 115402814580340) (u := 93689667318)
    (by norm_num) (by norm_num) hr.1 gap_11719 hl.2
    (by norm_num) upper_reach_11717

theorem upper_reach_11731 : UpperReach 11731 115590204149671 := by
  have hr := row_11731
  have hl := log_bounds hr.1
    (by change logScale (11731 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11719) (H := 115496504247734) (u := 93699901861)
    (by norm_num) (by norm_num) hr.1 gap_11731 hl.2
    (by norm_num) upper_reach_11719

theorem upper_reach_11743 : UpperReach 11743 115683914275686 := by
  have hr := row_11743
  have hl := log_bounds hr.1
    (by change logScale (11743 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11731) (H := 115590204149671) (u := 93710125939)
    (by norm_num) (by norm_num) hr.1 gap_11743 hl.2
    (by norm_num) upper_reach_11731

theorem upper_reach_11777 : UpperReach 11777 115777653313286 := by
  have hr := row_11777
  have hl := log_bounds hr.1
    (by change logScale (11777 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11743) (H := 115683914275686) (u := 93739037524)
    (by norm_num) (by norm_num) hr.1 gap_11777 hl.2
    (by norm_num) upper_reach_11743

theorem upper_reach_11779 : UpperReach 11779 115871394048967 := by
  have hr := row_11779
  have hl := log_bounds hr.1
    (by change logScale (11779 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11777) (H := 115777653313286) (u := 93740735605)
    (by norm_num) (by norm_num) hr.1 gap_11779 hl.2
    (by norm_num) upper_reach_11777

theorem upper_reach_11783 : UpperReach 11783 115965138179946 := by
  have hr := row_11783
  have hl := log_bounds hr.1
    (by change logScale (11783 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11779) (H := 115871394048967) (u := 93744130903)
    (by norm_num) (by norm_num) hr.1 gap_11783 hl.2
    (by norm_num) upper_reach_11779

theorem upper_reach_11789 : UpperReach 11789 116058887401711 := by
  have hr := row_11789
  have hl := log_bounds hr.1
    (by change logScale (11789 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11783) (H := 115965138179946) (u := 93749221689)
    (by norm_num) (by norm_num) hr.1 gap_11789 hl.2
    (by norm_num) upper_reach_11783

theorem upper_reach_11801 : UpperReach 11801 116152646797279 := by
  have hr := row_11801
  have hl := log_bounds hr.1
    (by change logScale (11801 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11789) (H := 116058887401711) (u := 93759395492)
    (by norm_num) (by norm_num) hr.1 gap_11801 hl.2
    (by norm_num) upper_reach_11789

theorem upper_reach_11807 : UpperReach 11807 116246411275870 := by
  have hr := row_11807
  have hl := log_bounds hr.1
    (by change logScale (11807 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11801) (H := 116152646797279) (u := 93764478515)
    (by norm_num) (by norm_num) hr.1 gap_11807 hl.2
    (by norm_num) upper_reach_11801

theorem upper_reach_11813 : UpperReach 11813 116340180834901 := by
  have hr := row_11813
  have hl := log_bounds hr.1
    (by change logScale (11813 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11807) (H := 116246411275870) (u := 93769558955)
    (by norm_num) (by norm_num) hr.1 gap_11813 hl.2
    (by norm_num) upper_reach_11807

theorem upper_reach_11821 : UpperReach 11821 116433957163840 := by
  have hr := row_11821
  have hl := log_bounds hr.1
    (by change logScale (11821 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11813) (H := 116340180834901) (u := 93776328863)
    (by norm_num) (by norm_num) hr.1 gap_11821 hl.2
    (by norm_num) upper_reach_11813

theorem upper_reach_11827 : UpperReach 11827 116527738567204 := by
  have hr := row_11827
  have hl := log_bounds hr.1
    (by change logScale (11827 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11821) (H := 116433957163840) (u := 93781403288)
    (by norm_num) (by norm_num) hr.1 gap_11827 hl.2
    (by norm_num) upper_reach_11821

theorem upper_reach_11831 : UpperReach 11831 116621523352088 := by
  have hr := row_11831
  have hl := log_bounds hr.1
    (by change logScale (11831 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11827) (H := 116527738567204) (u := 93784784808)
    (by norm_num) (by norm_num) hr.1 gap_11831 hl.2
    (by norm_num) upper_reach_11827

theorem upper_reach_11833 : UpperReach 11833 116715309827304 := by
  have hr := row_11833
  have hl := log_bounds hr.1
    (by change logScale (11833 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11831) (H := 116621523352088) (u := 93786475140)
    (by norm_num) (by norm_num) hr.1 gap_11833 hl.2
    (by norm_num) upper_reach_11831

theorem upper_reach_11839 : UpperReach 11839 116809101371800 := by
  have hr := row_11839
  have hl := log_bounds hr.1
    (by change logScale (11839 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11833) (H := 116715309827304) (u := 93791544420)
    (by norm_num) (by norm_num) hr.1 gap_11839 hl.2
    (by norm_num) upper_reach_11833

theorem upper_reach_11863 : UpperReach 11863 116902913167758 := by
  have hr := row_11863
  have hl := log_bounds hr.1
    (by change logScale (11863 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11839) (H := 116809101371800) (u := 93811795882)
    (by norm_num) (by norm_num) hr.1 gap_11863 hl.2
    (by norm_num) upper_reach_11839

theorem upper_reach_11867 : UpperReach 11867 116996728334976 := by
  have hr := row_11867
  have hl := log_bounds hr.1
    (by change logScale (11867 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11863) (H := 116902913167758) (u := 93815167142)
    (by norm_num) (by norm_num) hr.1 gap_11867 hl.2
    (by norm_num) upper_reach_11863

theorem upper_reach_11887 : UpperReach 11887 117090560341468 := by
  have hr := row_11887
  have hl := log_bounds hr.1
    (by change logScale (11887 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11867) (H := 116996728334976) (u := 93832006416)
    (by norm_num) (by norm_num) hr.1 gap_11887 hl.2
    (by norm_num) upper_reach_11867

theorem upper_reach_11897 : UpperReach 11897 117184400756974 := by
  have hr := row_11897
  have hl := log_bounds hr.1
    (by change logScale (11897 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11887) (H := 117090560341468) (u := 93840415430)
    (by norm_num) (by norm_num) hr.1 gap_11897 hl.2
    (by norm_num) upper_reach_11887

theorem upper_reach_11903 : UpperReach 11903 117278246214497 := by
  have hr := row_11903
  have hl := log_bounds hr.1
    (by change logScale (11903 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11897) (H := 117184400756974) (u := 93845457447)
    (by norm_num) (by norm_num) hr.1 gap_11903 hl.2
    (by norm_num) upper_reach_11897

theorem upper_reach_11909 : UpperReach 11909 117372096711496 := by
  have hr := row_11909
  have hl := log_bounds hr.1
    (by change logScale (11909 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11903) (H := 117278246214497) (u := 93850496923)
    (by norm_num) (by norm_num) hr.1 gap_11909 hl.2
    (by norm_num) upper_reach_11903

theorem upper_reach_11923 : UpperReach 11923 117465958957406 := by
  have hr := row_11923
  have hl := log_bounds hr.1
    (by change logScale (11923 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11909) (H := 117372096711496) (u := 93862245834)
    (by norm_num) (by norm_num) hr.1 gap_11923 hl.2
    (by norm_num) upper_reach_11909

#print axioms upper_reach_11923

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
