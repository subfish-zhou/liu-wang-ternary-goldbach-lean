import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper027
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block028

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_6823 : UpperReach 6823 67170736897980 := by
  have hr := row_6823
  have hl := log_bounds hr.1
    (by change logScale (6823 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6803) (H := 67082456352568) (u := 88280545336)
    (by norm_num) (by norm_num) hr.1 gap_6823 hl.2
    (by norm_num) upper_reach_6803

theorem upper_reach_6827 : UpperReach 6827 67259023304198 := by
  have hr := row_6827
  have hl := log_bounds hr.1
    (by change logScale (6827 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6823) (H := 67170736897980) (u := 88286406142)
    (by norm_num) (by norm_num) hr.1 gap_6827 hl.2
    (by norm_num) upper_reach_6823

theorem upper_reach_6829 : UpperReach 6829 67347312639532 := by
  have hr := row_6829
  have hl := log_bounds hr.1
    (by change logScale (6829 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6827) (H := 67259023304198) (u := 88289335258)
    (by norm_num) (by norm_num) hr.1 gap_6829 hl.2
    (by norm_num) upper_reach_6827

theorem upper_reach_6833 : UpperReach 6833 67435607830524 := by
  have hr := row_6833
  have hl := log_bounds hr.1
    (by change logScale (6833 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6829) (H := 67347312639532) (u := 88295190916)
    (by norm_num) (by norm_num) hr.1 gap_6833 hl.2
    (by norm_num) upper_reach_6829

theorem upper_reach_6841 : UpperReach 6841 67523914722556 := by
  have hr := row_6841
  have hl := log_bounds hr.1
    (by change logScale (6841 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6833) (H := 67435607830524) (u := 88306891956)
    (by norm_num) (by norm_num) hr.1 gap_6841 hl.2
    (by norm_num) upper_reach_6833

theorem upper_reach_6857 : UpperReach 6857 67612244975673 := by
  have hr := row_6857
  have hl := log_bounds hr.1
    (by change logScale (6857 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6841) (H := 67523914722556) (u := 88330253041)
    (by norm_num) (by norm_num) hr.1 gap_6857 hl.2
    (by norm_num) upper_reach_6841

theorem upper_reach_6863 : UpperReach 6863 67700583975146 := by
  have hr := row_6863
  have hl := log_bounds hr.1
    (by change logScale (6863 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6857) (H := 67612244975673) (u := 88338999397)
    (by norm_num) (by norm_num) hr.1 gap_6863 hl.2
    (by norm_num) upper_reach_6857

theorem upper_reach_6869 : UpperReach 6869 67788931713332 := by
  have hr := row_6869
  have hl := log_bounds hr.1
    (by change logScale (6869 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6863) (H := 67700583975146) (u := 88347738110)
    (by norm_num) (by norm_num) hr.1 gap_6869 hl.2
    (by norm_num) upper_reach_6863

theorem upper_reach_6871 : UpperReach 6871 67877282362727 := by
  have hr := row_6871
  have hl := log_bounds hr.1
    (by change logScale (6871 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6869) (H := 67788931713332) (u := 88350649319)
    (by norm_num) (by norm_num) hr.1 gap_6871 hl.2
    (by norm_num) upper_reach_6869

theorem upper_reach_6883 : UpperReach 6883 67965650461595 := by
  have hr := row_6883
  have hl := log_bounds hr.1
    (by change logScale (6883 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6871) (H := 67877282362727) (u := 88368098792)
    (by norm_num) (by norm_num) hr.1 gap_6883 hl.2
    (by norm_num) upper_reach_6871

theorem upper_reach_6899 : UpperReach 6899 68054041779165 := by
  have hr := row_6899
  have hl := log_bounds hr.1
    (by change logScale (6899 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6883) (H := 67965650461595) (u := 88391317494)
    (by norm_num) (by norm_num) hr.1 gap_6899 hl.2
    (by norm_num) upper_reach_6883

theorem upper_reach_6907 : UpperReach 6907 68142444685900 := by
  have hr := row_6907
  have hl := log_bounds hr.1
    (by change logScale (6907 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6899) (H := 68054041779165) (u := 88402906659)
    (by norm_num) (by norm_num) hr.1 gap_6907 hl.2
    (by norm_num) upper_reach_6899

theorem upper_reach_6911 : UpperReach 6911 68230853382185 := by
  have hr := row_6911
  have hl := log_bounds hr.1
    (by change logScale (6911 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6907) (H := 68142444685900) (u := 88408696209)
    (by norm_num) (by norm_num) hr.1 gap_6911 hl.2
    (by norm_num) upper_reach_6907

theorem upper_reach_6917 : UpperReach 6917 68319270756515 := by
  have hr := row_6917
  have hl := log_bounds hr.1
    (by change logScale (6917 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6911) (H := 68230853382185) (u := 88417374254)
    (by norm_num) (by norm_num) hr.1 gap_6917 hl.2
    (by norm_num) upper_reach_6911

theorem upper_reach_6947 : UpperReach 6947 68407731408466 := by
  have hr := row_6947
  have hl := log_bounds hr.1
    (by change logScale (6947 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6917) (H := 68319270756515) (u := 88460651875)
    (by norm_num) (by norm_num) hr.1 gap_6947 hl.2
    (by norm_num) upper_reach_6917

theorem upper_reach_6949 : UpperReach 6949 68496194938943 := by
  have hr := row_6949
  have hl := log_bounds hr.1
    (by change logScale (6949 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6947) (H := 68407731408466) (u := 88463530401)
    (by norm_num) (by norm_num) hr.1 gap_6949 hl.2
    (by norm_num) upper_reach_6947

theorem upper_reach_6959 : UpperReach 6959 68584672849636 := by
  have hr := row_6959
  have hl := log_bounds hr.1
    (by change logScale (6959 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6949) (H := 68496194938943) (u := 88477910617)
    (by norm_num) (by norm_num) hr.1 gap_6959 hl.2
    (by norm_num) upper_reach_6949

theorem upper_reach_6961 : UpperReach 6961 68673153633892 := by
  have hr := row_6961
  have hl := log_bounds hr.1
    (by change logScale (6961 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6959) (H := 68584672849636) (u := 88480784180)
    (by norm_num) (by norm_num) hr.1 gap_6961 hl.2
    (by norm_num) upper_reach_6959

theorem upper_reach_6967 : UpperReach 6967 68761643033887 := by
  have hr := row_6967
  have hl := log_bounds hr.1
    (by change logScale (6967 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6961) (H := 68673153633892) (u := 88489399919)
    (by norm_num) (by norm_num) hr.1 gap_6967 hl.2
    (by norm_num) upper_reach_6961

theorem upper_reach_6971 : UpperReach 6971 68850138173586 := by
  have hr := row_6971
  have hl := log_bounds hr.1
    (by change logScale (6971 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6967) (H := 68761643033887) (u := 88495139623)
    (by norm_num) (by norm_num) hr.1 gap_6971 hl.2
    (by norm_num) upper_reach_6967

theorem upper_reach_6977 : UpperReach 6977 68938641916670 := by
  have hr := row_6977
  have hl := log_bounds hr.1
    (by change logScale (6977 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6971) (H := 68850138173586) (u := 88503743008)
    (by norm_num) (by norm_num) hr.1 gap_6977 hl.2
    (by norm_num) upper_reach_6971

theorem upper_reach_6983 : UpperReach 6983 69027154255743 := by
  have hr := row_6983
  have hl := log_bounds hr.1
    (by change logScale (6983 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6977) (H := 68938641916670) (u := 88512338997)
    (by norm_num) (by norm_num) hr.1 gap_6983 hl.2
    (by norm_num) upper_reach_6977

theorem upper_reach_6991 : UpperReach 6991 69115678044652 := by
  have hr := row_6991
  have hl := log_bounds hr.1
    (by change logScale (6991 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6983) (H := 69027154255743) (u := 88523788833)
    (by norm_num) (by norm_num) hr.1 gap_6991 hl.2
    (by norm_num) upper_reach_6983

theorem upper_reach_6997 : UpperReach 6997 69204210412344 := by
  have hr := row_6997
  have hl := log_bounds hr.1
    (by change logScale (6997 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6991) (H := 69115678044652) (u := 88532367616)
    (by norm_num) (by norm_num) hr.1 gap_6997 hl.2
    (by norm_num) upper_reach_6991

#print axioms upper_reach_6997

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
