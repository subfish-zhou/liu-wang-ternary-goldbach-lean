import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper036
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block037

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_8761 : UpperReach 8761 86521784936406 := by
  have hr := row_8761
  have hl := log_bounds hr.1
    (by change logScale (8761 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8753) (H := 86431004283038) (u := 90780653292)
    (by norm_num) (by norm_num) hr.1 gap_8761 hl.2
    (by norm_num) upper_reach_8753

theorem upper_reach_8779 : UpperReach 8779 86612586114297 := by
  have hr := row_8779
  have hl := log_bounds hr.1
    (by change logScale (8779 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8761) (H := 86521784936406) (u := 90801177815)
    (by norm_num) (by norm_num) hr.1 gap_8779 hl.2
    (by norm_num) upper_reach_8761

theorem upper_reach_8783 : UpperReach 8783 86703391847478 := by
  have hr := row_8783
  have hl := log_bounds hr.1
    (by change logScale (8783 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8779) (H := 86612586114297) (u := 90805733105)
    (by norm_num) (by norm_num) hr.1 gap_8783 hl.2
    (by norm_num) upper_reach_8779

theorem upper_reach_8803 : UpperReach 8803 86794220326034 := by
  have hr := row_8803
  have hl := log_bounds hr.1
    (by change logScale (8803 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8783) (H := 86703391847478) (u := 90828478480)
    (by norm_num) (by norm_num) hr.1 gap_8803 hl.2
    (by norm_num) upper_reach_8783

theorem upper_reach_8807 : UpperReach 8807 86885053347464 := by
  have hr := row_8807
  have hl := log_bounds hr.1
    (by change logScale (8807 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8803) (H := 86794220326034) (u := 90833021354)
    (by norm_num) (by norm_num) hr.1 gap_8807 hl.2
    (by norm_num) upper_reach_8803

theorem upper_reach_8819 : UpperReach 8819 86975899985145 := by
  have hr := row_8819
  have hl := log_bounds hr.1
    (by change logScale (8819 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8807) (H := 86885053347464) (u := 90846637605)
    (by norm_num) (by norm_num) hr.1 gap_8819 hl.2
    (by norm_num) upper_reach_8807

theorem upper_reach_8821 : UpperReach 8821 87066748890399 := by
  have hr := row_8821
  have hl := log_bounds hr.1
    (by change logScale (8821 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8819) (H := 86975899985145) (u := 90848905178)
    (by norm_num) (by norm_num) hr.1 gap_8821 hl.2
    (by norm_num) upper_reach_8819

theorem upper_reach_8831 : UpperReach 8831 87157609125815 := by
  have hr := row_8831
  have hl := log_bounds hr.1
    (by change logScale (8831 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8821) (H := 87066748890399) (u := 90860235340)
    (by norm_num) (by norm_num) hr.1 gap_8831 hl.2
    (by norm_num) upper_reach_8821

theorem upper_reach_8837 : UpperReach 8837 87248476153172 := by
  have hr := row_8837
  have hl := log_bounds hr.1
    (by change logScale (8837 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8831) (H := 87157609125815) (u := 90867027281)
    (by norm_num) (by norm_num) hr.1 gap_8837 hl.2
    (by norm_num) upper_reach_8831

theorem upper_reach_8839 : UpperReach 8839 87339345443484 := by
  have hr := row_8839
  have hl := log_bounds hr.1
    (by change logScale (8839 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8837) (H := 87248476153172) (u := 90869290236)
    (by norm_num) (by norm_num) hr.1 gap_8839 hl.2
    (by norm_num) upper_reach_8837

theorem upper_reach_8849 : UpperReach 8849 87430226040898 := by
  have hr := row_8849
  have hl := log_bounds hr.1
    (by change logScale (8849 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8839) (H := 87339345443484) (u := 90880597338)
    (by norm_num) (by norm_num) hr.1 gap_8849 hl.2
    (by norm_num) upper_reach_8839

theorem upper_reach_8861 : UpperReach 8861 87521120189980 := by
  have hr := row_8861
  have hl := log_bounds hr.1
    (by change logScale (8861 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8849) (H := 87430226040898) (u := 90894149006)
    (by norm_num) (by norm_num) hr.1 gap_8861 hl.2
    (by norm_num) upper_reach_8849

theorem upper_reach_8863 : UpperReach 8863 87612016595889 := by
  have hr := row_8863
  have hl := log_bounds hr.1
    (by change logScale (8863 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8861) (H := 87521120189980) (u := 90896405833)
    (by norm_num) (by norm_num) hr.1 gap_8863 hl.2
    (by norm_num) upper_reach_8861

theorem upper_reach_8867 : UpperReach 8867 87702917513925 := by
  have hr := row_8867
  have hl := log_bounds hr.1
    (by change logScale (8867 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8863) (H := 87612016595889) (u := 90900917960)
    (by norm_num) (by norm_num) hr.1 gap_8867 hl.2
    (by norm_num) upper_reach_8863

theorem upper_reach_8887 : UpperReach 8887 87793840962104 := by
  have hr := row_8887
  have hl := log_bounds hr.1
    (by change logScale (8887 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8867) (H := 87702917513925) (u := 90923448103)
    (by norm_num) (by norm_num) hr.1 gap_8887 hl.2
    (by norm_num) upper_reach_8867

theorem upper_reach_8893 : UpperReach 8893 87884771159440 := by
  have hr := row_8893
  have hl := log_bounds hr.1
    (by change logScale (8893 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8887) (H := 87793840962104) (u := 90930197260)
    (by norm_num) (by norm_num) hr.1 gap_8893 hl.2
    (by norm_num) upper_reach_8887

theorem upper_reach_8923 : UpperReach 8923 87975735034401 := by
  have hr := row_8923
  have hl := log_bounds hr.1
    (by change logScale (8923 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8893) (H := 87884771159440) (u := 90963874885)
    (by norm_num) (by norm_num) hr.1 gap_8923 hl.2
    (by norm_num) upper_reach_8893

theorem upper_reach_8929 : UpperReach 8929 88066705631298 := by
  have hr := row_8929
  have hl := log_bounds hr.1
    (by change logScale (8929 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8923) (H := 87975735034401) (u := 90970596821)
    (by norm_num) (by norm_num) hr.1 gap_8929 hl.2
    (by norm_num) upper_reach_8923

theorem upper_reach_8933 : UpperReach 8933 88157680706977 := by
  have hr := row_8933
  have hl := log_bounds hr.1
    (by change logScale (8933 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8929) (H := 88066705631298) (u := 90975075603)
    (by norm_num) (by norm_num) hr.1 gap_8933 hl.2
    (by norm_num) upper_reach_8929

theorem upper_reach_8941 : UpperReach 8941 88248664734206 := by
  have hr := row_8941
  have hl := log_bounds hr.1
    (by change logScale (8941 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8933) (H := 88157680706977) (u := 90984027153)
    (by norm_num) (by norm_num) hr.1 gap_8941 hl.2
    (by norm_num) upper_reach_8933

theorem upper_reach_8951 : UpperReach 8951 88339659939616 := by
  have hr := row_8951
  have hl := log_bounds hr.1
    (by change logScale (8951 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8941) (H := 88248664734206) (u := 90995205334)
    (by norm_num) (by norm_num) hr.1 gap_8951 hl.2
    (by norm_num) upper_reach_8941

theorem upper_reach_8963 : UpperReach 8963 88430668542371 := by
  have hr := row_8963
  have hl := log_bounds hr.1
    (by change logScale (8963 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8951) (H := 88339659939616) (u := 91008602679)
    (by norm_num) (by norm_num) hr.1 gap_8963 hl.2
    (by norm_num) upper_reach_8951

theorem upper_reach_8969 : UpperReach 8969 88521683837074 := by
  have hr := row_8969
  have hl := log_bounds hr.1
    (by change logScale (8969 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8963) (H := 88430668542371) (u := 91015294627)
    (by norm_num) (by norm_num) hr.1 gap_8969 hl.2
    (by norm_num) upper_reach_8963

theorem upper_reach_8971 : UpperReach 8971 88612701361431 := by
  have hr := row_8971
  have hl := log_bounds hr.1
    (by change logScale (8971 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8969) (H := 88521683837074) (u := 91017524281)
    (by norm_num) (by norm_num) hr.1 gap_8971 hl.2
    (by norm_num) upper_reach_8969

#print axioms upper_reach_8971

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
