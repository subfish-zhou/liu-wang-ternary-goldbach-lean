import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper054
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block055

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_12791 : UpperReach 12791 126604996465960 := by
  have hr := row_12791
  have hl := log_bounds hr.1
    (by change logScale (12791 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12781) (H := 126510431495142) (u := 94564970742)
    (by norm_num) (by norm_num) hr.1 gap_12791 hl.2
    (by norm_num) upper_reach_12781

theorem upper_reach_12799 : UpperReach 12799 126699567689220 := by
  have hr := row_12799
  have hl := log_bounds hr.1
    (by change logScale (12799 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12791) (H := 126604996465960) (u := 94571223184)
    (by norm_num) (by norm_num) hr.1 gap_12799 hl.2
    (by norm_num) upper_reach_12791

theorem upper_reach_12809 : UpperReach 12809 126794146722540 := by
  have hr := row_12809
  have hl := log_bounds hr.1
    (by change logScale (12809 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12799) (H := 126699567689220) (u := 94579033244)
    (by norm_num) (by norm_num) hr.1 gap_12809 hl.2
    (by norm_num) upper_reach_12799

theorem upper_reach_12821 : UpperReach 12821 126888735119887 := by
  have hr := row_12821
  have hl := log_bounds hr.1
    (by change logScale (12821 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12809) (H := 126794146722540) (u := 94588397271)
    (by norm_num) (by norm_num) hr.1 gap_12821 hl.2
    (by norm_num) upper_reach_12809

theorem upper_reach_12823 : UpperReach 12823 126983325077053 := by
  have hr := row_12823
  have hl := log_bounds hr.1
    (by change logScale (12823 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12821) (H := 126888735119887) (u := 94589957090)
    (by norm_num) (by norm_num) hr.1 gap_12823 hl.2
    (by norm_num) upper_reach_12821

theorem upper_reach_12829 : UpperReach 12829 127077919712217 := by
  have hr := row_12829
  have hl := log_bounds hr.1
    (by change logScale (12829 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12823) (H := 126983325077053) (u := 94594635088)
    (by norm_num) (by norm_num) hr.1 gap_12829 hl.2
    (by norm_num) upper_reach_12823

theorem upper_reach_12841 : UpperReach 12841 127172523696817 := by
  have hr := row_12841
  have hl := log_bounds hr.1
    (by change logScale (12841 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12829) (H := 127077919712217) (u := 94603984524)
    (by norm_num) (by norm_num) hr.1 gap_12841 hl.2
    (by norm_num) upper_reach_12829

theorem upper_reach_12853 : UpperReach 12853 127267137022120 := by
  have hr := row_12853
  have hl := log_bounds hr.1
    (by change logScale (12853 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12841) (H := 127172523696817) (u := 94613325227)
    (by norm_num) (by norm_num) hr.1 gap_12853 hl.2
    (by norm_num) upper_reach_12841

theorem upper_reach_12889 : UpperReach 12889 127361778317296 := by
  have hr := row_12889
  have hl := log_bounds hr.1
    (by change logScale (12889 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12853) (H := 127267137022120) (u := 94641295100)
    (by norm_num) (by norm_num) hr.1 gap_12889 hl.2
    (by norm_num) upper_reach_12853

theorem upper_reach_12893 : UpperReach 12893 127456422715412 := by
  have hr := row_12893
  have hl := log_bounds hr.1
    (by change logScale (12893 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12889) (H := 127361778317296) (u := 94644398040)
    (by norm_num) (by norm_num) hr.1 gap_12893 hl.2
    (by norm_num) upper_reach_12889

theorem upper_reach_12899 : UpperReach 12899 127551071766133 := by
  have hr := row_12899
  have hl := log_bounds hr.1
    (by change logScale (12899 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12893) (H := 127456422715412) (u := 94649050645)
    (by norm_num) (by norm_num) hr.1 gap_12899 hl.2
    (by norm_num) upper_reach_12893

theorem upper_reach_12907 : UpperReach 12907 127645727016963 := by
  have hr := row_12907
  have hl := log_bounds hr.1
    (by change logScale (12907 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12899) (H := 127551071766133) (u := 94655250754)
    (by norm_num) (by norm_num) hr.1 gap_12907 hl.2
    (by norm_num) upper_reach_12899

theorem upper_reach_12911 : UpperReach 12911 127740385366406 := by
  have hr := row_12911
  have hl := log_bounds hr.1
    (by change logScale (12911 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12907) (H := 127645727016963) (u := 94658349367)
    (by norm_num) (by norm_num) hr.1 gap_12911 hl.2
    (by norm_num) upper_reach_12907

theorem upper_reach_12917 : UpperReach 12917 127835048361970 := by
  have hr := row_12917
  have hl := log_bounds hr.1
    (by change logScale (12917 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12911) (H := 127740385366406) (u := 94662995488)
    (by norm_num) (by norm_num) hr.1 gap_12917 hl.2
    (by norm_num) upper_reach_12911

theorem upper_reach_12919 : UpperReach 12919 127929712905761 := by
  have hr := row_12919
  have hl := log_bounds hr.1
    (by change logScale (12919 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12917) (H := 127835048361970) (u := 94664543715)
    (by norm_num) (by norm_num) hr.1 gap_12919 hl.2
    (by norm_num) upper_reach_12917

theorem upper_reach_12923 : UpperReach 12923 128024380545288 := by
  have hr := row_12923
  have hl := log_bounds hr.1
    (by change logScale (12923 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12919) (H := 127929712905761) (u := 94667639451)
    (by norm_num) (by norm_num) hr.1 gap_12923 hl.2
    (by norm_num) upper_reach_12919

theorem upper_reach_12941 : UpperReach 12941 128119062103778 := by
  have hr := row_12941
  have hl := log_bounds hr.1
    (by change logScale (12941 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12923) (H := 128024380545288) (u := 94681558414)
    (by norm_num) (by norm_num) hr.1 gap_12941 hl.2
    (by norm_num) upper_reach_12923

theorem upper_reach_12953 : UpperReach 12953 128213752930825 := by
  have hr := row_12953
  have hl := log_bounds hr.1
    (by change logScale (12953 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12941) (H := 128119062103778) (u := 94690826971)
    (by norm_num) (by norm_num) hr.1 gap_12953 hl.2
    (by norm_num) upper_reach_12941

theorem upper_reach_12959 : UpperReach 12959 128308448388931 := by
  have hr := row_12959
  have hl := log_bounds hr.1
    (by change logScale (12959 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12953) (H := 128213752930825) (u := 94695458030)
    (by norm_num) (by norm_num) hr.1 gap_12959 hl.2
    (by norm_num) upper_reach_12953

theorem upper_reach_12967 : UpperReach 12967 128403150018448 := by
  have hr := row_12967
  have hl := log_bounds hr.1
    (by change logScale (12967 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12959) (H := 128308448388931) (u := 94701629441)
    (by norm_num) (by norm_num) hr.1 gap_12967 hl.2
    (by norm_num) upper_reach_12959

theorem upper_reach_12973 : UpperReach 12973 128497856274025 := by
  have hr := row_12973
  have hl := log_bounds hr.1
    (by change logScale (12973 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12967) (H := 128403150018448) (u := 94706255501)
    (by norm_num) (by norm_num) hr.1 gap_12973 hl.2
    (by norm_num) upper_reach_12967

theorem upper_reach_12979 : UpperReach 12979 128592567153524 := by
  have hr := row_12979
  have hl := log_bounds hr.1
    (by change logScale (12979 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12973) (H := 128497856274025) (u := 94710879423)
    (by norm_num) (by norm_num) hr.1 gap_12979 hl.2
    (by norm_num) upper_reach_12973

theorem upper_reach_12983 : UpperReach 12983 128687281114449 := by
  have hr := row_12983
  have hl := log_bounds hr.1
    (by change logScale (12983 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12979) (H := 128592567153524) (u := 94713960849)
    (by norm_num) (by norm_num) hr.1 gap_12983 hl.2
    (by norm_num) upper_reach_12979

theorem upper_reach_13001 : UpperReach 13001 128782008930056 := by
  have hr := row_13001
  have hl := log_bounds hr.1
    (by change logScale (13001 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12983) (H := 128687281114449) (u := 94727815531)
    (by norm_num) (by norm_num) hr.1 gap_13001 hl.2
    (by norm_num) upper_reach_12983

#print axioms upper_reach_13001

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
