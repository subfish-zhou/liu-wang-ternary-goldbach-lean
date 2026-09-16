import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper046
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block047

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_10979 : UpperReach 10979 108587321615787 := by
  have hr := row_10979
  have hl := log_bounds hr.1
    (by change logScale (10979 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10973) (H := 108494284219383) (u := 93037396328)
    (by norm_num) (by norm_num) hr.1 gap_10979 hl.2
    (by norm_num) upper_reach_10973

theorem upper_reach_10987 : UpperReach 10987 108680366296176 := by
  have hr := row_10987
  have hl := log_bounds hr.1
    (by change logScale (10987 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10979) (H := 108587321615787) (u := 93044680313)
    (by norm_num) (by norm_num) hr.1 gap_10987 hl.2
    (by norm_num) upper_reach_10979

theorem upper_reach_10993 : UpperReach 10993 108773416436073 := by
  have hr := row_10993
  have hl := log_bounds hr.1
    (by change logScale (10993 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10987) (H := 108680366296176) (u := 93050139821)
    (by norm_num) (by norm_num) hr.1 gap_10993 hl.2
    (by norm_num) upper_reach_10987

theorem upper_reach_11003 : UpperReach 11003 108866475668533 := by
  have hr := row_11003
  have hl := log_bounds hr.1
    (by change logScale (11003 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10993) (H := 108773416436073) (u := 93059232384)
    (by norm_num) (by norm_num) hr.1 gap_11003 hl.2
    (by norm_num) upper_reach_10993

theorem upper_reach_11027 : UpperReach 11027 108959556689472 := by
  have hr := row_11027
  have hl := log_bounds hr.1
    (by change logScale (11027 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11003) (H := 108866475668533) (u := 93081020863)
    (by norm_num) (by norm_num) hr.1 gap_11027 hl.2
    (by norm_num) upper_reach_11003

theorem upper_reach_11047 : UpperReach 11047 109052655831282 := by
  have hr := row_11047
  have hl := log_bounds hr.1
    (by change logScale (11047 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11027) (H := 108959556689472) (u := 93099141734)
    (by norm_num) (by norm_num) hr.1 gap_11047 hl.2
    (by norm_num) upper_reach_11027

theorem upper_reach_11057 : UpperReach 11057 109145764021229 := by
  have hr := row_11057
  have hl := log_bounds hr.1
    (by change logScale (11057 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11047) (H := 109052655831282) (u := 93108189871)
    (by norm_num) (by norm_num) hr.1 gap_11057 hl.2
    (by norm_num) upper_reach_11047

theorem upper_reach_11059 : UpperReach 11059 109238874019821 := by
  have hr := row_11059
  have hl := log_bounds hr.1
    (by change logScale (11059 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11057) (H := 109145764021229) (u := 93109998516)
    (by norm_num) (by norm_num) hr.1 gap_11059 hl.2
    (by norm_num) upper_reach_11057

theorem upper_reach_11069 : UpperReach 11069 109331993056737 := by
  have hr := row_11069
  have hl := log_bounds hr.1
    (by change logScale (11069 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11059) (H := 109238874019821) (u := 93119036840)
    (by norm_num) (by norm_num) hr.1 gap_11069 hl.2
    (by norm_num) upper_reach_11059

theorem upper_reach_11071 : UpperReach 11071 109425113900337 := by
  have hr := row_11071
  have hl := log_bounds hr.1
    (by change logScale (11071 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11069) (H := 109331993056737) (u := 93120843524)
    (by norm_num) (by norm_num) hr.1 gap_11071 hl.2
    (by norm_num) upper_reach_11069

theorem upper_reach_11083 : UpperReach 11083 109518245577196 := by
  have hr := row_11083
  have hl := log_bounds hr.1
    (by change logScale (11083 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11071) (H := 109425113900337) (u := 93131676783)
    (by norm_num) (by norm_num) hr.1 gap_11083 hl.2
    (by norm_num) upper_reach_11071

theorem upper_reach_11087 : UpperReach 11087 109611380862535 := by
  have hr := row_11087
  have hl := log_bounds hr.1
    (by change logScale (11087 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11083) (H := 109518245577196) (u := 93135285263)
    (by norm_num) (by norm_num) hr.1 gap_11087 hl.2
    (by norm_num) upper_reach_11083

theorem upper_reach_11093 : UpperReach 11093 109704521558154 := by
  have hr := row_11093
  have hl := log_bounds hr.1
    (by change logScale (11093 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11087) (H := 109611380862535) (u := 93140695543)
    (by norm_num) (by norm_num) hr.1 gap_11093 hl.2
    (by norm_num) upper_reach_11087

theorem upper_reach_11113 : UpperReach 11113 109797680266928 := by
  have hr := row_11113
  have hl := log_bounds hr.1
    (by change logScale (11113 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11093) (H := 109704521558154) (u := 93158708698)
    (by norm_num) (by norm_num) hr.1 gap_11113 hl.2
    (by norm_num) upper_reach_11093

theorem upper_reach_11117 : UpperReach 11117 109890842574442 := by
  have hr := row_11117
  have hl := log_bounds hr.1
    (by change logScale (11117 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11113) (H := 109797680266928) (u := 93162307438)
    (by norm_num) (by norm_num) hr.1 gap_11117 hl.2
    (by norm_num) upper_reach_11113

theorem upper_reach_11119 : UpperReach 11119 109984006680841 := by
  have hr := row_11119
  have hl := log_bounds hr.1
    (by change logScale (11119 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11117) (H := 109890842574442) (u := 93164106323)
    (by norm_num) (by norm_num) hr.1 gap_11119 hl.2
    (by norm_num) upper_reach_11117

theorem upper_reach_11131 : UpperReach 11131 110077181573758 := by
  have hr := row_11131
  have hl := log_bounds hr.1
    (by change logScale (11131 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11119) (H := 109984006680841) (u := 93174892841)
    (by norm_num) (by norm_num) hr.1 gap_11131 hl.2
    (by norm_num) upper_reach_11119

theorem upper_reach_11149 : UpperReach 11149 110170372624667 := by
  have hr := row_11149
  have hl := log_bounds hr.1
    (by change logScale (11149 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11131) (H := 110077181573758) (u := 93191050833)
    (by norm_num) (by norm_num) hr.1 gap_11149 hl.2
    (by norm_num) upper_reach_11131

theorem upper_reach_11159 : UpperReach 11159 110263572640971 := by
  have hr := row_11159
  have hl := log_bounds hr.1
    (by change logScale (11159 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11149) (H := 110170372624667) (u := 93200016228)
    (by norm_num) (by norm_num) hr.1 gap_11159 hl.2
    (by norm_num) upper_reach_11149

theorem upper_reach_11161 : UpperReach 11161 110356774449389 := by
  have hr := row_11161
  have hl := log_bounds hr.1
    (by change logScale (11161 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11159) (H := 110263572640971) (u := 93201808342)
    (by norm_num) (by norm_num) hr.1 gap_11161 hl.2
    (by norm_num) upper_reach_11159

theorem upper_reach_11171 : UpperReach 11171 110449985213566 := by
  have hr := row_11171
  have hl := log_bounds hr.1
    (by change logScale (11171 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11161) (H := 110356774449389) (u := 93210764101)
    (by norm_num) (by norm_num) hr.1 gap_11171 hl.2
    (by norm_num) upper_reach_11161

theorem upper_reach_11173 : UpperReach 11173 110543197767933 := by
  have hr := row_11173
  have hl := log_bounds hr.1
    (by change logScale (11173 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11171) (H := 110449985213566) (u := 93212554291)
    (by norm_num) (by norm_num) hr.1 gap_11173 hl.2
    (by norm_num) upper_reach_11171

theorem upper_reach_11177 : UpperReach 11177 110636413901719 := by
  have hr := row_11177
  have hl := log_bounds hr.1
    (by change logScale (11177 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11173) (H := 110543197767933) (u := 93216133710)
    (by norm_num) (by norm_num) hr.1 gap_11177 hl.2
    (by norm_num) upper_reach_11173

theorem upper_reach_11197 : UpperReach 11197 110729647913403 := by
  have hr := row_11197
  have hl := log_bounds hr.1
    (by change logScale (11197 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11177) (H := 110636413901719) (u := 93234011608)
    (by norm_num) (by norm_num) hr.1 gap_11197 hl.2
    (by norm_num) upper_reach_11177

#print axioms upper_reach_11197

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
