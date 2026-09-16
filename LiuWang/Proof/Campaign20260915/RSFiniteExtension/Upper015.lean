import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper014
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block015

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_4099 : UpperReach 4099 40357254141828 := by
  have hr := row_4099
  have hl := log_bounds hr.1
    (by change logScale (4099 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4093) (H := 40274069158579) (u := 83184983173)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 17, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4093

theorem upper_reach_4111 : UpperReach 4111 40440468357741 := by
  have hr := row_4111
  have hl := log_bounds hr.1
    (by change logScale (4111 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4099) (H := 40357254141828) (u := 83214215837)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4099

theorem upper_reach_4127 : UpperReach 4127 40523721418083 := by
  have hr := row_4127
  have hl := log_bounds hr.1
    (by change logScale (4127 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4111) (H := 40440468357741) (u := 83253060266)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 23, 2, 3, 2, 13, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4111

theorem upper_reach_4129 : UpperReach 4129 40606979323386 := by
  have hr := row_4129
  have hl := log_bounds hr.1
    (by change logScale (4129 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4127) (H := 40523721418083) (u := 83257905227)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4127

theorem upper_reach_4133 : UpperReach 4133 40690246911575 := by
  have hr := row_4133
  have hl := log_bounds hr.1
    (by change logScale (4133 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4129) (H := 40606979323386) (u := 83267588113)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4129

theorem upper_reach_4139 : UpperReach 4139 40773529006537 := by
  have hr := row_4139
  have hl := log_bounds hr.1
    (by change logScale (4139 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4133) (H := 40690246911575) (u := 83282094886)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4133

theorem upper_reach_4153 : UpperReach 4153 40856844869018 := by
  have hr := row_4153
  have hl := log_bounds hr.1
    (by change logScale (4153 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4139) (H := 40773529006537) (u := 83315862405)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 41, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4139

theorem upper_reach_4157 : UpperReach 4157 40940170358455 := by
  have hr := row_4157
  have hl := log_bounds hr.1
    (by change logScale (4157 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4153) (H := 40856844869018) (u := 83325489361)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4153

theorem upper_reach_4159 : UpperReach 4159 41023500657897 := by
  have hr := row_4159
  have hl := log_bounds hr.1
    (by change logScale (4159 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4157) (H := 40940170358455) (u := 83330299366)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4157

theorem upper_reach_4177 : UpperReach 4177 41106874143586 := by
  have hr := row_4177
  have hl := log_bounds hr.1
    (by change logScale (4177 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4159) (H := 41023500657897) (u := 83373485613)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 23, 2, 5, 2, 3, 2, 11, 2, 43, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4159

theorem upper_reach_4201 : UpperReach 4201 41190304922342 := by
  have hr := row_4201
  have hl := log_bounds hr.1
    (by change logScale (4201 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4177) (H := 41106874143586) (u := 83430778680)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 37, 2, 47, 2, 3, 2, 53, 2, 59, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4177

theorem upper_reach_4211 : UpperReach 4211 41273759476668 := by
  have hr := row_4211
  have hl := log_bounds hr.1
    (by change logScale (4211 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4201) (H := 41190304922342) (u := 83454554250)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4201

theorem upper_reach_4217 : UpperReach 4217 41357228269250 := by
  have hr := row_4217
  have hl := log_bounds hr.1
    (by change logScale (4217 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4211) (H := 41273759476668) (u := 83468792506)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4211

theorem upper_reach_4219 : UpperReach 4219 41440701803416 := by
  have hr := row_4219
  have hl := log_bounds hr.1
    (by change logScale (4219 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4217) (H := 41357228269250) (u := 83473534090)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4217

theorem upper_reach_4229 : UpperReach 4229 41524199011835 := by
  have hr := row_4229
  have hl := log_bounds hr.1
    (by change logScale (4229 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4219) (H := 41440701803416) (u := 83497208343)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 41, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4219

theorem upper_reach_4231 : UpperReach 4231 41607700948387 := by
  have hr := row_4231
  have hl := log_bounds hr.1
    (by change logScale (4231 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4229) (H := 41524199011835) (u := 83501936476)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4229

theorem upper_reach_4241 : UpperReach 4241 41691226492126 := by
  have hr := row_4241
  have hl := log_bounds hr.1
    (by change logScale (4241 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4231) (H := 41607700948387) (u := 83525543663)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 19, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4231

theorem upper_reach_4243 : UpperReach 4243 41774756750622 := by
  have hr := row_4243
  have hl := log_bounds hr.1
    (by change logScale (4243 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4241) (H := 41691226492126) (u := 83530258420)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4241

theorem upper_reach_4253 : UpperReach 4253 41858310549619 := by
  have hr := row_4253
  have hl := log_bounds hr.1
    (by change logScale (4253 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4243) (H := 41774756750622) (u := 83553798921)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 31, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4243

theorem upper_reach_4259 : UpperReach 4259 41941878446363 := by
  have hr := row_4259
  have hl := log_bounds hr.1
    (by change logScale (4259 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4253) (H := 41858310549619) (u := 83567896668)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4253

theorem upper_reach_4261 : UpperReach 4261 42025451037942 := by
  have hr := row_4261
  have hl := log_bounds hr.1
    (by change logScale (4261 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4259) (H := 41941878446363) (u := 83572591503)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4259

theorem upper_reach_4271 : UpperReach 4271 42109047070695 := by
  have hr := row_4271
  have hl := log_bounds hr.1
    (by change logScale (4271 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4261) (H := 42025451037942) (u := 83596032677)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 17, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4261

theorem upper_reach_4273 : UpperReach 4273 42192647785096 := by
  have hr := row_4273
  have hl := log_bounds hr.1
    (by change logScale (4273 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4271) (H := 42109047070695) (u := 83600714325)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4271

theorem upper_reach_4283 : UpperReach 4283 42276271874916 := by
  have hr := row_4283
  have hl := log_bounds hr.1
    (by change logScale (4283 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4273) (H := 42192647785096) (u := 83624089744)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4273

#print axioms upper_reach_4283

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
