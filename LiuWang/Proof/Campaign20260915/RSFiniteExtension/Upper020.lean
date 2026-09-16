import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper019
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block020

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_5119 : UpperReach 5119 50481687307485 := by
  have hr := row_5119
  have hl := log_bounds hr.1
    (by change logScale (5119 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5113) (H := 50396280163576) (u := 85407143833)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5113

theorem upper_reach_5147 : UpperReach 5147 50567149000526 := by
  have hr := row_5147
  have hl := log_bounds hr.1
    (by change logScale (5147 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5119) (H := 50481687307485) (u := 85461692965)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 47, 2, 5, 2, 3, 2, 23, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 53, 2, 37, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5119

theorem upper_reach_5153 : UpperReach 5153 50652622344054 := by
  have hr := row_5153
  have hl := log_bounds hr.1
    (by change logScale (5153 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5147) (H := 50567149000526) (u := 85473343452)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 19, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5147

theorem upper_reach_5167 : UpperReach 5167 50738122819381 := by
  have hr := row_5167
  have hl := log_bounds hr.1
    (by change logScale (5167 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5153) (H := 50652622344054) (u := 85500475251)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5153

theorem upper_reach_5171 : UpperReach 5171 50823631033149 := by
  have hr := row_5171
  have hl := log_bounds hr.1
    (by change logScale (5171 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5167) (H := 50738122819381) (u := 85508213692)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5167

theorem upper_reach_5179 : UpperReach 5179 50909154705858 := by
  have hr := row_5179
  have hl := log_bounds hr.1
    (by change logScale (5179 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5171) (H := 50823631033149) (u := 85523672633)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 31, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5171

theorem upper_reach_5189 : UpperReach 5189 50994697668696 := by
  have hr := row_5189
  have hl := log_bounds hr.1
    (by change logScale (5189 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5179) (H := 50909154705858) (u := 85542962762)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 71, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5179

theorem upper_reach_5197 : UpperReach 5197 51080256036890 := by
  have hr := row_5197
  have hl := log_bounds hr.1
    (by change logScale (5197 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5189) (H := 50994697668696) (u := 85558368118)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 29, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5189

theorem upper_reach_5209 : UpperReach 5209 51165837468712 := by
  have hr := row_5209
  have hl := log_bounds hr.1
    (by change logScale (5209 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5197) (H := 51080256036890) (u := 85581431746)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 11, 2, 3, 2, 41, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5197

theorem upper_reach_5227 : UpperReach 5227 51251453396543 := by
  have hr := row_5227
  have hl := log_bounds hr.1
    (by change logScale (5227 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5209) (H := 51165837468712) (u := 85615927755)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 13, 2, 5, 2, 3, 2, 17, 2, 23, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5209

theorem upper_reach_5231 : UpperReach 5231 51337076974021 := by
  have hr := row_5231
  have hl := log_bounds hr.1
    (by change logScale (5231 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5227) (H := 51251453396543) (u := 85623577402)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5227

theorem upper_reach_5233 : UpperReach 5233 51422704374129 := by
  have hr := row_5233
  have hl := log_bounds hr.1
    (by change logScale (5233 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5231) (H := 51337076974021) (u := 85627400032)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5231

theorem upper_reach_5237 : UpperReach 5237 51508339415116 := by
  have hr := row_5237
  have hl := log_bounds hr.1
    (by change logScale (5237 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5233) (H := 51422704374129) (u := 85635040911)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5233

theorem upper_reach_5261 : UpperReach 5261 51594020179178 := by
  have hr := row_5261
  have hl := log_bounds hr.1
    (by change logScale (5261 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5237) (H := 51508339415116) (u := 85680763986)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 29, 2, 59, 2, 3, 2, 5, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5237

theorem upper_reach_5273 : UpperReach 5273 51679723726618 := by
  have hr := row_5273
  have hl := log_bounds hr.1
    (by change logScale (5273 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5261) (H := 51594020179178) (u := 85703547364)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 19, 2, 3, 2, 23, 2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5261

theorem upper_reach_5279 : UpperReach 5279 51765438646311 := by
  have hr := row_5279
  have hl := log_bounds hr.1
    (by change logScale (5279 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5273) (H := 51679723726618) (u := 85714919617)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5273

theorem upper_reach_5281 : UpperReach 5281 51851157353882 := by
  have hr := row_5281
  have hl := log_bounds hr.1
    (by change logScale (5281 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5279) (H := 51765438646311) (u := 85718707495)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5279

theorem upper_reach_5297 : UpperReach 5297 51936906312942 := by
  have hr := row_5297
  have hl := log_bounds hr.1
    (by change logScale (5297 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5281) (H := 51851157353882) (u := 85748958984)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 17, 2, 3, 2, 11, 2, 67, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5281

theorem upper_reach_5303 : UpperReach 5303 52022666592758 := by
  have hr := row_5303
  have hl := log_bounds hr.1
    (by change logScale (5303 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5297) (H := 51936906312942) (u := 85760279740)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5297

theorem upper_reach_5309 : UpperReach 5309 52108438180528 := by
  have hr := row_5309
  have hl := log_bounds hr.1
    (by change logScale (5309 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5303) (H := 52022666592758) (u := 85771587694)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5303

theorem upper_reach_5323 : UpperReach 5323 52194236103904 := by
  have hr := row_5323
  have hl := log_bounds hr.1
    (by change logScale (5323 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5309) (H := 52108438180528) (u := 85797923300)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 47, 2, 3, 2, 5, 2, 13, 2, 3, 2, 17, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5309

theorem upper_reach_5333 : UpperReach 5333 52280052796054 := by
  have hr := row_5333
  have hl := log_bounds hr.1
    (by change logScale (5333 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5323) (H := 52194236103904) (u := 85816692074)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 73, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5323

theorem upper_reach_5347 : UpperReach 5347 52365895705448 := by
  have hr := row_5347
  have hl := log_bounds hr.1
    (by change logScale (5347 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5333) (H := 52280052796054) (u := 85842909318)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 19, 2, 7, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5333

theorem upper_reach_5351 : UpperReach 5351 52451746092875 := by
  have hr := row_5351
  have hl := log_bounds hr.1
    (by change logScale (5351 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5347) (H := 52365895705448) (u := 85850387351)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5347

#print axioms upper_reach_5351

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
