import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper024
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block025

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_6197 : UpperReach 6197 60850253389140 := by
  have hr := row_6197
  have hl := log_bounds hr.1
    (by change logScale (6197 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6173) (H := 60762935183266) (u := 87318205798)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 37, 2, 7, 2, 3, 2, 5, 2, 23, 2, 3, 2, 41, 2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6173

theorem upper_reach_6199 : UpperReach 6199 60937574821861 := by
  have hr := row_6199
  have hl := log_bounds hr.1
    (by change logScale (6199 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6197) (H := 60850253389140) (u := 87321432645)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6197

theorem upper_reach_6203 : UpperReach 6203 61024902705155 := by
  have hr := row_6203
  have hl := log_bounds hr.1
    (by change logScale (6203 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6199) (H := 60937574821861) (u := 87327883218)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6199

theorem upper_reach_6211 : UpperReach 6211 61112243477125 := by
  have hr := row_6211
  have hl := log_bounds hr.1
    (by change logScale (6211 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6203) (H := 61024902705155) (u := 87340771894)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6203

theorem upper_reach_6217 : UpperReach 6217 61199593904712 := by
  have hr := row_6217
  have hl := log_bounds hr.1
    (by change logScale (6217 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6211) (H := 61112243477125) (u := 87350427511)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6211

theorem upper_reach_6221 : UpperReach 6221 61286950764201 := by
  have hr := row_6221
  have hl := log_bounds hr.1
    (by change logScale (6221 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6217) (H := 61199593904712) (u := 87356859413)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6217

theorem upper_reach_6229 : UpperReach 6229 61374320475098 := by
  have hr := row_6229
  have hl := log_bounds hr.1
    (by change logScale (6229 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6221) (H := 61286950764201) (u := 87369710821)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6221

theorem upper_reach_6247 : UpperReach 6247 61461719041417 := by
  have hr := row_6247
  have hl := log_bounds hr.1
    (by change logScale (6247 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6229) (H := 61374320475098) (u := 87398566243)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 23, 2, 5, 2, 3, 2, 17, 2, 79, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6229

theorem upper_reach_6257 : UpperReach 6257 61549133602621 := by
  have hr := row_6257
  have hl := log_bounds hr.1
    (by change logScale (6257 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6247) (H := 61461719041417) (u := 87414561128)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6247

theorem upper_reach_6263 : UpperReach 6263 61636557748491 := by
  have hr := row_6263
  have hl := log_bounds hr.1
    (by change logScale (6263 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6257) (H := 61549133602621) (u := 87424145794)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6257

theorem upper_reach_6269 : UpperReach 6269 61723991469848 := by
  have hr := row_6269
  have hl := log_bounds hr.1
    (by change logScale (6269 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6263) (H := 61636557748491) (u := 87433721281)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6263

theorem upper_reach_6271 : UpperReach 6271 61811428380998 := by
  have hr := row_6271
  have hl := log_bounds hr.1
    (by change logScale (6271 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6269) (H := 61723991469848) (u := 87436911074)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6269

theorem upper_reach_6277 : UpperReach 6277 61898874855425 := by
  have hr := row_6277
  have hl := log_bounds hr.1
    (by change logScale (6277 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6271) (H := 61811428380998) (u := 87446474351)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6271

theorem upper_reach_6287 : UpperReach 6287 61986337248353 := by
  have hr := row_6287
  have hl := log_bounds hr.1
    (by change logScale (6287 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6277) (H := 61898874855425) (u := 87462392852)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 61, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6277

theorem upper_reach_6299 : UpperReach 6299 62073818710094 := by
  have hr := row_6299
  have hl := log_bounds hr.1
    (by change logScale (6299 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6287) (H := 61986337248353) (u := 87481461665)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 19, 2, 3, 2, 7, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6287

theorem upper_reach_6301 : UpperReach 6301 62161303346438 := by
  have hr := row_6301
  have hl := log_bounds hr.1
    (by change logScale (6301 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6299) (H := 62073818710094) (u := 87484636268)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6299

theorem upper_reach_6311 : UpperReach 6311 62248803840698 := by
  have hr := row_6311
  have hl := log_bounds hr.1
    (by change logScale (6311 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6301) (H := 62161303346438) (u := 87500494184)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6301

theorem upper_reach_6317 : UpperReach 6317 62336313837651 := by
  have hr := row_6317
  have hl := log_bounds hr.1
    (by change logScale (6317 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6311) (H := 62248803840698) (u := 87509996877)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 59, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6311

theorem upper_reach_6323 : UpperReach 6323 62423833328276 := by
  have hr := row_6323
  have hl := log_bounds hr.1
    (by change logScale (6323 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6317) (H := 62336313837651) (u := 87519490549)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 71, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6317

theorem upper_reach_6329 : UpperReach 6329 62511362303568 := by
  have hr := row_6329
  have hl := log_bounds hr.1
    (by change logScale (6329 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6323) (H := 62423833328276) (u := 87528975216)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6323

theorem upper_reach_6337 : UpperReach 6337 62598903911106 := by
  have hr := row_6337
  have hl := log_bounds hr.1
    (by change logScale (6337 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6329) (H := 62511362303568) (u := 87541607462)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 13, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6329

theorem upper_reach_6343 : UpperReach 6343 62686454982367 := by
  have hr := row_6343
  have hl := log_bounds hr.1
    (by change logScale (6343 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6337) (H := 62598903911106) (u := 87551071185)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 17, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6337

theorem upper_reach_6353 : UpperReach 6353 62774021806624 := by
  have hr := row_6353
  have hl := log_bounds hr.1
    (by change logScale (6353 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6343) (H := 62686454982367) (u := 87566824181)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6343

theorem upper_reach_6359 : UpperReach 6359 62861598070781 := by
  have hr := row_6359
  have hl := log_bounds hr.1
    (by change logScale (6359 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6353) (H := 62774021806624) (u := 87576264081)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6353

#print axioms upper_reach_6359

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
