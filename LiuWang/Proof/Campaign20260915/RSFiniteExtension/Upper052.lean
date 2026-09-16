import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper051
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block052

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_12143 : UpperReach 12143 119814687397656 := by
  have hr := row_12143
  have hl := log_bounds hr.1
    (by change logScale (12143 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12119) (H := 119720642316104) (u := 94045081476)
    (by norm_num) (by norm_num) hr.1 gap_12143 hl.2
    (by norm_num) upper_reach_12119

theorem upper_reach_12149 : UpperReach 12149 119908737419106 := by
  have hr := row_12149
  have hl := log_bounds hr.1
    (by change logScale (12149 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12143) (H := 119814687397656) (u := 94050021374)
    (by norm_num) (by norm_num) hr.1 gap_12149 hl.2
    (by norm_num) upper_reach_12143

theorem upper_reach_12157 : UpperReach 12157 120002794023293 := by
  have hr := row_12157
  have hl := log_bounds hr.1
    (by change logScale (12157 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12149) (H := 119908737419106) (u := 94056604111)
    (by norm_num) (by norm_num) hr.1 gap_12157 hl.2
    (by norm_num) upper_reach_12149

theorem upper_reach_12161 : UpperReach 12161 120096853917225 := by
  have hr := row_12161
  have hl := log_bounds hr.1
    (by change logScale (12161 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12157) (H := 120002794023293) (u := 94059893856)
    (by norm_num) (by norm_num) hr.1 gap_12161 hl.2
    (by norm_num) upper_reach_12157

theorem upper_reach_12163 : UpperReach 12163 120190915455623 := by
  have hr := row_12163
  have hl := log_bounds hr.1
    (by change logScale (12163 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12161) (H := 120096853917225) (u := 94061538322)
    (by norm_num) (by norm_num) hr.1 gap_12163 hl.2
    (by norm_num) upper_reach_12161

theorem upper_reach_12197 : UpperReach 12197 120285004908653 := by
  have hr := row_12197
  have hl := log_bounds hr.1
    (by change logScale (12197 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12163) (H := 120190915455623) (u := 94089452954)
    (by norm_num) (by norm_num) hr.1 gap_12197 hl.2
    (by norm_num) upper_reach_12163

theorem upper_reach_12203 : UpperReach 12203 120379099279716 := by
  have hr := row_12203
  have hl := log_bounds hr.1
    (by change logScale (12203 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12197) (H := 120285004908653) (u := 94094370987)
    (by norm_num) (by norm_num) hr.1 gap_12203 hl.2
    (by norm_num) upper_reach_12197

theorem upper_reach_12211 : UpperReach 12211 120473200204396 := by
  have hr := row_12211
  have hl := log_bounds hr.1
    (by change logScale (12211 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12203) (H := 120379099279716) (u := 94100924604)
    (by norm_num) (by norm_num) hr.1 gap_12211 hl.2
    (by norm_num) upper_reach_12203

theorem upper_reach_12227 : UpperReach 12227 120567314223439 := by
  have hr := row_12227
  have hl := log_bounds hr.1
    (by change logScale (12227 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12211) (H := 120473200204396) (u := 94114018967)
    (by norm_num) (by norm_num) hr.1 gap_12227 hl.2
    (by norm_num) upper_reach_12211

theorem upper_reach_12239 : UpperReach 12239 120661438052015 := by
  have hr := row_12239
  have hl := log_bounds hr.1
    (by change logScale (12239 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12227) (H := 120567314223439) (u := 94123828500)
    (by norm_num) (by norm_num) hr.1 gap_12239 hl.2
    (by norm_num) upper_reach_12227

theorem upper_reach_12241 : UpperReach 12241 120755563514577 := by
  have hr := row_12241
  have hl := log_bounds hr.1
    (by change logScale (12241 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12239) (H := 120661438052015) (u := 94125462486)
    (by norm_num) (by norm_num) hr.1 gap_12241 hl.2
    (by norm_num) upper_reach_12239

theorem upper_reach_12251 : UpperReach 12251 120849697143072 := by
  have hr := row_12251
  have hl := log_bounds hr.1
    (by change logScale (12251 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12241) (H := 120755563514577) (u := 94133628419)
    (by norm_num) (by norm_num) hr.1 gap_12251 hl.2
    (by norm_num) upper_reach_12241

theorem upper_reach_12253 : UpperReach 12253 120943832403953 := by
  have hr := row_12253
  have hl := log_bounds hr.1
    (by change logScale (12253 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12251) (H := 120849697143072) (u := 94135260805)
    (by norm_num) (by norm_num) hr.1 gap_12253 hl.2
    (by norm_num) upper_reach_12251

theorem upper_reach_12263 : UpperReach 12263 121037975822772 := by
  have hr := row_12263
  have hl := log_bounds hr.1
    (by change logScale (12263 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12253) (H := 120943832403953) (u := 94143418743)
    (by norm_num) (by norm_num) hr.1 gap_12263 hl.2
    (by norm_num) upper_reach_12253

theorem upper_reach_12269 : UpperReach 12269 121132124133162 := by
  have hr := row_12269
  have hl := log_bounds hr.1
    (by change logScale (12269 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12263) (H := 121037975822772) (u := 94148310314)
    (by norm_num) (by norm_num) hr.1 gap_12269 hl.2
    (by norm_num) upper_reach_12263

theorem upper_reach_12277 : UpperReach 12277 121226278961926 := by
  have hr := row_12277
  have hl := log_bounds hr.1
    (by change logScale (12277 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12269) (H := 121132124133162) (u := 94154828688)
    (by norm_num) (by norm_num) hr.1 gap_12277 hl.2
    (by norm_num) upper_reach_12269

theorem upper_reach_12281 : UpperReach 12281 121320437048284 := by
  have hr := row_12281
  have hl := log_bounds hr.1
    (by change logScale (12281 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12277) (H := 121226278961926) (u := 94158086282)
    (by norm_num) (by norm_num) hr.1 gap_12281 hl.2
    (by norm_num) upper_reach_12277

theorem upper_reach_12289 : UpperReach 12289 121414601646649 := by
  have hr := row_12289
  have hl := log_bounds hr.1
    (by change logScale (12289 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12281) (H := 121320437048284) (u := 94164598289)
    (by norm_num) (by norm_num) hr.1 gap_12289 hl.2
    (by norm_num) upper_reach_12281

theorem upper_reach_12301 : UpperReach 12301 121508776005079 := by
  have hr := row_12301
  have hl := log_bounds hr.1
    (by change logScale (12301 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12289) (H := 121414601646649) (u := 94174358354)
    (by norm_num) (by norm_num) hr.1 gap_12301 hl.2
    (by norm_num) upper_reach_12289

theorem upper_reach_12323 : UpperReach 12323 121602968232260 := by
  have hr := row_12323
  have hl := log_bounds hr.1
    (by change logScale (12323 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12301) (H := 121508776005079) (u := 94192227105)
    (by norm_num) (by norm_num) hr.1 gap_12323 hl.2
    (by norm_num) upper_reach_12301

theorem upper_reach_12329 : UpperReach 12329 121697165327200 := by
  have hr := row_12329
  have hl := log_bounds hr.1
    (by change logScale (12329 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12323) (H := 121602968232260) (u := 94197094864)
    (by norm_num) (by norm_num) hr.1 gap_12329 hl.2
    (by norm_num) upper_reach_12323

theorem upper_reach_12343 : UpperReach 12343 121791373771039 := by
  have hr := row_12343
  have hl := log_bounds hr.1
    (by change logScale (12343 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12329) (H := 121697165327200) (u := 94208443763)
    (by norm_num) (by norm_num) hr.1 gap_12343 hl.2
    (by norm_num) upper_reach_12329

theorem upper_reach_12347 : UpperReach 12347 121885585455056 := by
  have hr := row_12347
  have hl := log_bounds hr.1
    (by change logScale (12347 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12343) (H := 121791373771039) (u := 94211683941)
    (by norm_num) (by norm_num) hr.1 gap_12347 hl.2
    (by norm_num) upper_reach_12343

theorem upper_reach_12373 : UpperReach 12373 121979818174680 := by
  have hr := row_12373
  have hl := log_bounds hr.1
    (by change logScale (12373 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12347) (H := 121885585455056) (u := 94232719548)
    (by norm_num) (by norm_num) hr.1 gap_12373 hl.2
    (by norm_num) upper_reach_12347

#print axioms upper_reach_12373

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
