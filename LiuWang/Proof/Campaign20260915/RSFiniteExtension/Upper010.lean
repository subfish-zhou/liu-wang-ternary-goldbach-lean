import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper009
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block010

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_3121 : UpperReach 3121 30527535777615 := by
  have hr := row_3121
  have hl := log_bounds hr.1
    (by change logScale (3121 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3119) (H := 30447076690145) (u := 80459087394)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3119

theorem upper_reach_3137 : UpperReach 3137 30608045999744 := by
  have hr := row_3137
  have hl := log_bounds hr.1
    (by change logScale (3137 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3121) (H := 30527535777615) (u := 80510222053)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 53, 2, 3, 2, 31, 2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3121

theorem upper_reach_3163 : UpperReach 3163 30688638762024 := by
  have hr := row_3163
  have hl := log_bounds hr.1
    (by change logScale (3163 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3137) (H := 30608045999744) (u := 80592762204)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 43, 2, 3, 2, 7, 2, 5, 2, 3, 2, 47, 2, 23, 2, 3, 2, 5, 2, 7, 2, 3, 2, 29, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3137

theorem upper_reach_3167 : UpperReach 3167 30769244162536 := by
  have hr := row_3167
  have hl := log_bounds hr.1
    (by change logScale (3167 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3163) (H := 30688638762024) (u := 80605400436)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3163

theorem upper_reach_3169 : UpperReach 3169 30849855876180 := by
  have hr := row_3169
  have hl := log_bounds hr.1
    (by change logScale (3169 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3167) (H := 30769244162536) (u := 80611713568)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3167

theorem upper_reach_3181 : UpperReach 3181 30930505385144 := by
  have hr := row_3181
  have hl := log_bounds hr.1
    (by change logScale (3181 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3169) (H := 30849855876180) (u := 80649508888)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 19, 2, 5, 2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3169

theorem upper_reach_3187 : UpperReach 3187 31011173738335 := by
  have hr := row_3187
  have hl := log_bounds hr.1
    (by change logScale (3187 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3181) (H := 30930505385144) (u := 80668353115)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3181

theorem upper_reach_3191 : UpperReach 3191 31091854634645 := by
  have hr := row_3191
  have hl := log_bounds hr.1
    (by change logScale (3191 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3187) (H := 31011173738335) (u := 80680896234)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3187

theorem upper_reach_3203 : UpperReach 3203 31172573066188 := by
  have hr := row_3203
  have hl := log_bounds hr.1
    (by change logScale (3203 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3191) (H := 31091854634645) (u := 80718431467)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 31, 2, 3, 2, 23, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3191

theorem upper_reach_3209 : UpperReach 3209 31253310212646 := by
  have hr := row_3209
  have hl := log_bounds hr.1
    (by change logScale (3209 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3203) (H := 31172573066188) (u := 80737146382)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3203

theorem upper_reach_3217 : UpperReach 3217 31334072257965 := by
  have hr := row_3217
  have hl := log_bounds hr.1
    (by change logScale (3217 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3209) (H := 31253310212646) (u := 80762045243)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 13, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3209

theorem upper_reach_3221 : UpperReach 3221 31414846729505 := by
  have hr := row_3221
  have hl := log_bounds hr.1
    (by change logScale (3221 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3217) (H := 31334072257965) (u := 80774471464)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3217

theorem upper_reach_3229 : UpperReach 3229 31495646007259 := by
  have hr := row_3229
  have hl := log_bounds hr.1
    (by change logScale (3229 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3221) (H := 31414846729505) (u := 80799277678)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3221

theorem upper_reach_3251 : UpperReach 3251 31576513186509 := by
  have hr := row_3251
  have hl := log_bounds hr.1
    (by change logScale (3251 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3229) (H := 31495646007259) (u := 80867179174)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 53, 2, 5, 2, 3, 2, 41, 2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3229

theorem upper_reach_3253 : UpperReach 3253 31657386515821 := by
  have hr := row_3253
  have hl := log_bounds hr.1
    (by change logScale (3253 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3251) (H := 31576513186509) (u := 80873329236)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3251

theorem upper_reach_3257 : UpperReach 3257 31738272133921 := by
  have hr := row_3257
  have hl := log_bounds hr.1
    (by change logScale (3257 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3253) (H := 31657386515821) (u := 80885618024)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3253

theorem upper_reach_3259 : UpperReach 3259 31819163890756 := by
  have hr := row_3259
  have hl := log_bounds hr.1
    (by change logScale (3259 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3257) (H := 31738272133921) (u := 80891756759)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3257

theorem upper_reach_3271 : UpperReach 3271 31900092401078 := by
  have hr := row_3271
  have hl := log_bounds hr.1
    (by change logScale (3271 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3259) (H := 31819163890756) (u := 80928510246)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3259

theorem upper_reach_3299 : UpperReach 3299 31981106147837 := by
  have hr := row_3299
  have hl := log_bounds hr.1
    (by change logScale (3299 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3271) (H := 31900092401078) (u := 81013746683)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 29, 2, 3, 2, 17, 2, 7, 2, 3, 2, 19, 2, 11, 2, 3, 2, 37, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3271

theorem upper_reach_3301 : UpperReach 3301 32062125955202 := by
  have hr := row_3301
  have hl := log_bounds hr.1
    (by change logScale (3301 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3299) (H := 31981106147837) (u := 81019807289)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3299

theorem upper_reach_3307 : UpperReach 3307 32143163922379 := by
  have hr := row_3307
  have hl := log_bounds hr.1
    (by change logScale (3307 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3301) (H := 32062125955202) (u := 81037967101)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3301

theorem upper_reach_3313 : UpperReach 3313 32224220016449 := by
  have hr := row_3313
  have hl := log_bounds hr.1
    (by change logScale (3313 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3307) (H := 32143163922379) (u := 81056093994)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3307

theorem upper_reach_3319 : UpperReach 3319 32305294204613 := by
  have hr := row_3319
  have hl := log_bounds hr.1
    (by change logScale (3319 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3313) (H := 32224220016449) (u := 81074188088)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 31, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3313

theorem upper_reach_3323 : UpperReach 3323 32386380437343 := by
  have hr := row_3323
  have hl := log_bounds hr.1
    (by change logScale (3323 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 3319) (H := 32305294204613) (u := 81086232654)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_3319

#print axioms upper_reach_3323

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
