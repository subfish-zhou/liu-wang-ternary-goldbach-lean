import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper004
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block005

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_2153 : UpperReach 2153 21079395937671 := by
  have hr := row_2153
  have hl := log_bounds hr.1
    (by change logScale (2153 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2143) (H := 21002649762650) (u := 76746174945)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 19, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2143

theorem upper_reach_2161 : UpperReach 2161 21156179201283 := by
  have hr := row_2161
  have hl := log_bounds hr.1
    (by change logScale (2161 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2153) (H := 21079395937671) (u := 76783263536)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 17, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2153

theorem upper_reach_2179 : UpperReach 2179 21233045414679 := by
  have hr := row_2179
  have hl := log_bounds hr.1
    (by change logScale (2179 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2161) (H := 21156179201283) (u := 76866213320)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 11, 2, 3, 2, 13, 2, 41, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2161

theorem upper_reach_2203 : UpperReach 2203 21310021168194 := by
  have hr := row_2203
  have hl := log_bounds hr.1
    (by change logScale (2203 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2179) (H := 21233045414679) (u := 76975753439)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 37, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 31, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2179

theorem upper_reach_2207 : UpperReach 2207 21387015062303 := by
  have hr := row_2207
  have hl := log_bounds hr.1
    (by change logScale (2207 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2203) (H := 21310021168194) (u := 76993894033)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2203

theorem upper_reach_2213 : UpperReach 2213 21464036105750 := by
  have hr := row_2213
  have hl := log_bounds hr.1
    (by change logScale (2213 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2207) (H := 21387015062303) (u := 77021043371)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 47, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2207

theorem upper_reach_2221 : UpperReach 2221 21541093234036 := by
  have hr := row_2221
  have hl := log_bounds hr.1
    (by change logScale (2221 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2213) (H := 21464036105750) (u := 77057128210)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2213

theorem upper_reach_2237 : UpperReach 2237 21618222143698 := by
  have hr := row_2237
  have hl := log_bounds hr.1
    (by change logScale (2237 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2221) (H := 21541093234036) (u := 77128909586)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 17, 2, 3, 2, 23, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2221

theorem upper_reach_2239 : UpperReach 2239 21695359989911 := by
  have hr := row_2239
  have hl := log_bounds hr.1
    (by change logScale (2239 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2237) (H := 21618222143698) (u := 77137846137)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2237

theorem upper_reach_2243 : UpperReach 2243 21772515685303 := by
  have hr := row_2243
  have hl := log_bounds hr.1
    (by change logScale (2243 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2239) (H := 21695359989911) (u := 77155695316)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2239

theorem upper_reach_2251 : UpperReach 2251 21849706983759 := by
  have hr := row_2251
  have hl := log_bounds hr.1
    (by change logScale (2251 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2243) (H := 21772515685303) (u := 77191298380)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2243

theorem upper_reach_2267 : UpperReach 2267 21926969110311 := by
  have hr := row_2267
  have hl := log_bounds hr.1
    (by change logScale (2267 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2251) (H := 21849706983759) (u := 77262126476)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 37, 2, 3, 2, 7, 2, 31, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2251

theorem upper_reach_2269 : UpperReach 2269 22004240055206 := by
  have hr := row_2269
  have hl := log_bounds hr.1
    (by change logScale (2269 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2267) (H := 21926969110311) (u := 77270944819)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2267

theorem upper_reach_2273 : UpperReach 2273 22081528613491 := by
  have hr := row_2273
  have hl := log_bounds hr.1
    (by change logScale (2273 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2269) (H := 22004240055206) (u := 77288558209)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2269

theorem upper_reach_2281 : UpperReach 2281 22158852305761 := by
  have hr := row_2281
  have hl := log_bounds hr.1
    (by change logScale (2281 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2273) (H := 22081528613491) (u := 77323692194)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 43, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2273

theorem upper_reach_2287 : UpperReach 2287 22236202267748 := by
  have hr := row_2287
  have hl := log_bounds hr.1
    (by change logScale (2287 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2281) (H := 22158852305761) (u := 77349961911)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2281

theorem upper_reach_2293 : UpperReach 2293 22313578430623 := by
  have hr := row_2293
  have hl := log_bounds hr.1
    (by change logScale (2293 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2287) (H := 22236202267748) (u := 77376162799)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 29, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2287

theorem upper_reach_2297 : UpperReach 2297 22390972022697 := by
  have hr := row_2297
  have hl := log_bounds hr.1
    (by change logScale (2297 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2293) (H := 22313578430623) (u := 77393591998)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2293

theorem upper_reach_2309 : UpperReach 2309 22468417720837 := by
  have hr := row_2309
  have hl := log_bounds hr.1
    (by change logScale (2309 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2297) (H := 22390972022697) (u := 77445698064)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2297

theorem upper_reach_2311 : UpperReach 2311 22545872076987 := by
  have hr := row_2311
  have hl := log_bounds hr.1
    (by change logScale (2311 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2309) (H := 22468417720837) (u := 77454356074)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2309

theorem upper_reach_2333 : UpperReach 2333 22623421179754 := by
  have hr := row_2333
  have hl := log_bounds hr.1
    (by change logScale (2333 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2311) (H := 22545872076987) (u := 77549102691)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 23, 2, 3, 2, 13, 2, 17, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2311

theorem upper_reach_2339 : UpperReach 2339 22700995967467 := by
  have hr := row_2339
  have hl := log_bounds hr.1
    (by change logScale (2339 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2333) (H := 22623421179754) (u := 77574787637)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2333

theorem upper_reach_2341 : UpperReach 2341 22778579302189 := by
  have hr := row_2341
  have hl := log_bounds hr.1
    (by change logScale (2341 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2339) (H := 22700995967467) (u := 77583334646)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2339

theorem upper_reach_2347 : UpperReach 2347 22856188234194 := by
  have hr := row_2347
  have hl := log_bounds hr.1
    (by change logScale (2347 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 2341) (H := 22778579302189) (u := 77608931929)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_2341

#print axioms upper_reach_2347

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
