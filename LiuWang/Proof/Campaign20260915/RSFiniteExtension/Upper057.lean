import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper056
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block057

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_13229 : UpperReach 13229 131152401738890 := by
  have hr := row_13229
  have hl := log_bounds hr.1
    (by change logScale (13229 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13219) (H := 131057500072164) (u := 94901666650)
    (by norm_num) (by norm_num) hr.1 gap_13229 hl.2
    (by norm_num) upper_reach_13219

theorem upper_reach_13241 : UpperReach 13241 131247312472485 := by
  have hr := row_13241
  have hl := log_bounds hr.1
    (by change logScale (13241 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13229) (H := 131152401738890) (u := 94910733519)
    (by norm_num) (by norm_num) hr.1 gap_13241 hl.2
    (by norm_num) upper_reach_13229

theorem upper_reach_13249 : UpperReach 13249 131342229246095 := by
  have hr := row_13249
  have hl := log_bounds hr.1
    (by change logScale (13249 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13241) (H := 131247312472485) (u := 94916773534)
    (by norm_num) (by norm_num) hr.1 gap_13249 hl.2
    (by norm_num) upper_reach_13241

theorem upper_reach_13259 : UpperReach 13259 131437153564598 := by
  have hr := row_13259
  have hl := log_bounds hr.1
    (by change logScale (13259 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13249) (H := 131342229246095) (u := 94924318427)
    (by norm_num) (by norm_num) hr.1 gap_13259 hl.2
    (by norm_num) upper_reach_13249

theorem upper_reach_13267 : UpperReach 13267 131532083914919 := by
  have hr := row_13267
  have hl := log_bounds hr.1
    (by change logScale (13267 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13259) (H := 131437153564598) (u := 94930350245)
    (by norm_num) (by norm_num) hr.1 gap_13267 hl.2
    (by norm_num) upper_reach_13259

theorem upper_reach_13291 : UpperReach 13291 131627032338895 := by
  have hr := row_13291
  have hl := log_bounds hr.1
    (by change logScale (13291 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13267) (H := 131532083914919) (u := 94948423900)
    (by norm_num) (by norm_num) hr.1 gap_13291 hl.2
    (by norm_num) upper_reach_13267

theorem upper_reach_13297 : UpperReach 13297 131721985276185 := by
  have hr := row_13297
  have hl := log_bounds hr.1
    (by change logScale (13297 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13291) (H := 131627032338895) (u := 94952937214)
    (by norm_num) (by norm_num) hr.1 gap_13297 hl.2
    (by norm_num) upper_reach_13291

theorem upper_reach_13309 : UpperReach 13309 131816947233998 := by
  have hr := row_13309
  have hl := log_bounds hr.1
    (by change logScale (13309 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13297) (H := 131721985276185) (u := 94961957737)
    (by norm_num) (by norm_num) hr.1 gap_13309 hl.2
    (by norm_num) upper_reach_13297

theorem upper_reach_13313 : UpperReach 13313 131911912196844 := by
  have hr := row_13313
  have hl := log_bounds hr.1
    (by change logScale (13313 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13309) (H := 131816947233998) (u := 94964962770)
    (by norm_num) (by norm_num) hr.1 gap_13313 hl.2
    (by norm_num) upper_reach_13309

theorem upper_reach_13327 : UpperReach 13327 132006887670202 := by
  have hr := row_13327
  have hl := log_bounds hr.1
    (by change logScale (13327 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13313) (H := 131911912196844) (u := 94975473282)
    (by norm_num) (by norm_num) hr.1 gap_13327 hl.2
    (by norm_num) upper_reach_13313

theorem upper_reach_13331 : UpperReach 13331 132101866144535 := by
  have hr := row_13331
  have hl := log_bounds hr.1
    (by change logScale (13331 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13327) (H := 132006887670202) (u := 94978474257)
    (by norm_num) (by norm_num) hr.1 gap_13331 hl.2
    (by norm_num) upper_reach_13327

theorem upper_reach_13337 : UpperReach 13337 132196849118643 := by
  have hr := row_13337
  have hl := log_bounds hr.1
    (by change logScale (13337 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13331) (H := 132101866144535) (u := 94982974032)
    (by norm_num) (by norm_num) hr.1 gap_13337 hl.2
    (by norm_num) upper_reach_13331

theorem upper_reach_13339 : UpperReach 13339 132291833592226 := by
  have hr := row_13339
  have hl := log_bounds hr.1
    (by change logScale (13339 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13337) (H := 132196849118643) (u := 94984473507)
    (by norm_num) (by norm_num) hr.1 gap_13339 hl.2
    (by norm_num) upper_reach_13337

theorem upper_reach_13367 : UpperReach 13367 132386839034887 := by
  have hr := row_13367
  have hl := log_bounds hr.1
    (by change logScale (13367 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13339) (H := 132291833592226) (u := 95005442585)
    (by norm_num) (by norm_num) hr.1 gap_13367 hl.2
    (by norm_num) upper_reach_13339

theorem upper_reach_13381 : UpperReach 13381 132481854945622 := by
  have hr := row_13381
  have hl := log_bounds hr.1
    (by change logScale (13381 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13367) (H := 132386839034887) (u := 95015910659)
    (by norm_num) (by norm_num) hr.1 gap_13381 hl.2
    (by norm_num) upper_reach_13367

theorem upper_reach_13397 : UpperReach 13397 132576882806466 := by
  have hr := row_13397
  have hl := log_bounds hr.1
    (by change logScale (13397 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13381) (H := 132481854945622) (u := 95027860768)
    (by norm_num) (by norm_num) hr.1 gap_13397 hl.2
    (by norm_num) upper_reach_13381

theorem upper_reach_13399 : UpperReach 13399 132671912160071 := by
  have hr := row_13399
  have hl := log_bounds hr.1
    (by change logScale (13399 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13397) (H := 132576882806466) (u := 95029353529)
    (by norm_num) (by norm_num) hr.1 gap_13399 hl.2
    (by norm_num) upper_reach_13397

theorem upper_reach_13411 : UpperReach 13411 132766950465560 := by
  have hr := row_13411
  have hl := log_bounds hr.1
    (by change logScale (13411 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13399) (H := 132671912160071) (u := 95038305413)
    (by norm_num) (by norm_num) hr.1 gap_13411 hl.2
    (by norm_num) upper_reach_13399

theorem upper_reach_13417 : UpperReach 13417 132861993243988 := by
  have hr := row_13417
  have hl := log_bounds hr.1
    (by change logScale (13417 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13411) (H := 132766950465560) (u := 95042778352)
    (by norm_num) (by norm_num) hr.1 gap_13417 hl.2
    (by norm_num) upper_reach_13411

theorem upper_reach_13421 : UpperReach 13421 132957039003264 := by
  have hr := row_13421
  have hl := log_bounds hr.1
    (by change logScale (13421 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13417) (H := 132861993243988) (u := 95045759200)
    (by norm_num) (by norm_num) hr.1 gap_13421 hl.2
    (by norm_num) upper_reach_13417

theorem upper_reach_13441 : UpperReach 13441 133052099653466 := by
  have hr := row_13441
  have hl := log_bounds hr.1
    (by change logScale (13441 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13421) (H := 132957039003264) (u := 95060650126)
    (by norm_num) (by norm_num) hr.1 gap_13441 hl.2
    (by norm_num) upper_reach_13421

theorem upper_reach_13451 : UpperReach 13451 133147167740825 := by
  have hr := row_13451
  have hl := log_bounds hr.1
    (by change logScale (13451 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13441) (H := 133052099653466) (u := 95068087283)
    (by norm_num) (by norm_num) hr.1 gap_13451 hl.2
    (by norm_num) upper_reach_13441

theorem upper_reach_13457 : UpperReach 13457 133242240287824 := by
  have hr := row_13457
  have hl := log_bounds hr.1
    (by change logScale (13457 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13451) (H := 133147167740825) (u := 95072546923)
    (by norm_num) (by norm_num) hr.1 gap_13457 hl.2
    (by norm_num) upper_reach_13451

theorem upper_reach_13463 : UpperReach 13463 133337317292475 := by
  have hr := row_13463
  have hl := log_bounds hr.1
    (by change logScale (13463 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 13457) (H := 133242240287824) (u := 95077004575)
    (by norm_num) (by norm_num) hr.1 gap_13463 hl.2
    (by norm_num) upper_reach_13457

#print axioms upper_reach_13463

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
