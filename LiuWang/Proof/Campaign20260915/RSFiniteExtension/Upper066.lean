import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper065
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block066

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_15313 : UpperReach 15313 151817452351995 := by
  have hr := row_15313
  have hl := log_bounds hr.1
    (by change logScale (15313 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15307) (H := 151721087777755) (u := 96364574164)
    (by norm_num) (by norm_num) hr.1 gap_15313 hl.2
    (by norm_num) upper_reach_15307

theorem upper_reach_15319 : UpperReach 15319 151913820843707 := by
  have hr := row_15319
  have hl := log_bounds hr.1
    (by change logScale (15319 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15313) (H := 151817452351995) (u := 96368491636)
    (by norm_num) (by norm_num) hr.1 gap_15319 hl.2
    (by norm_num) upper_reach_15313

theorem upper_reach_15329 : UpperReach 15329 152010195861130 := by
  have hr := row_15329
  have hl := log_bounds hr.1
    (by change logScale (15329 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15319) (H := 151913820843707) (u := 96375017347)
    (by norm_num) (by norm_num) hr.1 gap_15329 hl.2
    (by norm_num) upper_reach_15319

theorem upper_reach_15331 : UpperReach 15331 152106572183185 := by
  have hr := row_15331
  have hl := log_bounds hr.1
    (by change logScale (15331 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15329) (H := 152010195861130) (u := 96376321979)
    (by norm_num) (by norm_num) hr.1 gap_15331 hl.2
    (by norm_num) upper_reach_15329

theorem upper_reach_15349 : UpperReach 15349 152202960239270 := by
  have hr := row_15349
  have hl := log_bounds hr.1
    (by change logScale (15349 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15331) (H := 152106572183185) (u := 96388056009)
    (by norm_num) (by norm_num) hr.1 gap_15349 hl.2
    (by norm_num) upper_reach_15331

theorem upper_reach_15359 : UpperReach 15359 152299354808316 := by
  have hr := row_15359
  have hl := log_bounds hr.1
    (by change logScale (15359 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15349) (H := 152202960239270) (u := 96394568970)
    (by norm_num) (by norm_num) hr.1 gap_15359 hl.2
    (by norm_num) upper_reach_15349

theorem upper_reach_15361 : UpperReach 15361 152395750679445 := by
  have hr := row_15361
  have hl := log_bounds hr.1
    (by change logScale (15361 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15359) (H := 152299354808316) (u := 96395871053)
    (by norm_num) (by norm_num) hr.1 gap_15361 hl.2
    (by norm_num) upper_reach_15359

theorem upper_reach_15373 : UpperReach 15373 152492154359516 := by
  have hr := row_15373
  have hl := log_bounds hr.1
    (by change logScale (15373 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15361) (H := 152395750679445) (u := 96403679995)
    (by norm_num) (by norm_num) hr.1 gap_15373 hl.2
    (by norm_num) upper_reach_15361

theorem upper_reach_15377 : UpperReach 15377 152588560641213 := by
  have hr := row_15377
  have hl := log_bounds hr.1
    (by change logScale (15377 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15373) (H := 152492154359516) (u := 96406281621)
    (by norm_num) (by norm_num) hr.1 gap_15377 hl.2
    (by norm_num) upper_reach_15373

theorem upper_reach_15383 : UpperReach 15383 152684970824080 := by
  have hr := row_15383
  have hl := log_bounds hr.1
    (by change logScale (15383 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15377) (H := 152588560641213) (u := 96410182791)
    (by norm_num) (by norm_num) hr.1 gap_15383 hl.2
    (by norm_num) upper_reach_15377

theorem upper_reach_15391 : UpperReach 15391 152781386206141 := by
  have hr := row_15391
  have hl := log_bounds hr.1
    (by change logScale (15391 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15383) (H := 152684970824080) (u := 96415381985)
    (by norm_num) (by norm_num) hr.1 gap_15391 hl.2
    (by norm_num) upper_reach_15383

theorem upper_reach_15401 : UpperReach 15401 152877808083396 := by
  have hr := row_15401
  have hl := log_bounds hr.1
    (by change logScale (15401 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15391) (H := 152781386206141) (u := 96421877179)
    (by norm_num) (by norm_num) hr.1 gap_15401 hl.2
    (by norm_num) upper_reach_15391

theorem upper_reach_15413 : UpperReach 15413 152974237749319 := by
  have hr := row_15413
  have hl := log_bounds hr.1
    (by change logScale (15413 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15401) (H := 152877808083396) (u := 96429665847)
    (by norm_num) (by norm_num) hr.1 gap_15413 hl.2
    (by norm_num) upper_reach_15401

theorem upper_reach_15427 : UpperReach 15427 153070676494361 := by
  have hr := row_15427
  have hl := log_bounds hr.1
    (by change logScale (15427 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15413) (H := 152974237749319) (u := 96438744966)
    (by norm_num) (by norm_num) hr.1 gap_15427 hl.2
    (by norm_num) upper_reach_15413

theorem upper_reach_15439 : UpperReach 15439 153167123014949 := by
  have hr := row_15439
  have hl := log_bounds hr.1
    (by change logScale (15439 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15427) (H := 153070676494361) (u := 96446520512)
    (by norm_num) (by norm_num) hr.1 gap_15439 hl.2
    (by norm_num) upper_reach_15427

theorem upper_reach_15443 : UpperReach 15443 153263572126043 := by
  have hr := row_15443
  have hl := log_bounds hr.1
    (by change logScale (15443 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15439) (H := 153167123014949) (u := 96449111018)
    (by norm_num) (by norm_num) hr.1 gap_15443 hl.2
    (by norm_num) upper_reach_15439

theorem upper_reach_15451 : UpperReach 15451 153360026416136 := by
  have hr := row_15451
  have hl := log_bounds hr.1
    (by change logScale (15451 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15443) (H := 153263572126043) (u := 96454290017)
    (by norm_num) (by norm_num) hr.1 gap_15451 hl.2
    (by norm_num) upper_reach_15443

theorem upper_reach_15461 : UpperReach 15461 153456487176209 := by
  have hr := row_15461
  have hl := log_bounds hr.1
    (by change logScale (15461 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15451) (H := 153360026416136) (u := 96460759997)
    (by norm_num) (by norm_num) hr.1 gap_15461 hl.2
    (by norm_num) upper_reach_15451

theorem upper_reach_15467 : UpperReach 15467 153552951816261 := by
  have hr := row_15467
  have hl := log_bounds hr.1
    (by change logScale (15467 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15461) (H := 153456487176209) (u := 96464639976)
    (by norm_num) (by norm_num) hr.1 gap_15467 hl.2
    (by norm_num) upper_reach_15461

theorem upper_reach_15473 : UpperReach 15473 153649420334788 := by
  have hr := row_15473
  have hl := log_bounds hr.1
    (by change logScale (15473 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15467) (H := 153552951816261) (u := 96468518451)
    (by norm_num) (by norm_num) hr.1 gap_15473 hl.2
    (by norm_num) upper_reach_15467

theorem upper_reach_15493 : UpperReach 15493 153745901770710 := by
  have hr := row_15493
  have hl := log_bounds hr.1
    (by change logScale (15493 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15473) (H := 153649420334788) (u := 96481435846)
    (by norm_num) (by norm_num) hr.1 gap_15493 hl.2
    (by norm_num) upper_reach_15473

theorem upper_reach_15497 : UpperReach 15497 153842385788110 := by
  have hr := row_15497
  have hl := log_bounds hr.1
    (by change logScale (15497 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15493) (H := 153745901770710) (u := 96484017324)
    (by norm_num) (by norm_num) hr.1 gap_15497 hl.2
    (by norm_num) upper_reach_15493

theorem upper_reach_15511 : UpperReach 15511 153938878835438 := by
  have hr := row_15511
  have hl := log_bounds hr.1
    (by change logScale (15511 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15497) (H := 153842385788110) (u := 96493047252)
    (by norm_num) (by norm_num) hr.1 gap_15511 hl.2
    (by norm_num) upper_reach_15497

theorem upper_reach_15527 : UpperReach 15527 154035382192709 := by
  have hr := row_15527
  have hl := log_bounds hr.1
    (by change logScale (15527 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 15511) (H := 153938878835438) (u := 96503357195)
    (by norm_num) (by norm_num) hr.1 gap_15527 hl.2
    (by norm_num) upper_reach_15511

#print axioms upper_reach_15527

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
