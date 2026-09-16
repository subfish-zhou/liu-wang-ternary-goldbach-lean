import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper043
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block044

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_10273 : UpperReach 10273 101911896569569 := by
  have hr := row_10273
  have hl := log_bounds hr.1
    (by change logScale (10273 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10271) (H := 101819523825795) (u := 92372743698)
    (by norm_num) (by norm_num) hr.1 gap_10273 hl.2
    (by norm_num) upper_reach_10271

theorem upper_reach_10289 : UpperReach 10289 102004284876034 := by
  have hr := row_10289
  have hl := log_bounds hr.1
    (by change logScale (10289 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10273) (H := 101911896569569) (u := 92388306389)
    (by norm_num) (by norm_num) hr.1 gap_10289 hl.2
    (by norm_num) upper_reach_10273

theorem upper_reach_10301 : UpperReach 10301 102096684838645 := by
  have hr := row_10301
  have hl := log_bounds hr.1
    (by change logScale (10301 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10289) (H := 102004284876034) (u := 92399962535)
    (by norm_num) (by norm_num) hr.1 gap_10301 hl.2
    (by norm_num) upper_reach_10289

theorem upper_reach_10303 : UpperReach 10303 102189086742626 := by
  have hr := row_10303
  have hl := log_bounds hr.1
    (by change logScale (10303 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10301) (H := 102096684838645) (u := 92401903905)
    (by norm_num) (by norm_num) hr.1 gap_10303 hl.2
    (by norm_num) upper_reach_10301

theorem upper_reach_10313 : UpperReach 10313 102281498347811 := by
  have hr := row_10313
  have hl := log_bounds hr.1
    (by change logScale (10313 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10303) (H := 102189086742626) (u := 92411605109)
    (by norm_num) (by norm_num) hr.1 gap_10313 hl.2
    (by norm_num) upper_reach_10303

theorem upper_reach_10321 : UpperReach 10321 102373917707188 := by
  have hr := row_10321
  have hl := log_bounds hr.1
    (by change logScale (10321 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10313) (H := 102281498347811) (u := 92419359301)
    (by norm_num) (by norm_num) hr.1 gap_10321 hl.2
    (by norm_num) upper_reach_10313

theorem upper_reach_10331 : UpperReach 10331 102466346750858 := by
  have hr := row_10331
  have hl := log_bounds hr.1
    (by change logScale (10331 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10321) (H := 102373917707188) (u := 92429043594)
    (by norm_num) (by norm_num) hr.1 gap_10331 hl.2
    (by norm_num) upper_reach_10321

theorem upper_reach_10333 : UpperReach 10333 102558777730262 := by
  have hr := row_10333
  have hl := log_bounds hr.1
    (by change logScale (10333 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10331) (H := 102466346750858) (u := 92430979328)
    (by norm_num) (by norm_num) hr.1 gap_10333 hl.2
    (by norm_num) upper_reach_10331

theorem upper_reach_10337 : UpperReach 10337 102651212580009 := by
  have hr := row_10337
  have hl := log_bounds hr.1
    (by change logScale (10337 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10333) (H := 102558777730262) (u := 92434849671)
    (by norm_num) (by norm_num) hr.1 gap_10337 hl.2
    (by norm_num) upper_reach_10333

theorem upper_reach_10343 : UpperReach 10343 102743653232464 := by
  have hr := row_10343
  have hl := log_bounds hr.1
    (by change logScale (10343 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10337) (H := 102651212580009) (u := 92440652379)
    (by norm_num) (by norm_num) hr.1 gap_10343 hl.2
    (by norm_num) upper_reach_10337

theorem upper_reach_10357 : UpperReach 10357 102836107411492 := by
  have hr := row_10357
  have hl := log_bounds hr.1
    (by change logScale (10357 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10343) (H := 102743653232464) (u := 92454178952)
    (by norm_num) (by norm_num) hr.1 gap_10357 hl.2
    (by norm_num) upper_reach_10343

theorem upper_reach_10369 : UpperReach 10369 102928573170179 := by
  have hr := row_10369
  have hl := log_bounds hr.1
    (by change logScale (10369 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10357) (H := 102836107411492) (u := 92465758611)
    (by norm_num) (by norm_num) hr.1 gap_10369 hl.2
    (by norm_num) upper_reach_10357

theorem upper_reach_10391 : UpperReach 10391 103021060123479 := by
  have hr := row_10391
  have hl := log_bounds hr.1
    (by change logScale (10391 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10369) (H := 102928573170179) (u := 92486953224)
    (by norm_num) (by norm_num) hr.1 gap_10391 hl.2
    (by norm_num) upper_reach_10369

theorem upper_reach_10399 : UpperReach 10399 103113554772787 := by
  have hr := row_10399
  have hl := log_bounds hr.1
    (by change logScale (10399 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10391) (H := 103021060123479) (u := 92494649232)
    (by norm_num) (by norm_num) hr.1 gap_10399 hl.2
    (by norm_num) upper_reach_10391

theorem upper_reach_10427 : UpperReach 10427 103206076311577 := by
  have hr := row_10427
  have hl := log_bounds hr.1
    (by change logScale (10427 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10399) (H := 103113554772787) (u := 92521538714)
    (by norm_num) (by norm_num) hr.1 gap_10427 hl.2
    (by norm_num) upper_reach_10399

theorem upper_reach_10429 : UpperReach 10429 103298599768280 := by
  have hr := row_10429
  have hl := log_bounds hr.1
    (by change logScale (10429 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10427) (H := 103206076311577) (u := 92523456627)
    (by norm_num) (by norm_num) hr.1 gap_10429 hl.2
    (by norm_num) upper_reach_10427

theorem upper_reach_10433 : UpperReach 10433 103391127059706 := by
  have hr := row_10433
  have hl := log_bounds hr.1
    (by change logScale (10433 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10429) (H := 103298599768280) (u := 92527291350)
    (by norm_num) (by norm_num) hr.1 gap_10433 hl.2
    (by norm_num) upper_reach_10429

theorem upper_reach_10453 : UpperReach 10453 103483673502723 := by
  have hr := row_10453
  have hl := log_bounds hr.1
    (by change logScale (10453 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10433) (H := 103391127059706) (u := 92546442941)
    (by norm_num) (by norm_num) hr.1 gap_10453 hl.2
    (by norm_num) upper_reach_10433

theorem upper_reach_10457 : UpperReach 10457 103576223771661 := by
  have hr := row_10457
  have hl := log_bounds hr.1
    (by change logScale (10457 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10453) (H := 103483673502723) (u := 92550268862)
    (by norm_num) (by norm_num) hr.1 gap_10457 hl.2
    (by norm_num) upper_reach_10453

theorem upper_reach_10459 : UpperReach 10459 103668775953010 := by
  have hr := row_10459
  have hl := log_bounds hr.1
    (by change logScale (10459 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10457) (H := 103576223771661) (u := 92552181273)
    (by norm_num) (by norm_num) hr.1 gap_10459 hl.2
    (by norm_num) upper_reach_10457

theorem upper_reach_10463 : UpperReach 10463 103761331958086 := by
  have hr := row_10463
  have hl := log_bounds hr.1
    (by change logScale (10463 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10459) (H := 103668775953010) (u := 92556005000)
    (by norm_num) (by norm_num) hr.1 gap_10463 hl.2
    (by norm_num) upper_reach_10459

theorem upper_reach_10477 : UpperReach 10477 103853901334701 := by
  have hr := row_10477
  have hl := log_bounds hr.1
    (by change logScale (10477 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10463) (H := 103761331958086) (u := 92569376539)
    (by norm_num) (by norm_num) hr.1 gap_10477 hl.2
    (by norm_num) upper_reach_10463

theorem upper_reach_10487 : UpperReach 10487 103946480251481 := by
  have hr := row_10487
  have hl := log_bounds hr.1
    (by change logScale (10487 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10477) (H := 103853901334701) (u := 92578916704)
    (by norm_num) (by norm_num) hr.1 gap_10487 hl.2
    (by norm_num) upper_reach_10477

theorem upper_reach_10499 : UpperReach 10499 104039070604458 := by
  have hr := row_10499
  have hl := log_bounds hr.1
    (by change logScale (10499 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 10487) (H := 103946480251481) (u := 92590352901)
    (by norm_num) (by norm_num) hr.1 gap_10499 hl.2
    (by norm_num) upper_reach_10487

#print axioms upper_reach_10499

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
