import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper039
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block040

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_9419 : UpperReach 9419 93085138527256 := by
  have hr := row_9419
  have hl := log_bounds hr.1
    (by change logScale (9419 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9413) (H := 92993633685166) (u := 91504842014)
    (by norm_num) (by norm_num) hr.1 gap_9419 hl.2
    (by norm_num) upper_reach_9413

theorem upper_reach_9421 : UpperReach 9421 93176645492488 := by
  have hr := row_9421
  have hl := log_bounds hr.1
    (by change logScale (9421 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9419) (H := 93085138527256) (u := 91506965156)
    (by norm_num) (by norm_num) hr.1 gap_9421 hl.2
    (by norm_num) upper_reach_9419

theorem upper_reach_9431 : UpperReach 9431 93268163066675 := by
  have hr := row_9431
  have hl := log_bounds hr.1
    (by change logScale (9431 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9421) (H := 93176645492488) (u := 91517574111)
    (by norm_num) (by norm_num) hr.1 gap_9431 hl.2
    (by norm_num) upper_reach_9421

theorem upper_reach_9433 : UpperReach 9433 93359682761303 := by
  have hr := row_9433
  have hl := log_bounds hr.1
    (by change logScale (9433 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9431) (H := 93268163066675) (u := 91519694552)
    (by norm_num) (by norm_num) hr.1 gap_9433 hl.2
    (by norm_num) upper_reach_9431

theorem upper_reach_9437 : UpperReach 9437 93451206695465 := by
  have hr := row_9437
  have hl := log_bounds hr.1
    (by change logScale (9437 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9433) (H := 93359682761303) (u := 91523934086)
    (by norm_num) (by norm_num) hr.1 gap_9437 hl.2
    (by norm_num) upper_reach_9433

theorem upper_reach_9439 : UpperReach 9439 93542732748720 := by
  have hr := row_9439
  have hl := log_bounds hr.1
    (by change logScale (9439 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9437) (H := 93451206695465) (u := 91526053179)
    (by norm_num) (by norm_num) hr.1 gap_9439 hl.2
    (by norm_num) upper_reach_9437

theorem upper_reach_9461 : UpperReach 9461 93634282082409 := by
  have hr := row_9461
  have hl := log_bounds hr.1
    (by change logScale (9461 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9439) (H := 93542732748720) (u := 91549333613)
    (by norm_num) (by norm_num) hr.1 gap_9461 hl.2
    (by norm_num) upper_reach_9439

theorem upper_reach_9463 : UpperReach 9463 93725833529816 := by
  have hr := row_9463
  have hl := log_bounds hr.1
    (by change logScale (9463 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9461) (H := 93634282082409) (u := 91551447331)
    (by norm_num) (by norm_num) hr.1 gap_9463 hl.2
    (by norm_num) upper_reach_9461

theorem upper_reach_9467 : UpperReach 9467 93817389203319 := by
  have hr := row_9467
  have hl := log_bounds hr.1
    (by change logScale (9467 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9463) (H := 93725833529816) (u := 91555673427)
    (by norm_num) (by norm_num) hr.1 gap_9467 hl.2
    (by norm_num) upper_reach_9463

theorem upper_reach_9473 : UpperReach 9473 93908951212619 := by
  have hr := row_9473
  have hl := log_bounds hr.1
    (by change logScale (9473 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9467) (H := 93817389203319) (u := 91562009224)
    (by norm_num) (by norm_num) hr.1 gap_9473 hl.2
    (by norm_num) upper_reach_9467

theorem upper_reach_9479 : UpperReach 9479 94000519553705 := by
  have hr := row_9479
  have hl := log_bounds hr.1
    (by change logScale (9479 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9473) (H := 93908951212619) (u := 91568341010)
    (by norm_num) (by norm_num) hr.1 gap_9479 hl.2
    (by norm_num) upper_reach_9473

theorem upper_reach_9491 : UpperReach 9491 94092100546348 := by
  have hr := row_9491
  have hl := log_bounds hr.1
    (by change logScale (9491 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9479) (H := 94000519553705) (u := 91580992567)
    (by norm_num) (by norm_num) hr.1 gap_9491 hl.2
    (by norm_num) upper_reach_9479

theorem upper_reach_9497 : UpperReach 9497 94183687858772 := by
  have hr := row_9497
  have hl := log_bounds hr.1
    (by change logScale (9497 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9491) (H := 94092100546348) (u := 91587312348)
    (by norm_num) (by norm_num) hr.1 gap_9497 hl.2
    (by norm_num) upper_reach_9491

theorem upper_reach_9511 : UpperReach 9511 94275289901839 := by
  have hr := row_9511
  have hl := log_bounds hr.1
    (by change logScale (9511 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9497) (H := 94183687858772) (u := 91602042991)
    (by norm_num) (by norm_num) hr.1 gap_9511 hl.2
    (by norm_num) upper_reach_9497

theorem upper_reach_9521 : UpperReach 9521 94366902453524 := by
  have hr := row_9521
  have hl := log_bounds hr.1
    (by change logScale (9521 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9511) (H := 94275289901839) (u := 91612551609)
    (by norm_num) (by norm_num) hr.1 gap_9521 hl.2
    (by norm_num) upper_reach_9511

theorem upper_reach_9533 : UpperReach 9533 94458527600991 := by
  have hr := row_9533
  have hl := log_bounds hr.1
    (by change logScale (9533 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9521) (H := 94366902453524) (u := 91625147391)
    (by norm_num) (by norm_num) hr.1 gap_9533 hl.2
    (by norm_num) upper_reach_9521

theorem upper_reach_9539 : UpperReach 9539 94550159040404 := by
  have hr := row_9539
  have hl := log_bounds hr.1
    (by change logScale (9539 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9533) (H := 94458527600991) (u := 91631439337)
    (by norm_num) (by norm_num) hr.1 gap_9539 hl.2
    (by norm_num) upper_reach_9533

theorem upper_reach_9547 : UpperReach 9547 94641798862926 := by
  have hr := row_9547
  have hl := log_bounds hr.1
    (by change logScale (9547 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9539) (H := 94550159040404) (u := 91639822446)
    (by norm_num) (by norm_num) hr.1 gap_9547 hl.2
    (by norm_num) upper_reach_9539

theorem upper_reach_9551 : UpperReach 9551 94733442874368 := by
  have hr := row_9551
  have hl := log_bounds hr.1
    (by change logScale (9551 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9547) (H := 94641798862926) (u := 91644011366)
    (by norm_num) (by norm_num) hr.1 gap_9551 hl.2
    (by norm_num) upper_reach_9547

theorem upper_reach_9587 : UpperReach 9587 94825124507340 := by
  have hr := row_9587
  have hl := log_bounds hr.1
    (by change logScale (9587 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9551) (H := 94733442874368) (u := 91681632896)
    (by norm_num) (by norm_num) hr.1 gap_9587 hl.2
    (by norm_num) upper_reach_9551

theorem upper_reach_9601 : UpperReach 9601 94916820732769 := by
  have hr := row_9601
  have hl := log_bounds hr.1
    (by change logScale (9601 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9587) (H := 94825124507340) (u := 91696225353)
    (by norm_num) (by norm_num) hr.1 gap_9601 hl.2
    (by norm_num) upper_reach_9587

theorem upper_reach_9613 : UpperReach 9613 95008529449091 := by
  have hr := row_9613
  have hl := log_bounds hr.1
    (by change logScale (9613 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9601) (H := 94916820732769) (u := 91708716246)
    (by norm_num) (by norm_num) hr.1 gap_9613 hl.2
    (by norm_num) upper_reach_9601

theorem upper_reach_9619 : UpperReach 9619 95100244405014 := by
  have hr := row_9619
  have hl := log_bounds hr.1
    (by change logScale (9619 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9613) (H := 95008529449091) (u := 91714955847)
    (by norm_num) (by norm_num) hr.1 gap_9619 hl.2
    (by norm_num) upper_reach_9613

theorem upper_reach_9623 : UpperReach 9623 95191963518509 := by
  have hr := row_9623
  have hl := log_bounds hr.1
    (by change logScale (9623 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 9619) (H := 95100244405014) (u := 91719113419)
    (by norm_num) (by norm_num) hr.1 gap_9623 hl.2
    (by norm_num) upper_reach_9619

#print axioms upper_reach_9623

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
