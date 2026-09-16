import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper025
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block026

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_6361 : UpperReach 6361 62949177479592 := by
  have hr := row_6361
  have hl := log_bounds hr.1
    (by change logScale (6361 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6359) (H := 62861598070781) (u := 87579408735)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6359

theorem upper_reach_6367 : UpperReach 6367 63036766316436 := by
  have hr := row_6367
  have hl := log_bounds hr.1
    (by change logScale (6367 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6361) (H := 62949177479592) (u := 87588836768)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6361

theorem upper_reach_6373 : UpperReach 6373 63124364572433 := by
  have hr := row_6373
  have hl := log_bounds hr.1
    (by change logScale (6373 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6367) (H := 63036766316436) (u := 87598255921)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 23, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6367

theorem upper_reach_6379 : UpperReach 6379 63211972238720 := by
  have hr := row_6379
  have hl := log_bounds hr.1
    (by change logScale (6379 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6373) (H := 63124364572433) (u := 87607666211)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6373

theorem upper_reach_6389 : UpperReach 6389 63299595569170 := by
  have hr := row_6389
  have hl := log_bounds hr.1
    (by change logScale (6389 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6379) (H := 63211972238720) (u := 87623330374)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 13, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6379

theorem upper_reach_6397 : UpperReach 6397 63387231413309 := by
  have hr := row_6397
  have hl := log_bounds hr.1
    (by change logScale (6397 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6389) (H := 63299595569170) (u := 87635844063)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6389

theorem upper_reach_6421 : UpperReach 6421 63474904704831 := by
  have hr := row_6421
  have hl := log_bounds hr.1
    (by change logScale (6421 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6397) (H := 63387231413309) (u := 87673291446)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 37, 2, 19, 2, 3, 2, 43, 2, 13, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6397

theorem upper_reach_6427 : UpperReach 6427 63562587336329 := by
  have hr := row_6427
  have hl := log_bounds hr.1
    (by change logScale (6427 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6421) (H := 63474904704831) (u := 87682631422)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6421

theorem upper_reach_6449 : UpperReach 6449 63650304139963 := by
  have hr := row_6449
  have hl := log_bounds hr.1
    (by change logScale (6449 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6427) (H := 63562587336329) (u := 87716803558)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 59, 2, 7, 2, 3, 2, 41, 2, 47, 2, 3, 2, 17, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6427

theorem upper_reach_6451 : UpperReach 6451 63738024044373 := by
  have hr := row_6451
  have hl := log_bounds hr.1
    (by change logScale (6451 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6449) (H := 63650304139963) (u := 87719904334)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6449

theorem upper_reach_6469 : UpperReach 6469 63825771812578 := by
  have hr := row_6469
  have hl := log_bounds hr.1
    (by change logScale (6469 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6451) (H := 63738024044373) (u := 87747768129)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 23, 2, 3, 2, 29, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6451

theorem upper_reach_6473 : UpperReach 6473 63913525762208 := by
  have hr := row_6473
  have hl := log_bounds hr.1
    (by change logScale (6473 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6469) (H := 63825771812578) (u := 87753949554)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6469

theorem upper_reach_6481 : UpperReach 6481 64001292063237 := by
  have hr := row_6481
  have hl := log_bounds hr.1
    (by change logScale (6481 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6473) (H := 63913525762208) (u := 87766300953)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6473

theorem upper_reach_6491 : UpperReach 6491 64089073782092 := by
  have hr := row_6491
  have hl := log_bounds hr.1
    (by change logScale (6491 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6481) (H := 64001292063237) (u := 87781718779)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6481

theorem upper_reach_6521 : UpperReach 6521 64176901612310 := by
  have hr := row_6521
  have hl := log_bounds hr.1
    (by change logScale (6521 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6491) (H := 64089073782092) (u := 87827830142)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 43, 2, 3, 2, 73, 2, 67, 2, 3, 2, 7, 2, 5, 2, 3, 2, 23, 2, 17, 2, 3, 2, 5, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6491

theorem upper_reach_6529 : UpperReach 6529 64264741703066 := by
  have hr := row_6529
  have hl := log_bounds hr.1
    (by change logScale (6529 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6521) (H := 64176901612310) (u := 87840090680)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 61, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6521

theorem upper_reach_6547 : UpperReach 6547 64352609325195 := by
  have hr := row_6547
  have hl := log_bounds hr.1
    (by change logScale (6547 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6529) (H := 64264741703066) (u := 87867622053)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 47, 2, 5, 2, 3, 2, 13, 2, 31, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6529

theorem upper_reach_6551 : UpperReach 6551 64440483055127 := by
  have hr := row_6551
  have hl := log_bounds hr.1
    (by change logScale (6551 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6547) (H := 64352609325195) (u := 87873729856)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6547

theorem upper_reach_6553 : UpperReach 6553 64528359837562 := by
  have hr := row_6553
  have hl := log_bounds hr.1
    (by change logScale (6553 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6551) (H := 64440483055127) (u := 87876782359)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6551

theorem upper_reach_6563 : UpperReach 6563 64616251868551 := by
  have hr := row_6563
  have hl := log_bounds hr.1
    (by change logScale (6563 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6553) (H := 64528359837562) (u := 87892030913)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 79, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6553

theorem upper_reach_6569 : UpperReach 6569 64704153037524 := by
  have hr := row_6569
  have hl := log_bounds hr.1
    (by change logScale (6569 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6563) (H := 64616251868551) (u := 87901168897)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6563

theorem upper_reach_6571 : UpperReach 6571 64792057250637 := by
  have hr := row_6571
  have hl := log_bounds hr.1
    (by change logScale (6571 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6569) (H := 64704153037524) (u := 87904213037)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6569

theorem upper_reach_6577 : UpperReach 6577 64879970590614 := by
  have hr := row_6577
  have hl := log_bounds hr.1
    (by change logScale (6577 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6571) (H := 64792057250637) (u := 87913339901)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6571

theorem upper_reach_6581 : UpperReach 6581 64967890010543 := by
  have hr := row_6581
  have hl := log_bounds hr.1
    (by change logScale (6581 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 6577) (H := 64879970590614) (u := 87919419853)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_6577

#print axioms upper_reach_6581

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
