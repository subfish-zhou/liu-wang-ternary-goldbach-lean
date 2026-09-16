import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper016
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block017

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_4517 : UpperReach 4517 44374320282791 := by
  have hr := row_4517
  have hl := log_bounds hr.1
    (by change logScale (4517 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4513) (H := 44290164249390) (u := 84156033325)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4513

theorem upper_reach_4519 : UpperReach 4519 44458480742929 := by
  have hr := row_4519
  have hl := log_bounds hr.1
    (by change logScale (4519 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4517) (H := 44374320282791) (u := 84160460062)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4517

theorem upper_reach_4523 : UpperReach 4523 44542650050668 := by
  have hr := row_4523
  have hl := log_bounds hr.1
    (by change logScale (4523 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4519) (H := 44458480742929) (u := 84169307663)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4519

theorem upper_reach_4547 : UpperReach 4547 44626872280251 := by
  have hr := row_4547
  have hl := log_bounds hr.1
    (by change logScale (4547 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4523) (H := 44542650050668) (u := 84222229507)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 7, 2, 23, 2, 3, 2, 5, 2, 13, 2, 3, 2, 19, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4523

theorem upper_reach_4549 : UpperReach 4549 44711098907371 := by
  have hr := row_4549
  have hl := log_bounds hr.1
    (by change logScale (4549 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4547) (H := 44626872280251) (u := 84226627044)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4547

theorem upper_reach_4561 : UpperReach 4561 44795351879182 := by
  have hr := row_4561
  have hl := log_bounds hr.1
    (by change logScale (4561 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4549) (H := 44711098907371) (u := 84252971735)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 29, 2, 5, 2, 3, 2, 47, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4549

theorem upper_reach_4567 : UpperReach 4567 44879617997358 := by
  have hr := row_4567
  have hl := log_bounds hr.1
    (by change logScale (4567 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4561) (H := 44795351879182) (u := 84266118100)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4561

theorem upper_reach_4583 : UpperReach 4583 44963919088247 := by
  have hr := row_4583
  have hl := log_bounds hr.1
    (by change logScale (4583 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4567) (H := 44879617997358) (u := 84301090813)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 17, 2, 3, 2, 23, 2, 19, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4567

theorem upper_reach_4591 : UpperReach 4591 45048237619734 := by
  have hr := row_4591
  have hl := log_bounds hr.1
    (by change logScale (4591 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4583) (H := 44963919088247) (u := 84318531411)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4583

theorem upper_reach_4597 : UpperReach 4597 45132569211736 := by
  have hr := row_4597
  have hl := log_bounds hr.1
    (by change logScale (4597 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4591) (H := 45048237619734) (u := 84331591926)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4591

theorem upper_reach_4603 : UpperReach 4603 45216913847218 := by
  have hr := row_4603
  have hl := log_bounds hr.1
    (by change logScale (4603 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4597) (H := 45132569211736) (u := 84344635406)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 43, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4597

theorem upper_reach_4621 : UpperReach 4621 45301297511371 := by
  have hr := row_4621
  have hl := log_bounds hr.1
    (by change logScale (4621 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4603) (H := 45216913847218) (u := 84383664077)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 17, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 31, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4603

theorem upper_reach_4637 : UpperReach 4637 45385715740259 := by
  have hr := row_4637
  have hl := log_bounds hr.1
    (by change logScale (4637 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4621) (H := 45301297511371) (u := 84418228812)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 41, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4621

theorem upper_reach_4639 : UpperReach 4639 45470138281351 := by
  have hr := row_4639
  have hl := log_bounds hr.1
    (by change logScale (4639 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4637) (H := 45385715740259) (u := 84422541016)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4637

theorem upper_reach_4643 : UpperReach 4643 45554569441276 := by
  have hr := row_4643
  have hl := log_bounds hr.1
    (by change logScale (4643 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4639) (H := 45470138281351) (u := 84431159849)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4639

theorem upper_reach_4649 : UpperReach 4649 45639013515537 := by
  have hr := row_4649
  have hl := log_bounds hr.1
    (by change logScale (4649 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4643) (H := 45554569441276) (u := 84444074185)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4643

theorem upper_reach_4651 : UpperReach 4651 45723461890874 := by
  have hr := row_4651
  have hl := log_bounds hr.1
    (by change logScale (4651 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4649) (H := 45639013515537) (u := 84448375261)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4649

theorem upper_reach_4657 : UpperReach 4657 45807923158348 := by
  have hr := row_4657
  have hl := log_bounds hr.1
    (by change logScale (4657 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4651) (H := 45723461890874) (u := 84461267398)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4651

theorem upper_reach_4663 : UpperReach 4663 45892397301360 := by
  have hr := row_4663
  have hl := log_bounds hr.1
    (by change logScale (4663 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4657) (H := 45807923158348) (u := 84474142936)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 59, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4657

theorem upper_reach_4673 : UpperReach 4673 45976892866831 := by
  have hr := row_4673
  have hl := log_bounds hr.1
    (by change logScale (4673 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4663) (H := 45892397301360) (u := 84495565395)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 13, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4663

theorem upper_reach_4679 : UpperReach 4679 46061401263784 := by
  have hr := row_4679
  have hl := log_bounds hr.1
    (by change logScale (4679 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4673) (H := 45976892866831) (u := 84508396877)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4673

theorem upper_reach_4691 : UpperReach 4691 46145935274412 := by
  have hr := row_4691
  have hl := log_bounds hr.1
    (by change logScale (4691 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4679) (H := 46061401263784) (u := 84534010552)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 31, 2, 3, 2, 5, 2, 43, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4679

theorem upper_reach_4703 : UpperReach 4703 46230494833276 := by
  have hr := row_4703
  have hl := log_bounds hr.1
    (by change logScale (4703 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4691) (H := 46145935274412) (u := 84559558788)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 13, 2, 3, 2, 7, 2, 37, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4691

theorem upper_reach_4721 : UpperReach 4721 46315092592526 := by
  have hr := row_4721
  have hl := log_bounds hr.1
    (by change logScale (4721 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 4703) (H := 46230494833276) (u := 84597759174)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5, 2, 53, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_4703

#print axioms upper_reach_4721

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
