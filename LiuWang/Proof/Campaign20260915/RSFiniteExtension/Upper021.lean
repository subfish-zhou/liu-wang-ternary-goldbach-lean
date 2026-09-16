import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper020
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block021

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_5381 : UpperReach 5381 52537652388014 := by
  have hr := row_5381
  have hl := log_bounds hr.1
    (by change logScale (5381 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5351) (H := 52451746092875) (u := 85906295063)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 53, 2, 3, 2, 11, 2, 23, 2, 3, 2, 31, 2, 5, 2, 3, 2, 7, 2, 41, 2, 3, 2, 5, 2, 19, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5351

theorem upper_reach_5387 : UpperReach 5387 52623569827285 := by
  have hr := row_5387
  have hl := log_bounds hr.1
    (by change logScale (5387 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5381) (H := 52537652388014) (u := 85917439195)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5381

theorem upper_reach_5393 : UpperReach 5393 52709498398283 := by
  have hr := row_5393
  have hl := log_bounds hr.1
    (by change logScale (5393 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5387) (H := 52623569827285) (u := 85928570922)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 17, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5387

theorem upper_reach_5399 : UpperReach 5399 52795438088629 := by
  have hr := row_5399
  have hl := log_bounds hr.1
    (by change logScale (5399 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5393) (H := 52709498398283) (u := 85939690270)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5393

theorem upper_reach_5407 : UpperReach 5407 52881392585567 := by
  have hr := row_5407
  have hl := log_bounds hr.1
    (by change logScale (5407 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5399) (H := 52795438088629) (u := 85954496862)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5399

theorem upper_reach_5413 : UpperReach 5413 52967358173079 := by
  have hr := row_5413
  have hl := log_bounds hr.1
    (by change logScale (5413 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5407) (H := 52881392585567) (u := 85965587436)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5407

theorem upper_reach_5417 : UpperReach 5417 53053331147480 := by
  have hr := row_5417
  have hl := log_bounds hr.1
    (by change logScale (5417 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5413) (H := 52967358173079) (u := 85972974325)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5413

theorem upper_reach_5419 : UpperReach 5419 53139307813280 := by
  have hr := row_5419
  have hl := log_bounds hr.1
    (by change logScale (5419 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5417) (H := 53053331147480) (u := 85976665724)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5417

theorem upper_reach_5431 : UpperReach 5431 53225306598905 := by
  have hr := row_5431
  have hl := log_bounds hr.1
    (by change logScale (5431 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5419) (H := 53139307813280) (u := 85998785549)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 5, 2, 3, 2, 61, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5419

theorem upper_reach_5437 : UpperReach 5437 53311316426121 := by
  have hr := row_5437
  have hl := log_bounds hr.1
    (by change logScale (5437 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5431) (H := 53225306598905) (u := 86009827140)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5431

theorem upper_reach_5441 : UpperReach 5441 53397333607630 := by
  have hr := row_5441
  have hl := log_bounds hr.1
    (by change logScale (5441 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5437) (H := 53311316426121) (u := 86017181433)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5437

theorem upper_reach_5443 : UpperReach 5443 53483354464259 := by
  have hr := row_5443
  have hl := log_bounds hr.1
    (by change logScale (5443 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5441) (H := 53397333607630) (u := 86020856553)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5441

theorem upper_reach_5449 : UpperReach 5449 53569386338149 := by
  have hr := row_5449
  have hl := log_bounds hr.1
    (by change logScale (5449 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5443) (H := 53483354464259) (u := 86031873814)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5443

theorem upper_reach_5471 : UpperReach 5471 53655458505134 := by
  have hr := row_5471
  have hl := log_bounds hr.1
    (by change logScale (5471 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5449) (H := 53569386338149) (u := 86072166909)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 5, 2, 3, 2, 53, 2, 43, 2, 3, 2, 5, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5449

theorem upper_reach_5477 : UpperReach 5477 53741541633026 := by
  have hr := row_5477
  have hl := log_bounds hr.1
    (by change logScale (5477 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5471) (H := 53655458505134) (u := 86083127816)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5471

theorem upper_reach_5479 : UpperReach 5479 53827628411886 := by
  have hr := row_5479
  have hl := log_bounds hr.1
    (by change logScale (5479 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5477) (H := 53741541633026) (u := 86086778784)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5477

theorem upper_reach_5483 : UpperReach 5483 53913722488684 := by
  have hr := row_5483
  have hl := log_bounds hr.1
    (by change logScale (5483 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5479) (H := 53827628411886) (u := 86094076722)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5479

theorem upper_reach_5501 : UpperReach 5501 53999849340457 := by
  have hr := row_5501
  have hl := log_bounds hr.1
    (by change logScale (5501 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5483) (H := 53913722488684) (u := 86126851697)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 11, 2, 17, 2, 3, 2, 5, 2, 23, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5483

theorem upper_reach_5503 : UpperReach 5503 54085979827272 := by
  have hr := row_5503
  have hl := log_bounds hr.1
    (by change logScale (5503 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5501) (H := 53999849340457) (u := 86130486739)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5501

theorem upper_reach_5507 : UpperReach 5507 54172117580209 := by
  have hr := row_5507
  have hl := log_bounds hr.1
    (by change logScale (5507 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5503) (H := 54085979827272) (u := 86137752861)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5503

theorem upper_reach_5519 : UpperReach 5519 54258277099888 := by
  have hr := row_5519
  have hl := log_bounds hr.1
    (by change logScale (5519 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5507) (H := 54172117580209) (u := 86159519603)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 37, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5507

theorem upper_reach_5521 : UpperReach 5521 54344440242755 := by
  have hr := row_5521
  have hl := log_bounds hr.1
    (by change logScale (5521 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5519) (H := 54258277099888) (u := 86163142791)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5519

theorem upper_reach_5527 : UpperReach 5527 54430614247318 := by
  have hr := row_5527
  have hl := log_bounds hr.1
    (by change logScale (5527 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5521) (H := 54344440242755) (u := 86174004487)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5521

theorem upper_reach_5531 : UpperReach 5531 54516795486462 := by
  have hr := row_5531
  have hl := log_bounds hr.1
    (by change logScale (5531 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 5527) (H := 54430614247318) (u := 86181239068)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_5527

#print axioms upper_reach_5531

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
