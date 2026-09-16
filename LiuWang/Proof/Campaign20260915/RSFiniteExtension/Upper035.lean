import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper034
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block035

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_8329 : UpperReach 8329 82174771916711 := by
  have hr := row_8329
  have hl := log_bounds hr.1
    (by change logScale (8329 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8317) (H := 82084496929870) (u := 90274986765)
    (by norm_num) (by norm_num) hr.1 gap_8329 hl.2
    (by norm_num) upper_reach_8317

theorem upper_reach_8353 : UpperReach 8353 82265075677100 := by
  have hr := row_8353
  have hl := log_bounds hr.1
    (by change logScale (8353 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8329) (H := 82174771916711) (u := 90303760313)
    (by norm_num) (by norm_num) hr.1 gap_8353 hl.2
    (by norm_num) upper_reach_8329

theorem upper_reach_8363 : UpperReach 8363 82355391402076 := by
  have hr := row_8363
  have hl := log_bounds hr.1
    (by change logScale (8363 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8353) (H := 82265075677100) (u := 90315724900)
    (by norm_num) (by norm_num) hr.1 gap_8363 hl.2
    (by norm_num) upper_reach_8353

theorem upper_reach_8369 : UpperReach 8369 82445714298938 := by
  have hr := row_8369
  have hl := log_bounds hr.1
    (by change logScale (8369 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8363) (H := 82355391402076) (u := 90322896786)
    (by norm_num) (by norm_num) hr.1 gap_8369 hl.2
    (by norm_num) upper_reach_8363

theorem upper_reach_8377 : UpperReach 8377 82536046750321 := by
  have hr := row_8377
  have hl := log_bounds hr.1
    (by change logScale (8377 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8369) (H := 82445714298938) (u := 90332451307)
    (by norm_num) (by norm_num) hr.1 gap_8377 hl.2
    (by norm_num) upper_reach_8369

theorem upper_reach_8387 : UpperReach 8387 82626391132033 := by
  have hr := row_8387
  have hl := log_bounds hr.1
    (by change logScale (8387 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8377) (H := 82536046750321) (u := 90344381636)
    (by norm_num) (by norm_num) hr.1 gap_8387 hl.2
    (by norm_num) upper_reach_8377

theorem upper_reach_8389 : UpperReach 8389 82716737898103 := by
  have hr := row_8389
  have hl := log_bounds hr.1
    (by change logScale (8389 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8387) (H := 82626391132033) (u := 90346765994)
    (by norm_num) (by norm_num) hr.1 gap_8389 hl.2
    (by norm_num) upper_reach_8387

theorem upper_reach_8419 : UpperReach 8419 82807120361498 := by
  have hr := row_8419
  have hl := log_bounds hr.1
    (by change logScale (8419 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8389) (H := 82716737898103) (u := 90382463319)
    (by norm_num) (by norm_num) hr.1 gap_8419 hl.2
    (by norm_num) upper_reach_8389

theorem upper_reach_8423 : UpperReach 8423 82897507574923 := by
  have hr := row_8423
  have hl := log_bounds hr.1
    (by change logScale (8423 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8419) (H := 82807120361498) (u := 90387213349)
    (by norm_num) (by norm_num) hr.1 gap_8423 hl.2
    (by norm_num) upper_reach_8419

theorem upper_reach_8429 : UpperReach 8429 82987901909165 := by
  have hr := row_8429
  have hl := log_bounds hr.1
    (by change logScale (8429 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8423) (H := 82897507574923) (u := 90394334166)
    (by norm_num) (by norm_num) hr.1 gap_8429 hl.2
    (by norm_num) upper_reach_8423

theorem upper_reach_8431 : UpperReach 8431 83078298615886 := by
  have hr := row_8431
  have hl := log_bounds hr.1
    (by change logScale (8431 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8429) (H := 82987901909165) (u := 90396706645)
    (by norm_num) (by norm_num) hr.1 gap_8431 hl.2
    (by norm_num) upper_reach_8429

theorem upper_reach_8443 : UpperReach 8443 83168709545674 := by
  have hr := row_8443
  have hl := log_bounds hr.1
    (by change logScale (8443 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8431) (H := 83078298615886) (u := 90410929712)
    (by norm_num) (by norm_num) hr.1 gap_8443 hl.2
    (by norm_num) upper_reach_8431

theorem upper_reach_8447 : UpperReach 8447 83259125211993 := by
  have hr := row_8447
  have hl := log_bounds hr.1
    (by change logScale (8447 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8443) (H := 83168709545674) (u := 90415666243)
    (by norm_num) (by norm_num) hr.1 gap_8447 hl.2
    (by norm_num) upper_reach_8443

theorem upper_reach_8461 : UpperReach 8461 83349557438524 := by
  have hr := row_8461
  have hl := log_bounds hr.1
    (by change logScale (8461 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8447) (H := 83259125211993) (u := 90432226455)
    (by norm_num) (by norm_num) hr.1 gap_8461 hl.2
    (by norm_num) upper_reach_8447

theorem upper_reach_8467 : UpperReach 8467 83439996753902 := by
  have hr := row_8467
  have hl := log_bounds hr.1
    (by change logScale (8467 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8461) (H := 83349557438524) (u := 90439315302)
    (by norm_num) (by norm_num) hr.1 gap_8467 hl.2
    (by norm_num) upper_reach_8461

theorem upper_reach_8501 : UpperReach 8501 83530476144770 := by
  have hr := row_8501
  have hl := log_bounds hr.1
    (by change logScale (8501 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8467) (H := 83439996753902) (u := 90479390792)
    (by norm_num) (by norm_num) hr.1 gap_8501 hl.2
    (by norm_num) upper_reach_8467

theorem upper_reach_8513 : UpperReach 8513 83620969641671 := by
  have hr := row_8513
  have hl := log_bounds hr.1
    (by change logScale (8513 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8501) (H := 83530476144770) (u := 90493496825)
    (by norm_num) (by norm_num) hr.1 gap_8513 hl.2
    (by norm_num) upper_reach_8501

theorem upper_reach_8521 : UpperReach 8521 83711472531551 := by
  have hr := row_8521
  have hl := log_bounds hr.1
    (by change logScale (8521 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8513) (H := 83620969641671) (u := 90502889804)
    (by norm_num) (by norm_num) hr.1 gap_8521 hl.2
    (by norm_num) upper_reach_8513

theorem upper_reach_8527 : UpperReach 8527 83801982460380 := by
  have hr := row_8527
  have hl := log_bounds hr.1
    (by change logScale (8527 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8521) (H := 83711472531551) (u := 90509928753)
    (by norm_num) (by norm_num) hr.1 gap_8527 hl.2
    (by norm_num) upper_reach_8521

theorem upper_reach_8537 : UpperReach 8537 83892504109792 := by
  have hr := row_8537
  have hl := log_bounds hr.1
    (by change logScale (8537 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8527) (H := 83801982460380) (u := 90521649336)
    (by norm_num) (by norm_num) hr.1 gap_8537 hl.2
    (by norm_num) upper_reach_8527

theorem upper_reach_8539 : UpperReach 8539 83983028101673 := by
  have hr := row_8539
  have hl := log_bounds hr.1
    (by change logScale (8539 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8537) (H := 83892504109792) (u := 90523991805)
    (by norm_num) (by norm_num) hr.1 gap_8539 hl.2
    (by norm_num) upper_reach_8537

theorem upper_reach_8543 : UpperReach 8543 84073556776846 := by
  have hr := row_8543
  have hl := log_bounds hr.1
    (by change logScale (8543 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8539) (H := 83983028101673) (u := 90528675097)
    (by norm_num) (by norm_num) hr.1 gap_8543 hl.2
    (by norm_num) upper_reach_8539

theorem upper_reach_8563 : UpperReach 8563 84164108835638 := by
  have hr := row_8563
  have hl := log_bounds hr.1
    (by change logScale (8563 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8543) (H := 84073556776846) (u := 90552058716)
    (by norm_num) (by norm_num) hr.1 gap_8563 hl.2
    (by norm_num) upper_reach_8543

theorem upper_reach_8573 : UpperReach 8573 84254672565766 := by
  have hr := row_8573
  have hl := log_bounds hr.1
    (by change logScale (8573 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 8563) (H := 84164108835638) (u := 90563730052)
    (by norm_num) (by norm_num) hr.1 gap_8573 hl.2
    (by norm_num) upper_reach_8563

#print axioms upper_reach_8573

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
