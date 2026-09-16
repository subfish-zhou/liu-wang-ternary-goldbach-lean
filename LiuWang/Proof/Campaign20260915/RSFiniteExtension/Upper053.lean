import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper052
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block053

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_12377 : UpperReach 12377 122074054126627 := by
  have hr := row_12377
  have hl := log_bounds hr.1
    (by change logScale (12377 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12373) (H := 121979818174680) (u := 94235951871)
    (by norm_num) (by norm_num) hr.1 gap_12377 hl.2
    (by norm_num) upper_reach_12373

theorem upper_reach_12379 : UpperReach 12379 122168291694344 := by
  have hr := row_12379
  have hl := log_bounds hr.1
    (by change logScale (12379 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12377) (H := 122074054126627) (u := 94237567641)
    (by norm_num) (by norm_num) hr.1 gap_12379 hl.2
    (by norm_num) upper_reach_12377

theorem upper_reach_12391 : UpperReach 12391 122262538951202 := by
  have hr := row_12391
  have hl := log_bounds hr.1
    (by change logScale (12391 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12379) (H := 122168291694344) (u := 94247256782)
    (by norm_num) (by norm_num) hr.1 gap_12391 hl.2
    (by norm_num) upper_reach_12379

theorem upper_reach_12401 : UpperReach 12401 122356794275179 := by
  have hr := row_12401
  have hl := log_bounds hr.1
    (by change logScale (12401 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12391) (H := 122262538951202) (u := 94255323901)
    (by norm_num) (by norm_num) hr.1 gap_12401 hl.2
    (by norm_num) upper_reach_12391

theorem upper_reach_12409 : UpperReach 12409 122451056048168 := by
  have hr := row_12409
  have hl := log_bounds hr.1
    (by change logScale (12409 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12401) (H := 122356794275179) (u := 94261772913)
    (by norm_num) (by norm_num) hr.1 gap_12409 hl.2
    (by norm_num) upper_reach_12401

theorem upper_reach_12413 : UpperReach 12413 122545321044105 := by
  have hr := row_12413
  have hl := log_bounds hr.1
    (by change logScale (12413 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12409) (H := 122451056048168) (u := 94264995861)
    (by norm_num) (by norm_num) hr.1 gap_12413 hl.2
    (by norm_num) upper_reach_12409

theorem upper_reach_12421 : UpperReach 12421 122639592482822 := by
  have hr := row_12421
  have hl := log_bounds hr.1
    (by change logScale (12421 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12413) (H := 122545321044105) (u := 94271438641)
    (by norm_num) (by norm_num) hr.1 gap_12421 hl.2
    (by norm_num) upper_reach_12413

theorem upper_reach_12433 : UpperReach 12433 122733873577933 := by
  have hr := row_12433
  have hl := log_bounds hr.1
    (by change logScale (12433 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12421) (H := 122639592482822) (u := 94281095035)
    (by norm_num) (by norm_num) hr.1 gap_12433 hl.2
    (by norm_num) upper_reach_12421

theorem upper_reach_12437 : UpperReach 12437 122828157889771 := by
  have hr := row_12437
  have hl := log_bounds hr.1
    (by change logScale (12437 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12433) (H := 122733873577933) (u := 94284311762)
    (by norm_num) (by norm_num) hr.1 gap_12437 hl.2
    (by norm_num) upper_reach_12433

theorem upper_reach_12451 : UpperReach 12451 122922453452012 := by
  have hr := row_12451
  have hl := log_bounds hr.1
    (by change logScale (12451 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12437) (H := 122828157889771) (u := 94295562165)
    (by norm_num) (by norm_num) hr.1 gap_12451 hl.2
    (by norm_num) upper_reach_12437

theorem upper_reach_12457 : UpperReach 12457 123016753831983 := by
  have hr := row_12457
  have hl := log_bounds hr.1
    (by change logScale (12457 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12451) (H := 122922453452012) (u := 94300379895)
    (by norm_num) (by norm_num) hr.1 gap_12457 hl.2
    (by norm_num) upper_reach_12451

theorem upper_reach_12473 : UpperReach 12473 123111067047896 := by
  have hr := row_12473
  have hl := log_bounds hr.1
    (by change logScale (12473 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12457) (H := 123016753831983) (u := 94313215837)
    (by norm_num) (by norm_num) hr.1 gap_12473 hl.2
    (by norm_num) upper_reach_12457

theorem upper_reach_12479 : UpperReach 12479 123205385073043 := by
  have hr := row_12479
  have hl := log_bounds hr.1
    (by change logScale (12479 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12473) (H := 123111067047896) (u := 94318025071)
    (by norm_num) (by norm_num) hr.1 gap_12479 hl.2
    (by norm_num) upper_reach_12473

theorem upper_reach_12487 : UpperReach 12487 123299709506906 := by
  have hr := row_12487
  have hl := log_bounds hr.1
    (by change logScale (12487 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12479) (H := 123205385073043) (u := 94324433787)
    (by norm_num) (by norm_num) hr.1 gap_12487 hl.2
    (by norm_num) upper_reach_12479

theorem upper_reach_12491 : UpperReach 12491 123394037143587 := by
  have hr := row_12491
  have hl := log_bounds hr.1
    (by change logScale (12491 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12487) (H := 123299709506906) (u := 94327636605)
    (by norm_num) (by norm_num) hr.1 gap_12491 hl.2
    (by norm_num) upper_reach_12487

theorem upper_reach_12497 : UpperReach 12497 123488369582574 := by
  have hr := row_12497
  have hl := log_bounds hr.1
    (by change logScale (12497 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12491) (H := 123394037143587) (u := 94332438911)
    (by norm_num) (by norm_num) hr.1 gap_12497 hl.2
    (by norm_num) upper_reach_12491

theorem upper_reach_12503 : UpperReach 12503 123582706821561 := by
  have hr := row_12503
  have hl := log_bounds hr.1
    (by change logScale (12503 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12497) (H := 123488369582574) (u := 94337238911)
    (by norm_num) (by norm_num) hr.1 gap_12503 hl.2
    (by norm_num) upper_reach_12497

theorem upper_reach_12511 : UpperReach 12511 123677050456966 := by
  have hr := row_12511
  have hl := log_bounds hr.1
    (by change logScale (12511 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12503) (H := 123582706821561) (u := 94343635329)
    (by norm_num) (by norm_num) hr.1 gap_12511 hl.2
    (by norm_num) upper_reach_12503

theorem upper_reach_12517 : UpperReach 12517 123771398887001 := by
  have hr := row_12517
  have hl := log_bounds hr.1
    (by change logScale (12517 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12511) (H := 123677050456966) (u := 94348429959)
    (by norm_num) (by norm_num) hr.1 gap_12517 hl.2
    (by norm_num) upper_reach_12511

theorem upper_reach_12527 : UpperReach 12527 123865755302981 := by
  have hr := row_12527
  have hl := log_bounds hr.1
    (by change logScale (12527 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12517) (H := 123771398887001) (u := 94356415904)
    (by norm_num) (by norm_num) hr.1 gap_12527 hl.2
    (by norm_num) upper_reach_12517

theorem upper_reach_12539 : UpperReach 12539 123960121293685 := by
  have hr := row_12539
  have hl := log_bounds hr.1
    (by change logScale (12539 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12527) (H := 123865755302981) (u := 94365990628)
    (by norm_num) (by norm_num) hr.1 gap_12539 hl.2
    (by norm_num) upper_reach_12527

theorem upper_reach_12541 : UpperReach 12541 124054488879285 := by
  have hr := row_12541
  have hl := log_bounds hr.1
    (by change logScale (12541 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12539) (H := 123960121293685) (u := 94367585524)
    (by norm_num) (by norm_num) hr.1 gap_12541 hl.2
    (by norm_num) upper_reach_12539

theorem upper_reach_12547 : UpperReach 12547 124148861248048 := by
  have hr := row_12547
  have hl := log_bounds hr.1
    (by change logScale (12547 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12541) (H := 124054488879285) (u := 94372368687)
    (by norm_num) (by norm_num) hr.1 gap_12547 hl.2
    (by norm_num) upper_reach_12541

theorem upper_reach_12553 : UpperReach 12553 124243238397688 := by
  have hr := row_12553
  have hl := log_bounds hr.1
    (by change logScale (12553 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 12547) (H := 124148861248048) (u := 94377149564)
    (by norm_num) (by norm_num) hr.1 gap_12553 hl.2
    (by norm_num) upper_reach_12547

#print axioms upper_reach_12553

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
