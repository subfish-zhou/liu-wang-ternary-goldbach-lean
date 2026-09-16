import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper048
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block049

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_11447 : UpperReach 11447 113063479915505 := by
  have hr := row_11447
  have hl := log_bounds hr.1
    (by change logScale (11447 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11443) (H := 112970025085804) (u := 93454829625)
    (by norm_num) (by norm_num) hr.1 gap_11447 hl.2
    (by norm_num) upper_reach_11443

theorem upper_reach_11467 : UpperReach 11467 113156952201787 := by
  have hr := row_11467
  have hl := log_bounds hr.1
    (by change logScale (11467 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11447) (H := 113063479915505) (u := 93472286206)
    (by norm_num) (by norm_num) hr.1 gap_11467 hl.2
    (by norm_num) upper_reach_11447

theorem upper_reach_11471 : UpperReach 11471 113250427975732 := by
  have hr := row_11471
  have hl := log_bounds hr.1
    (by change logScale (11471 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11467) (H := 113156952201787) (u := 93475773869)
    (by norm_num) (by norm_num) hr.1 gap_11471 hl.2
    (by norm_num) upper_reach_11467

theorem upper_reach_11483 : UpperReach 11483 113343914205371 := by
  have hr := row_11483
  have hl := log_bounds hr.1
    (by change logScale (11483 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11471) (H := 113250427975732) (u := 93486229563)
    (by norm_num) (by norm_num) hr.1 gap_11483 hl.2
    (by norm_num) upper_reach_11471

theorem upper_reach_11489 : UpperReach 11489 113437405658761 := by
  have hr := row_11489
  have hl := log_bounds hr.1
    (by change logScale (11489 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11483) (H := 113343914205371) (u := 93491453314)
    (by norm_num) (by norm_num) hr.1 gap_11489 hl.2
    (by norm_num) upper_reach_11483

theorem upper_reach_11491 : UpperReach 11491 113530898852795 := by
  have hr := row_11491
  have hl := log_bounds hr.1
    (by change logScale (11491 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11489) (H := 113437405658761) (u := 93493193958)
    (by norm_num) (by norm_num) hr.1 gap_11491 hl.2
    (by norm_num) upper_reach_11489

theorem upper_reach_11497 : UpperReach 11497 113624397266944 := by
  have hr := row_11497
  have hl := log_bounds hr.1
    (by change logScale (11497 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11491) (H := 113530898852795) (u := 93498414073)
    (by norm_num) (by norm_num) hr.1 gap_11497 hl.2
    (by norm_num) upper_reach_11491

theorem upper_reach_11503 : UpperReach 11503 113717900898485 := by
  have hr := row_11503
  have hl := log_bounds hr.1
    (by change logScale (11503 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11497) (H := 113624397266944) (u := 93503631465)
    (by norm_num) (by norm_num) hr.1 gap_11503 hl.2
    (by norm_num) upper_reach_11497

theorem upper_reach_11519 : UpperReach 11519 113811418429776 := by
  have hr := row_11519
  have hl := log_bounds hr.1
    (by change logScale (11519 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11503) (H := 113717900898485) (u := 93517531215)
    (by norm_num) (by norm_num) hr.1 gap_11519 hl.2
    (by norm_num) upper_reach_11503

theorem upper_reach_11527 : UpperReach 11527 113904942903704 := by
  have hr := row_11527
  have hl := log_bounds hr.1
    (by change logScale (11527 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11519) (H := 113811418429776) (u := 93524473852)
    (by norm_num) (by norm_num) hr.1 gap_11527 hl.2
    (by norm_num) upper_reach_11519

theorem upper_reach_11549 : UpperReach 11549 113998486445067 := by
  have hr := row_11549
  have hl := log_bounds hr.1
    (by change logScale (11549 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11527) (H := 113904942903704) (u := 93543541287)
    (by norm_num) (by norm_num) hr.1 gap_11549 hl.2
    (by norm_num) upper_reach_11527

theorem upper_reach_11551 : UpperReach 11551 114092031718032 := by
  have hr := row_11551
  have hl := log_bounds hr.1
    (by change logScale (11551 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11549) (H := 113998486445067) (u := 93545272889)
    (by norm_num) (by norm_num) hr.1 gap_11551 hl.2
    (by norm_num) upper_reach_11549

theorem upper_reach_11579 : UpperReach 11579 114185601201990 := by
  have hr := row_11579
  have hl := log_bounds hr.1
    (by change logScale (11579 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11551) (H := 114092031718032) (u := 93569483882)
    (by norm_num) (by norm_num) hr.1 gap_11579 hl.2
    (by norm_num) upper_reach_11551

theorem upper_reach_11587 : UpperReach 11587 114279177592622 := by
  have hr := row_11587
  have hl := log_bounds hr.1
    (by change logScale (11587 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11579) (H := 114185601201990) (u := 93576390556)
    (by norm_num) (by norm_num) hr.1 gap_11587 hl.2
    (by norm_num) upper_reach_11579

theorem upper_reach_11593 : UpperReach 11593 114372759160130 := by
  have hr := row_11593
  have hl := log_bounds hr.1
    (by change logScale (11593 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11587) (H := 114279177592622) (u := 93581567432)
    (by norm_num) (by norm_num) hr.1 gap_11593 hl.2
    (by norm_num) upper_reach_11587

theorem upper_reach_11597 : UpperReach 11597 114466344177401 := by
  have hr := row_11597
  have hl := log_bounds hr.1
    (by change logScale (11597 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11593) (H := 114372759160130) (u := 93585017195)
    (by norm_num) (by norm_num) hr.1 gap_11597 hl.2
    (by norm_num) upper_reach_11593

theorem upper_reach_11617 : UpperReach 11617 114559946425658 := by
  have hr := row_11617
  have hl := log_bounds hr.1
    (by change logScale (11617 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11597) (H := 114466344177401) (u := 93602248181)
    (by norm_num) (by norm_num) hr.1 gap_11617 hl.2
    (by norm_num) upper_reach_11597

theorem upper_reach_11621 : UpperReach 11621 114653552116552 := by
  have hr := row_11621
  have hl := log_bounds hr.1
    (by change logScale (11621 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11617) (H := 114559946425658) (u := 93605690818)
    (by norm_num) (by norm_num) hr.1 gap_11621 hl.2
    (by norm_num) upper_reach_11617

theorem upper_reach_11633 : UpperReach 11633 114747168128252 := by
  have hr := row_11633
  have hl := log_bounds hr.1
    (by change logScale (11633 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11621) (H := 114653552116552) (u := 93616011624)
    (by norm_num) (by norm_num) hr.1 gap_11633 hl.2
    (by norm_num) upper_reach_11621

theorem upper_reach_11657 : UpperReach 11657 114840804749663 := by
  have hr := row_11657
  have hl := log_bounds hr.1
    (by change logScale (11657 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11633) (H := 114747168128252) (u := 93636621335)
    (by norm_num) (by norm_num) hr.1 gap_11657 hl.2
    (by norm_num) upper_reach_11633

theorem upper_reach_11677 : UpperReach 11677 114934458513445 := by
  have hr := row_11677
  have hl := log_bounds hr.1
    (by change logScale (11677 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11657) (H := 114840804749663) (u := 93653763706)
    (by norm_num) (by norm_num) hr.1 gap_11677 hl.2
    (by norm_num) upper_reach_11657

theorem upper_reach_11681 : UpperReach 11681 115028115702178 := by
  have hr := row_11681
  have hl := log_bounds hr.1
    (by change logScale (11681 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11677) (H := 114934458513445) (u := 93657188657)
    (by norm_num) (by norm_num) hr.1 gap_11681 hl.2
    (by norm_num) upper_reach_11677

theorem upper_reach_11689 : UpperReach 11689 115121779737296 := by
  have hr := row_11689
  have hl := log_bounds hr.1
    (by change logScale (11689 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11681) (H := 115028115702178) (u := 93664035042)
    (by norm_num) (by norm_num) hr.1 gap_11689 hl.2
    (by norm_num) upper_reach_11681

theorem upper_reach_11699 : UpperReach 11699 115215452323808 := by
  have hr := row_11699
  have hl := log_bounds hr.1
    (by change logScale (11699 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 11689) (H := 115121779737296) (u := 93672586436)
    (by norm_num) (by norm_num) hr.1 gap_11699 hl.2
    (by norm_num) upper_reach_11689

#print axioms upper_reach_11699

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
