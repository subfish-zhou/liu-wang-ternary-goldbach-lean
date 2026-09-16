import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block001 : List ℕ := [1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601]

theorem complete_Block001 :
    ∀ p ∈ Finset.Ioc 1439 1601, p.Prime ↔ p ∈ primes_Block001 := by
  decide +kernel

theorem row_1447 :
    (1447 : ℕ).Prime ∧ logScale (1447 : ℚ) = 10 ∧
      (72772477240 : ℤ) = ⌊logCenter (1447 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1447 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1447 : Reach 1447 13891672856810 129945682089 := by
  have hr := row_1447
  have hl := log_bounds hr.1
    (by change logScale (1447 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1439) (T := 13818900379570) (U := 129855878576)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1439

theorem row_1451 :
    (1451 : ℕ).Prime ∧ logScale (1451 : ℚ) = 10 ∧
      (72800082502 : ℤ) = ⌊logCenter (1451 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1451 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1451 : Reach 1451 13964472939312 130035299801 := by
  have hr := row_1451
  have hl := log_bounds hr.1
    (by change logScale (1451 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1447) (T := 13891672856810) (U := 129945682089)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1447

theorem row_1453 :
    (1453 : ℕ).Prime ∧ logScale (1453 : ℚ) = 10 ∧
      (72813856609 : ℤ) = ⌊logCenter (1453 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1453 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1453 : Reach 1453 14037286795921 130124855793 := by
  have hr := row_1453
  have hl := log_bounds hr.1
    (by change logScale (1453 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1451) (T := 13964472939312) (U := 130035299801)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1451

theorem row_1459 :
    (1459 : ℕ).Prime ∧ logScale (1459 : ℚ) = 10 ∧
      (72855065459 : ℤ) = ⌊logCenter (1459 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1459 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1459 : Reach 1459 14110141861380 130214104666 := by
  have hr := row_1459
  have hl := log_bounds hr.1
    (by change logScale (1459 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1453) (T := 14037286795921) (U := 130124855793)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1453

theorem row_1471 :
    (1471 : ℕ).Prime ∧ logScale (1471 : ℚ) = 10 ∧
      (72936977180 : ℤ) = ⌊logCenter (1471 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1471 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1471 : Reach 1471 14183078838560 130302685690 := by
  have hr := row_1471
  have hl := log_bounds hr.1
    (by change logScale (1471 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1459) (T := 14110141861380) (U := 130214104666)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1459

theorem row_1481 :
    (1481 : ℕ).Prime ∧ logScale (1481 : ℚ) = 10 ∧
      (73004728116 : ℤ) = ⌊logCenter (1481 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1481 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1481 : Reach 1481 14256083566676 130390728046 := by
  have hr := row_1481
  have hl := log_bounds hr.1
    (by change logScale (1481 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1471) (T := 14183078838560) (U := 130302685690)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1471

theorem row_1483 :
    (1483 : ℕ).Prime ∧ logScale (1483 : ℚ) = 10 ∧
      (73018223395 : ℤ) = ⌊logCenter (1483 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1483 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1483 : Reach 1483 14329101790071 130478710994 := by
  have hr := row_1483
  have hl := log_bounds hr.1
    (by change logScale (1483 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1481) (T := 14256083566676) (U := 130390728046)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1481

theorem row_1487 :
    (1487 : ℕ).Prime ∧ logScale (1487 : ℚ) = 10 ∧
      (73045159438 : ℤ) = ⌊logCenter (1487 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1487 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1487 : Reach 1487 14402146949509 130566516318 := by
  have hr := row_1487
  have hl := log_bounds hr.1
    (by change logScale (1487 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1483) (T := 14329101790071) (U := 130478710994)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1483

theorem row_1489 :
    (1489 : ℕ).Prime ∧ logScale (1489 : ℚ) = 10 ∧
      (73058600300 : ℤ) = ⌊logCenter (1489 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1489 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1489 : Reach 1489 14475205549809 130654262633 := by
  have hr := row_1489
  have hl := log_bounds hr.1
    (by change logScale (1489 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1487) (T := 14402146949509) (U := 130566516318)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1487

theorem row_1493 :
    (1493 : ℕ).Prime ∧ logScale (1493 : ℚ) = 10 ∧
      (73085427949 : ℤ) = ⌊logCenter (1493 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1493 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1493 : Reach 1493 14548290977758 130741832515 := by
  have hr := row_1493
  have hl := log_bounds hr.1
    (by change logScale (1493 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1489) (T := 14475205549809) (U := 130654262633)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1489

theorem row_1499 :
    (1499 : ℕ).Prime ∧ logScale (1499 : ℚ) = 10 ∧
      (73125534955 : ℤ) = ⌊logCenter (1499 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1499 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1499 : Reach 1499 14621416512713 130829110107 := by
  have hr := row_1499
  have hl := log_bounds hr.1
    (by change logScale (1499 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1493) (T := 14548290977758) (U := 130741832515)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1493

theorem row_1511 :
    (1511 : ℕ).Prime ∧ logScale (1511 : ℚ) = 10 ∧
      (73205269596 : ℤ) = ⌊logCenter (1511 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1511 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1511 : Reach 1511 14694621782309 130915751902 := by
  have hr := row_1511
  have hl := log_bounds hr.1
    (by change logScale (1511 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1499) (T := 14621416512713) (U := 130829110107)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1499

theorem row_1523 :
    (1523 : ℕ).Prime ∧ logScale (1523 : ℚ) = 10 ∧
      (73284373502 : ℤ) = ⌊logCenter (1523 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1523 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1523 : Reach 1523 14767906155811 131001767508 := by
  have hr := row_1523
  have hl := log_bounds hr.1
    (by change logScale (1523 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1511) (T := 14694621782309) (U := 130915751902)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1511

theorem row_1531 :
    (1531 : ℕ).Prime ∧ logScale (1531 : ℚ) = 10 ∧
      (73336763930 : ℤ) = ⌊logCenter (1531 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1531 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1531 : Reach 1531 14841242919741 131087389579 := by
  have hr := row_1531
  have hl := log_bounds hr.1
    (by change logScale (1531 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1523) (T := 14767906155811) (U := 131001767508)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1523

theorem row_1543 :
    (1543 : ℕ).Prime ∧ logScale (1543 : ℚ) = 10 ∧
      (73414838497 : ℤ) = ⌊logCenter (1543 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1543 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1543 : Reach 1543 14914657758238 131172400857 := by
  have hr := row_1543
  have hl := log_bounds hr.1
    (by change logScale (1543 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1531) (T := 14841242919741) (U := 131087389579)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1531

theorem row_1549 :
    (1549 : ℕ).Prime ∧ logScale (1549 : ℚ) = 10 ∧
      (73453648378 : ℤ) = ⌊logCenter (1549 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1549 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1549 : Reach 1549 14988111406616 131257137551 := by
  have hr := row_1549
  have hl := log_bounds hr.1
    (by change logScale (1549 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1543) (T := 14914657758238) (U := 131172400857)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1543

theorem row_1553 :
    (1553 : ℕ).Prime ∧ logScale (1553 : ℚ) = 10 ∧
      (73479438205 : ℤ) = ⌊logCenter (1553 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1553 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1553 : Reach 1553 15061590844821 131341710449 := by
  have hr := row_1553
  have hl := log_bounds hr.1
    (by change logScale (1553 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1549) (T := 14988111406616) (U := 131257137551)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1549

theorem row_1559 :
    (1559 : ℕ).Prime ∧ logScale (1559 : ℚ) = 10 ∧
      (73517998664 : ℤ) = ⌊logCenter (1559 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1559 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1559 : Reach 1559 15135108843485 131426011932 := by
  have hr := row_1559
  have hl := log_bounds hr.1
    (by change logScale (1559 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1553) (T := 15061590844821) (U := 131341710449)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1553

theorem row_1567 :
    (1567 : ℕ).Prime ∧ logScale (1567 : ℚ) = 10 ∧
      (73569182397 : ℤ) = ⌊logCenter (1567 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1567 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1567 : Reach 1567 15208678025882 131509936589 := by
  have hr := row_1567
  have hl := log_bounds hr.1
    (by change logScale (1567 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1559) (T := 15135108843485) (U := 131426011932)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1559

theorem row_1571 :
    (1571 : ℕ).Prime ∧ logScale (1571 : ℚ) = 10 ∧
      (73594676356 : ℤ) = ⌊logCenter (1571 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1571 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1571 : Reach 1571 15282272702238 131593700880 := by
  have hr := row_1571
  have hl := log_bounds hr.1
    (by change logScale (1571 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1567) (T := 15208678025882) (U := 131509936589)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1567

theorem row_1579 :
    (1579 : ℕ).Prime ∧ logScale (1579 : ℚ) = 10 ∧
      (73645470116 : ℤ) = ⌊logCenter (1579 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1579 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1579 : Reach 1579 15355918172354 131677093593 := by
  have hr := row_1579
  have hl := log_bounds hr.1
    (by change logScale (1579 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1571) (T := 15282272702238) (U := 131593700880)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1571

theorem row_1583 :
    (1583 : ℕ).Prime ∧ logScale (1583 : ℚ) = 10 ∧
      (73670770572 : ℤ) = ⌊logCenter (1583 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1583 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1583 : Reach 1583 15429588942926 131760328166 := by
  have hr := row_1583
  have hl := log_bounds hr.1
    (by change logScale (1583 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1579) (T := 15355918172354) (U := 131677093593)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1579

theorem row_1597 :
    (1597 : ℕ).Prime ∧ logScale (1597 : ℚ) = 10 ∧
      (73758821456 : ℤ) = ⌊logCenter (1597 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1597 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1597 : Reach 1597 15503347764382 131842884763 := by
  have hr := row_1597
  have hl := log_bounds hr.1
    (by change logScale (1597 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1583) (T := 15429588942926) (U := 131760328166)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1583

theorem row_1601 :
    (1601 : ℕ).Prime ∧ logScale (1601 : ℚ) = 10 ∧
      (73783837103 : ℤ) = ⌊logCenter (1601 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1601 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1601 : Reach 1601 15577131601485 131925286566 := by
  have hr := row_1601
  have hl := log_bounds hr.1
    (by change logScale (1601 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1597) (T := 15503347764382) (U := 131842884763)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1597

#print axioms reach_1601

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
