import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block057
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_13469 : PrimeGap 13463 13469 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13469 :
    (13469 : ℕ).Prime ∧ logScale (13469 : ℚ) = 13 ∧
      (95081460242 : ℤ) = ⌊logCenter (13469 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13469 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13469 : Reach 13469 133432398561688 169512182703 := by
  have hr := row_13469
  have hl := log_bounds hr.1
    (by change logScale (13469 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13463) (T := 133337317101446) (U := 169499597345)
    (by norm_num) (by norm_num) hr.1 gap_13469
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13463

theorem gap_13477 : PrimeGap 13469 13477 :=
  (primeGap_of_factors (ds := [2, 19, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13477 :
    (13477 : ℕ).Prime ∧ logScale (13477 : ℚ) = 13 ∧
      (95087398043 : ℤ) = ⌊logCenter (13477 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13477 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13477 : Reach 13477 133527485959731 169524761524 := by
  have hr := row_13477
  have hl := log_bounds hr.1
    (by change logScale (13477 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13469) (T := 133432398561688) (U := 169512182703)
    (by norm_num) (by norm_num) hr.1 gap_13477
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13469

theorem gap_13487 : PrimeGap 13477 13487 :=
  (primeGap_of_factors (ds := [2, 3, 2, 13, 2, 97, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13487 :
    (13487 : ℕ).Prime ∧ logScale (13487 : ℚ) = 13 ∧
      (95094815341 : ℤ) = ⌊logCenter (13487 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13487 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13487 : Reach 13487 133622580775072 169537331950 := by
  have hr := row_13487
  have hl := log_bounds hr.1
    (by change logScale (13487 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13477) (T := 133527485959731) (U := 169524761524)
    (by norm_num) (by norm_num) hr.1 gap_13487
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13477

theorem gap_13499 : PrimeGap 13487 13499 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 103, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13499 :
    (13499 : ℕ).Prime ∧ logScale (13499 : ℚ) = 13 ∧
      (95103708842 : ℤ) = ⌊logCenter (13499 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13499 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13499 : Reach 13499 133717684483914 169549892132 := by
  have hr := row_13499
  have hl := log_bounds hr.1
    (by change logScale (13499 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13487) (T := 133622580775072) (U := 169537331950)
    (by norm_num) (by norm_num) hr.1 gap_13499
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13487

theorem gap_13513 : PrimeGap 13499 13513 :=
  (primeGap_of_factors (ds := [2, 23, 2, 3, 2, 5, 2, 13, 2, 3, 2, 59, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13513 :
    (13513 : ℕ).Prime ∧ logScale (13513 : ℚ) = 13 ∧
      (95114074606 : ℤ) = ⌊logCenter (13513 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13513 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13513 : Reach 13513 133812798558520 169562440230 := by
  have hr := row_13513
  have hl := log_bounds hr.1
    (by change logScale (13513 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13499) (T := 133717684483914) (U := 169549892132)
    (by norm_num) (by norm_num) hr.1 gap_13513
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13499

theorem gap_13523 : PrimeGap 13513 13523 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13523 :
    (13523 : ℕ).Prime ∧ logScale (13523 : ℚ) = 13 ∧
      (95121472150 : ℤ) = ⌊logCenter (13523 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13523 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13523 : Reach 13523 133907920030670 169574979976 := by
  have hr := row_13523
  have hl := log_bounds hr.1
    (by change logScale (13523 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13513) (T := 133812798558520) (U := 169562440230)
    (by norm_num) (by norm_num) hr.1 gap_13523
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13513

theorem gap_13537 : PrimeGap 13523 13537 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 83, 2, 7, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13537 :
    (13537 : ℕ).Prime ∧ logScale (13537 : ℚ) = 13 ∧
      (95131819528 : ℤ) = ⌊logCenter (13537 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13537 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13537 : Reach 13537 134003051850198 169587507679 := by
  have hr := row_13537
  have hl := log_bounds hr.1
    (by change logScale (13537 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13523) (T := 133907920030670) (U := 169574979976)
    (by norm_num) (by norm_num) hr.1 gap_13537
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13523

theorem gap_13553 : PrimeGap 13537 13553 :=
  (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 29, 2, 3, 2, 19, 2, 17, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_13553 :
    (13553 : ℕ).Prime ∧ logScale (13553 : ℚ) = 13 ∧
      (95143632006 : ℤ) = ⌊logCenter (13553 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (13553 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_13553 : Reach 13553 134098195482204 169600021516 := by
  have hr := row_13553
  have hl := log_bounds hr.1
    (by change logScale (13553 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 13537) (T := 134003051850198) (U := 169587507679)
    (by norm_num) (by norm_num) hr.1 gap_13553
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_13537

#print axioms reach_13553

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
