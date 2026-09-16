import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0400
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_9467 : PrimeGap 9463 9467 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9467 :
    (9467 : ℕ).Prime ∧ logScale (9467 : ℚ) = 13 ∧
      (91555673427 : ℤ) = ⌊logCenter (9467 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9467 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9467 : Reach 9467 93817389044438 163302270314 := by
  have hr := row_9467
  have hl := log_bounds hr.1
    (by change logScale (9467 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9463) (T := 93725833371011) (U := 163285020681)
    (by norm_num) (by norm_num) hr.1 gap_9467
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9463

theorem gap_9473 : PrimeGap 9467 9473 :=
  (primeGap_of_factors (ds := [2, 17, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9473 :
    (9473 : ℕ).Prime ∧ logScale (9473 : ℚ) = 13 ∧
      (91562009224 : ℤ) = ⌊logCenter (9473 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9473 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9473 : Reach 9473 93908951053662 163319510841 := by
  have hr := row_9473
  have hl := log_bounds hr.1
    (by change logScale (9473 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9467) (T := 93817389044438) (U := 163302270314)
    (by norm_num) (by norm_num) hr.1 gap_9473
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9467

theorem gap_9479 : PrimeGap 9473 9479 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9479 :
    (9479 : ℕ).Prime ∧ logScale (9479 : ℚ) = 13 ∧
      (91568341010 : ℤ) = ⌊logCenter (9479 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9479 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9479 : Reach 9479 94000519394672 163336742273 := by
  have hr := row_9479
  have hl := log_bounds hr.1
    (by change logScale (9479 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9473) (T := 93908951053662) (U := 163319510841)
    (by norm_num) (by norm_num) hr.1 gap_9479
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9473

theorem gap_9491 : PrimeGap 9479 9491 :=
  (primeGap_of_factors (ds := [2, 19, 2, 3, 2, 5, 2, 53, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9491 :
    (9491 : ℕ).Prime ∧ logScale (9491 : ℚ) = 13 ∧
      (91580992567 : ℤ) = ⌊logCenter (9491 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9491 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9491 : Reach 9491 94092100387239 163353953732 := by
  have hr := row_9491
  have hl := log_bounds hr.1
    (by change logScale (9491 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9479) (T := 94000519394672) (U := 163336742273)
    (by norm_num) (by norm_num) hr.1 gap_9491
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9479

theorem gap_9497 : PrimeGap 9491 9497 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9497 :
    (9497 : ℕ).Prime ∧ logScale (9497 : ℚ) = 13 ∧
      (91587312348 : ℤ) = ⌊logCenter (9497 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9497 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9497 : Reach 9497 94183687699587 163371156129 := by
  have hr := row_9497
  have hl := log_bounds hr.1
    (by change logScale (9497 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9491) (T := 94092100387239) (U := 163353953732)
    (by norm_num) (by norm_num) hr.1 gap_9497
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9491

theorem gap_9511 : PrimeGap 9497 9511 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 37, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9511 :
    (9511 : ℕ).Prime ∧ logScale (9511 : ℚ) = 13 ∧
      (91602042991 : ℤ) = ⌊logCenter (9511 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9511 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9511 : Reach 9511 94275289742578 163388335010 := by
  have hr := row_9511
  have hl := log_bounds hr.1
    (by change logScale (9511 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9497) (T := 94183687699587) (U := 163371156129)
    (by norm_num) (by norm_num) hr.1 gap_9511
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9497

theorem gap_9521 : PrimeGap 9511 9521 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 31, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9521 :
    (9521 : ℕ).Prime ∧ logScale (9521 : ℚ) = 13 ∧
      (91612551609 : ℤ) = ⌊logCenter (9521 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9521 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9521 : Reach 9521 94366902294187 163405497651 := by
  have hr := row_9521
  have hl := log_bounds hr.1
    (by change logScale (9521 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9511) (T := 94275289742578) (U := 163388335010)
    (by norm_num) (by norm_num) hr.1 gap_9521
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9511

theorem gap_9533 : PrimeGap 9521 9533 :=
  (primeGap_of_factors (ds := [2, 89, 2, 3, 2, 7, 2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_9533 :
    (9533 : ℕ).Prime ∧ logScale (9533 : ℚ) = 13 ∧
      (91625147391 : ℤ) = ⌊logCenter (9533 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (9533 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_9533 : Reach 9533 94458527441578 163422640486 := by
  have hr := row_9533
  have hl := log_bounds hr.1
    (by change logScale (9533 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 9521) (T := 94366902294187) (U := 163405497651)
    (by norm_num) (by norm_num) hr.1 gap_9533
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_9521

#print axioms reach_9533

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
