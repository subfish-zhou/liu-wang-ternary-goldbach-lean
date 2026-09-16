import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0320
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_7727 : PrimeGap 7723 7727 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7727 :
    (7727 : ℕ).Prime ∧ logScale (7727 : ℚ) = 12 ∧
      (89524759648 : ℤ) = ⌊logCenter (7727 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7727 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7727 : Reach 7727 76419237483131 159697774490 := by
  have hr := row_7727
  have hl := log_bounds hr.1
    (by change logScale (7727 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7723) (T := 76329712723483) (U := 159677106989)
    (by norm_num) (by norm_num) hr.1 gap_7727
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7723

theorem gap_7741 : PrimeGap 7727 7741 :=
  (primeGap_of_factors (ds := [2, 59, 2, 3, 2, 11, 2, 5, 2, 3, 2, 71, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7741 :
    (7741 : ℕ).Prime ∧ logScale (7741 : ℚ) = 12 ∧
      (89542861540 : ℤ) = ⌊logCenter (7741 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7741 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7741 : Reach 7741 76508780344671 159718407278 := by
  have hr := row_7741
  have hl := log_bounds hr.1
    (by change logScale (7741 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7727) (T := 76419237483131) (U := 159697774490)
    (by norm_num) (by norm_num) hr.1 gap_7741
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7727

theorem gap_7753 : PrimeGap 7741 7753 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 61, 2, 3, 2, 23, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7753 :
    (7753 : ℕ).Prime ∧ logScale (7753 : ℚ) = 12 ∧
      (89558351410 : ℤ) = ⌊logCenter (7753 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7753 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7753 : Reach 7753 76598338696081 159739010788 := by
  have hr := row_7753
  have hl := log_bounds hr.1
    (by change logScale (7753 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7741) (T := 76508780344671) (U := 159718407278)
    (by norm_num) (by norm_num) hr.1 gap_7753
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7741

theorem gap_7757 : PrimeGap 7753 7757 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7757 :
    (7757 : ℕ).Prime ∧ logScale (7757 : ℚ) = 12 ∧
      (89563509373 : ℤ) = ⌊logCenter (7757 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7757 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7757 : Reach 7757 76687902205454 159759606329 := by
  have hr := row_7757
  have hl := log_bounds hr.1
    (by change logScale (7757 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7753) (T := 76598338696081) (U := 159739010788)
    (by norm_num) (by norm_num) hr.1 gap_7757
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7753

theorem gap_7759 : PrimeGap 7757 7759 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_7759 :
    (7759 : ℕ).Prime ∧ logScale (7759 : ℚ) = 12 ∧
      (89566087357 : ℤ) = ⌊logCenter (7759 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7759 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7759 : Reach 7759 76777468292811 159780199215 := by
  have hr := row_7759
  have hl := log_bounds hr.1
    (by change logScale (7759 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7757) (T := 76687902205454) (U := 159759606329)
    (by norm_num) (by norm_num) hr.1 gap_7759
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7757

theorem gap_7789 : PrimeGap 7759 7789 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 19, 2, 3, 2, 5, 2, 7, 2, 3, 2, 31, 2, 43, 2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7789 :
    (7789 : ℕ).Prime ∧ logScale (7789 : ℚ) = 12 ∧
      (89604677577 : ℤ) = ⌊logCenter (7789 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7789 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7789 : Reach 7789 76867072970388 159800715420 := by
  have hr := row_7789
  have hl := log_bounds hr.1
    (by change logScale (7789 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7759) (T := 76777468292811) (U := 159780199215)
    (by norm_num) (by norm_num) hr.1 gap_7789
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7759

theorem gap_7793 : PrimeGap 7789 7793 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7793 :
    (7793 : ℕ).Prime ∧ logScale (7793 : ℚ) = 12 ∧
      (89609811707 : ℤ) = ⌊logCenter (7793 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7793 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7793 : Reach 7793 76956682782095 159821223726 := by
  have hr := row_7793
  have hl := log_bounds hr.1
    (by change logScale (7793 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7789) (T := 76867072970388) (U := 159800715420)
    (by norm_num) (by norm_num) hr.1 gap_7793
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7789

theorem gap_7817 : PrimeGap 7793 7817 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 11, 2, 29, 2, 3, 2, 5, 2, 37, 2, 3, 2, 73, 2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7817 :
    (7817 : ℕ).Prime ∧ logScale (7817 : ℚ) = 12 ∧
      (89640561250 : ℤ) = ⌊logCenter (7817 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7817 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7817 : Reach 7817 77046323343345 159841671682 := by
  have hr := row_7817
  have hl := log_bounds hr.1
    (by change logScale (7817 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7793) (T := 76956682782095) (U := 159821223726)
    (by norm_num) (by norm_num) hr.1 gap_7817
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7793

#print axioms reach_7817

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
