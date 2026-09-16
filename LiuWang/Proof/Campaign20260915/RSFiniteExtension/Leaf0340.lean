import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block033
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_8117 : PrimeGap 8111 8117 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8117 :
    (8117 : ℕ).Prime ∧ logScale (8117 : ℚ) = 12 ∧
      (90017159036 : ℤ) = ⌊logCenter (8117 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8117 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8117 : Reach 8117 80010875173884 160504925224 := by
  have hr := row_8117
  have hl := log_bounds hr.1
    (by change logScale (8117 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 8111) (T := 79920858014848) (U := 160485151301)
    (by norm_num) (by norm_num) hr.1 gap_8117
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8111

theorem gap_8123 : PrimeGap 8117 8123 :=
  (primeGap_of_factors (ds := [2, 23, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8123 :
    (8123 : ℕ).Prime ∧ logScale (8123 : ℚ) = 12 ∧
      (90024548199 : ℤ) = ⌊logCenter (8123 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8123 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8123 : Reach 8123 80100899722083 160524686973 := by
  have hr := row_8123
  have hl := log_bounds hr.1
    (by change logScale (8123 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 8117) (T := 80010875173884) (U := 160504925224)
    (by norm_num) (by norm_num) hr.1 gap_8123
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8117

theorem gap_8147 : PrimeGap 8123 8147 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 11, 2, 47, 2, 3, 2, 5, 2, 79, 2, 3, 2, 7, 2, 17, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8147 :
    (8147 : ℕ).Prime ∧ logScale (8147 : ℚ) = 12 ∧
      (90054050371 : ℤ) = ⌊logCenter (8147 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8147 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8147 : Reach 8147 80190953772454 160544392926 := by
  have hr := row_8147
  have hl := log_bounds hr.1
    (by change logScale (8147 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 8123) (T := 80100899722083) (U := 160524686973)
    (by norm_num) (by norm_num) hr.1 gap_8147
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8123

theorem gap_8161 : PrimeGap 8147 8161 :=
  (primeGap_of_factors (ds := [2, 29, 2, 3, 2, 31, 2, 5, 2, 3, 2, 41, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8161 :
    (8161 : ℕ).Prime ∧ logScale (8161 : ℚ) = 12 ∧
      (90071219863 : ℤ) = ⌊logCenter (8161 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8161 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8161 : Reach 8161 80281024992317 160564067484 := by
  have hr := row_8161
  have hl := log_bounds hr.1
    (by change logScale (8161 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 8147) (T := 80190953772454) (U := 160544392926)
    (by norm_num) (by norm_num) hr.1 gap_8161
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8147

theorem gap_8167 : PrimeGap 8161 8167 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8167 :
    (8167 : ℕ).Prime ∧ logScale (8167 : ℚ) = 12 ∧
      (90078569202 : ℤ) = ⌊logCenter (8167 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8167 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8167 : Reach 8167 80371103561519 160583729996 := by
  have hr := row_8167
  have hl := log_bounds hr.1
    (by change logScale (8167 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 8161) (T := 80281024992317) (U := 160564067484)
    (by norm_num) (by norm_num) hr.1 gap_8167
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8161

theorem gap_8171 : PrimeGap 8167 8171 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8171 :
    (8171 : ℕ).Prime ∧ logScale (8171 : ℚ) = 12 ∧
      (90083465762 : ℤ) = ⌊logCenter (8171 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8171 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8171 : Reach 8171 80461187027281 160603385288 := by
  have hr := row_8171
  have hl := log_bounds hr.1
    (by change logScale (8171 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 8167) (T := 80371103561519) (U := 160583729996)
    (by norm_num) (by norm_num) hr.1 gap_8171
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8167

theorem gap_8179 : PrimeGap 8171 8179 :=
  (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8179 :
    (8179 : ℕ).Prime ∧ logScale (8179 : ℚ) = 12 ∧
      (90093251696 : ℤ) = ⌊logCenter (8179 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8179 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8179 : Reach 8179 80551280278977 160623023756 := by
  have hr := row_8179
  have hl := log_bounds hr.1
    (by change logScale (8179 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 8171) (T := 80461187027281) (U := 160603385288)
    (by norm_num) (by norm_num) hr.1 gap_8179
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8171

theorem gap_8191 : PrimeGap 8179 8191 :=
  (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 5, 2, 3, 2, 19, 2]) (by decide +kernel) (by decide +kernel))

theorem row_8191 :
    (8191 : ℕ).Prime ∧ logScale (8191 : ℚ) = 12 ∧
      (90107912663 : ℤ) = ⌊logCenter (8191 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (8191 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_8191 : Reach 8191 80641388191640 160642635847 := by
  have hr := row_8191
  have hl := log_bounds hr.1
    (by change logScale (8191 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 8179) (T := 80551280278977) (U := 160623023756)
    (by norm_num) (by norm_num) hr.1 gap_8191
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_8179

#print axioms reach_8191

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
