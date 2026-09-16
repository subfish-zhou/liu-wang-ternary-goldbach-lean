import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0300
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_7321 : PrimeGap 7309 7321 :=
  (primeGap_of_factors (ds := [2, 3, 2, 71, 2, 5, 2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7321 :
    (7321 : ℕ).Prime ∧ logScale (7321 : ℚ) = 12 ∧
      (88985022065 : ℤ) = ⌊logCenter (7321 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7321 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7321 : Reach 7321 72133486971437 158684858340 := by
  have hr := row_7321
  have hl := log_bounds hr.1
    (by change logScale (7321 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7309) (T := 72044501949372) (U := 158663183041)
    (by norm_num) (by norm_num) hr.1 gap_7321
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7309

theorem gap_7331 : PrimeGap 7321 7331 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 17, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7331 :
    (7331 : ℕ).Prime ∧ logScale (7331 : ℚ) = 12 ∧
      (88998672081 : ℤ) = ⌊logCenter (7331 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7331 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7331 : Reach 7331 72222485643518 158706507025 := by
  have hr := row_7331
  have hl := log_bounds hr.1
    (by change logScale (7331 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7321) (T := 72133486971437) (U := 158684858340)
    (by norm_num) (by norm_num) hr.1 gap_7331
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7321

theorem gap_7333 : PrimeGap 7331 7333 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_7333 :
    (7333 : ℕ).Prime ∧ logScale (7333 : ℚ) = 12 ∧
      (89001399849 : ℤ) = ⌊logCenter (7333 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7333 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7333 : Reach 7333 72311487043367 158728152758 := by
  have hr := row_7333
  have hl := log_bounds hr.1
    (by change logScale (7333 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7331) (T := 72222485643518) (U := 158706507025)
    (by norm_num) (by norm_num) hr.1 gap_7333
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7331

theorem gap_7349 : PrimeGap 7333 7349 :=
  (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 41, 2, 3, 2, 7, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7349 :
    (7349 : ℕ).Prime ∧ logScale (7349 : ℚ) = 12 ∧
      (89023195254 : ℤ) = ⌊logCenter (7349 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7349 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7349 : Reach 7349 72400510238621 158749754304 := by
  have hr := row_7349
  have hl := log_bounds hr.1
    (by change logScale (7349 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7333) (T := 72311487043367) (U := 158728152758)
    (by norm_num) (by norm_num) hr.1 gap_7349
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7333

theorem gap_7351 : PrimeGap 7349 7351 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_7351 :
    (7351 : ℕ).Prime ∧ logScale (7351 : ℚ) = 12 ∧
      (89025916342 : ℤ) = ⌊logCenter (7351 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7351 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7351 : Reach 7351 72489536154963 158771352911 := by
  have hr := row_7351
  have hl := log_bounds hr.1
    (by change logScale (7351 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7349) (T := 72400510238621) (U := 158749754304)
    (by norm_num) (by norm_num) hr.1 gap_7351
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7349

theorem gap_7369 : PrimeGap 7351 7369 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2, 37, 2, 3, 2, 53, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7369 :
    (7369 : ℕ).Prime ∧ logScale (7369 : ℚ) = 12 ∧
      (89050372876 : ℤ) = ⌊logCenter (7369 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7369 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7369 : Reach 7369 72578586527839 158792901684 := by
  have hr := row_7369
  have hl := log_bounds hr.1
    (by change logScale (7369 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7351) (T := 72489536154963) (U := 158771352911)
    (by norm_num) (by norm_num) hr.1 gap_7369
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7351

theorem gap_7393 : PrimeGap 7369 7393 :=
  (primeGap_of_factors (ds := [2, 3, 2, 73, 2, 5, 2, 3, 2, 47, 2, 11, 2, 3, 2, 5, 2, 83, 2, 3, 2, 19, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7393 :
    (7393 : ℕ).Prime ∧ logScale (7393 : ℚ) = 12 ∧
      (89082888824 : ℤ) = ⌊logCenter (7393 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7393 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7393 : Reach 7393 72667669416663 158814383408 := by
  have hr := row_7393
  have hl := log_bounds hr.1
    (by change logScale (7393 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7369) (T := 72578586527839) (U := 158792901684)
    (by norm_num) (by norm_num) hr.1 gap_7393
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7369

theorem gap_7411 : PrimeGap 7393 7411 :=
  (primeGap_of_factors (ds := [2, 3, 2, 13, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 31, 2]) (by decide +kernel) (by decide +kernel))

theorem row_7411 :
    (7411 : ℕ).Prime ∧ logScale (7411 : ℚ) = 12 ∧
      (89107206588 : ℤ) = ⌊logCenter (7411 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (7411 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_7411 : Reach 7411 72756776623251 158835815849 := by
  have hr := row_7411
  have hl := log_bounds hr.1
    (by change logScale (7411 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 7393) (T := 72667669416663) (U := 158814383408)
    (by norm_num) (by norm_num) hr.1 gap_7411
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_7393

#print axioms reach_7411

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
