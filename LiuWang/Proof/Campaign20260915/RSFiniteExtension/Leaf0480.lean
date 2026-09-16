import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block047
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_11213 : PrimeGap 11197 11213 :=
  (primeGap_of_factors (ds := [2, 3, 2, 23, 2, 17, 2, 3, 2, 7, 2, 11, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11213 :
    (11213 : ℕ).Prime ∧ logScale (11213 : ℚ) = 13 ∧
      (93248290950 : ℤ) = ⌊logCenter (11213 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11213 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11213 : Reach 11213 110822896031564 166242780133 := by
  have hr := row_11213
  have hl := log_bounds hr.1
    (by change logScale (11213 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11197) (T := 110729647740614) (U := 166227954236)
    (by norm_num) (by norm_num) hr.1 gap_11213
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11197

theorem gap_11239 : PrimeGap 11213 11239 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 103, 2, 3, 2, 11, 2, 47, 2, 3, 2, 17, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11239 :
    (11239 : ℕ).Prime ∧ logScale (11239 : ℚ) = 13 ∧
      (93271451481 : ℤ) = ⌊logCenter (11239 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11239 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11239 : Reach 11239 110916167483045 166257573049 := by
  have hr := row_11239
  have hl := log_bounds hr.1
    (by change logScale (11239 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11213) (T := 110822896031564) (U := 166242780133)
    (by norm_num) (by norm_num) hr.1 gap_11239
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11213

theorem gap_11243 : PrimeGap 11239 11243 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11243 :
    (11243 : ℕ).Prime ∧ logScale (11243 : ℚ) = 13 ∧
      (93275009883 : ℤ) = ⌊logCenter (11243 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11243 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11243 : Reach 11243 111009442492928 166272362017 := by
  have hr := row_11243
  have hl := log_bounds hr.1
    (by change logScale (11243 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11239) (T := 110916167483045) (U := 166257573049)
    (by norm_num) (by norm_num) hr.1 gap_11243
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11239

theorem gap_11251 : PrimeGap 11243 11251 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11251 :
    (11251 : ℕ).Prime ∧ logScale (11251 : ℚ) = 13 ∧
      (93282122891 : ℤ) = ⌊logCenter (11251 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11251 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11251 : Reach 11251 111102724615819 166287141783 := by
  have hr := row_11251
  have hl := log_bounds hr.1
    (by change logScale (11251 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11243) (T := 111009442492928) (U := 166272362017)
    (by norm_num) (by norm_num) hr.1 gap_11251
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11243

theorem gap_11257 : PrimeGap 11251 11257 :=
  (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11257 :
    (11257 : ℕ).Prime ∧ logScale (11257 : ℚ) = 13 ∧
      (93287454329 : ℤ) = ⌊logCenter (11257 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11257 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11257 : Reach 11257 111196012070148 166301914984 := by
  have hr := row_11257
  have hl := log_bounds hr.1
    (by change logScale (11257 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11251) (T := 111102724615819) (U := 166287141783)
    (by norm_num) (by norm_num) hr.1 gap_11257
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11251

theorem gap_11261 : PrimeGap 11257 11261 :=
  (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11261 :
    (11261 : ℕ).Prime ∧ logScale (11261 : ℚ) = 13 ∧
      (93291007043 : ℤ) = ⌊logCenter (11261 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11261 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11261 : Reach 11261 111289303077191 166316684249 := by
  have hr := row_11261
  have hl := log_bounds hr.1
    (by change logScale (11261 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11257) (T := 111196012070148) (U := 166301914984)
    (by norm_num) (by norm_num) hr.1 gap_11261
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11257

theorem gap_11273 : PrimeGap 11261 11273 :=
  (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 19, 2, 59, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11273 :
    (11273 : ℕ).Prime ∧ logScale (11273 : ℚ) = 13 ∧
      (93301657616 : ℤ) = ⌊logCenter (11273 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11273 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11273 : Reach 11273 111382604734807 166331439101 := by
  have hr := row_11273
  have hl := log_bounds hr.1
    (by change logScale (11273 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11261) (T := 111289303077191) (U := 166316684249)
    (by norm_num) (by norm_num) hr.1 gap_11273
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11261

theorem gap_11279 : PrimeGap 11273 11279 :=
  (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel))

theorem row_11279 :
    (11279 : ℕ).Prime ∧ logScale (11279 : ℚ) = 13 ∧
      (93306978652 : ℤ) = ⌊logCenter (11279 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (11279 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_11279 : Reach 11279 111475911713459 166346187411 := by
  have hr := row_11279
  have hl := log_bounds hr.1
    (by change logScale (11279 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 11273) (T := 111382604734807) (U := 166331439101)
    (by norm_num) (by norm_num) hr.1 gap_11279
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_11273

#print axioms reach_11279

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
