import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block068
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_15973 : PrimeGap 15971 15973 :=
  (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel))

theorem row_15973 :
    (15973 : ℕ).Prime ∧ logScale (15973 : ℚ) = 13 ∧
      (96786550724 : ℤ) = ⌊logCenter (15973 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15973 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15973 : Reach 15973 158771126812918 172580378443 := by
  have hr := row_15973
  have hl := log_bounds hr.1
    (by change logScale (15973 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15971) (T := 158674340262194) (U := 172569573936)
    (by norm_num) (by norm_num) hr.1 gap_15973
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15971

theorem gap_15991 : PrimeGap 15973 15991 :=
  (primeGap_of_factors (ds := [2, 3, 2, 13, 2, 19, 2, 3, 2, 11, 2, 5, 2, 3, 2, 59, 2]) (by decide +kernel) (by decide +kernel))

theorem row_15991 :
    (15991 : ℕ).Prime ∧ logScale (15991 : ℚ) = 13 ∧
      (96797813395 : ℤ) = ⌊logCenter (15991 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (15991 : ℚ) = 13 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_15991 : Reach 15991 158867924626313 172591171463 := by
  have hr := row_15991
  have hl := log_bounds hr.1
    (by change logScale (15991 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact reach_next (a := 15973) (T := 158771126812918) (U := 172580378443)
    (by norm_num) (by norm_num) hr.1 gap_15991
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_15973

#print axioms reach_15991

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
