import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block018

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_4943 :
    (4943 : ℕ).Prime ∧ logScale (4943 : ℚ) = 12 ∧
      (85057277101 : ℤ) = ⌊logCenter (4943 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4943 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4943 : Reach 4943 48435987501354 151695205644 := by
  have hr := row_4943
  have hl := log_bounds hr.1
    (by change logScale (4943 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4937) (T := 48350930224253) (U := 151664516749)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4937

theorem row_4951 :
    (4951 : ℕ).Prime ∧ logScale (4951 : ℚ) = 12 ∧
      (85073448522 : ℤ) = ⌊logCenter (4951 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4951 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4951 : Reach 4951 48521060949876 151725851141 := by
  have hr := row_4951
  have hl := log_bounds hr.1
    (by change logScale (4951 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4943) (T := 48435987501354) (U := 151695205644)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4943

theorem row_4957 :
    (4957 : ℕ).Prime ∧ logScale (4957 : ℚ) = 12 ∧
      (85085559949 : ℤ) = ⌊logCenter (4957 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4957 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4957 : Reach 4957 48606146509825 151756465720 := by
  have hr := row_4957
  have hl := log_bounds hr.1
    (by change logScale (4957 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4951) (T := 48521060949876) (U := 151725851141)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4951

theorem row_4967 :
    (4967 : ℕ).Prime ∧ logScale (4967 : ℚ) = 12 ∧
      (85105713119 : ℤ) = ⌊logCenter (4967 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4967 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4967 : Reach 4967 48691252222944 151787024815 := by
  have hr := row_4967
  have hl := log_bounds hr.1
    (by change logScale (4967 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4957) (T := 48606146509825) (U := 151756465720)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4957

theorem row_4969 :
    (4969 : ℕ).Prime ∧ logScale (4969 : ℚ) = 12 ∧
      (85109738884 : ℤ) = ⌊logCenter (4969 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4969 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4969 : Reach 4969 48776361961828 151817577759 := by
  have hr := row_4969
  have hl := log_bounds hr.1
    (by change logScale (4969 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4967) (T := 48691252222944) (U := 151787024815)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4967

theorem row_4973 :
    (4973 : ℕ).Prime ∧ logScale (4973 : ℚ) = 12 ∧
      (85117785555 : ℤ) = ⌊logCenter (4973 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4973 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4973 : Reach 4973 48861479747383 151848112268 := by
  have hr := row_4973
  have hl := log_bounds hr.1
    (by change logScale (4973 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4969) (T := 48776361961828) (U := 151817577759)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4969

theorem row_4987 :
    (4987 : ℕ).Prime ∧ logScale (4987 : ℚ) = 12 ∧
      (85145898024 : ℤ) = ⌊logCenter (4987 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4987 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4987 : Reach 4987 48946625645407 151878567165 := by
  have hr := row_4987
  have hl := log_bounds hr.1
    (by change logScale (4987 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4973) (T := 48861479747383) (U := 151848112268)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4973

theorem row_4993 :
    (4993 : ℕ).Prime ∧ logScale (4993 : ℚ) = 12 ∧
      (85157922073 : ℤ) = ⌊logCenter (4993 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (4993 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_4993 : Reach 4993 49031783567480 151908991558 := by
  have hr := row_4993
  have hl := log_bounds hr.1
    (by change logScale (4993 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 4987) (T := 48946625645407) (U := 151878567165)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_4987

#print axioms reach_4993

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
