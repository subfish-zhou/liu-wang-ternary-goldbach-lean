import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block023

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_5953 :
    (5953 : ℕ).Prime ∧ logScale (5953 : ℚ) = 12 ∧
      (86916505700 : ℤ) = ⌊logCenter (5953 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5953 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5953 : Reach 5953 58759037663148 155080561253 := by
  have hr := row_5953
  have hl := log_bounds hr.1
    (by change logScale (5953 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5939) (T := 58672121157448) (U := 155054510427)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5939

theorem row_5981 :
    (5981 : ℕ).Prime ∧ logScale (5981 : ℚ) = 12 ∧
      (86963430539 : ℤ) = ⌊logCenter (5981 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5981 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5981 : Reach 5981 58846001093687 155106494458 := by
  have hr := row_5981
  have hl := log_bounds hr.1
    (by change logScale (5981 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5953) (T := 58759037663148) (U := 155080561253)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5953

theorem row_5987 :
    (5987 : ℕ).Prime ∧ logScale (5987 : ℚ) = 12 ∧
      (86973457278 : ℤ) = ⌊logCenter (5987 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (5987 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_5987 : Reach 5987 58932974550965 155132406001 := by
  have hr := row_5987
  have hl := log_bounds hr.1
    (by change logScale (5987 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5981) (T := 58846001093687) (U := 155106494458)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5981

theorem row_6007 :
    (6007 : ℕ).Prime ∧ logScale (6007 : ℚ) = 12 ∧
      (87006807317 : ℤ) = ⌊logCenter (6007 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6007 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6007 : Reach 6007 59019981358282 155158235573 := by
  have hr := row_6007
  have hl := log_bounds hr.1
    (by change logScale (6007 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 5987) (T := 58932974550965) (U := 155132406001)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_5987

theorem row_6011 :
    (6011 : ℕ).Prime ∧ logScale (6011 : ℚ) = 12 ∧
      (87013463999 : ℤ) = ⌊logCenter (6011 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6011 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6011 : Reach 6011 59106994822281 155184052252 := by
  have hr := row_6011
  have hl := log_bounds hr.1
    (by change logScale (6011 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6007) (T := 59019981358282) (U := 155158235573)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6007

theorem row_6029 :
    (6029 : ℕ).Prime ∧ logScale (6029 : ℚ) = 12 ∧
      (87043364353 : ℤ) = ⌊logCenter (6029 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6029 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6029 : Reach 6029 59194038186634 155209796123 := by
  have hr := row_6029
  have hl := log_bounds hr.1
    (by change logScale (6029 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6011) (T := 59106994822281) (U := 155184052252)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6011

theorem row_6037 :
    (6037 : ℕ).Prime ∧ logScale (6037 : ℚ) = 12 ∧
      (87056624756 : ℤ) = ⌊logCenter (6037 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6037 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6037 : Reach 6037 59281094811390 155235510139 := by
  have hr := row_6037
  have hl := log_bounds hr.1
    (by change logScale (6037 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6029) (T := 59194038186634) (U := 155209796123)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6029

theorem row_6043 :
    (6043 : ℕ).Prime ∧ logScale (6043 : ℚ) = 12 ∧
      (87066558532 : ℤ) = ⌊logCenter (6043 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6043 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6043 : Reach 6043 59368161369922 155261202875 := by
  have hr := row_6043
  have hl := log_bounds hr.1
    (by change logScale (6043 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6037) (T := 59281094811390) (U := 155235510139)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6037

#print axioms reach_6043

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
