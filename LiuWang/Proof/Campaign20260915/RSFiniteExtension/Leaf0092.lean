import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0091

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_3049 :
    (3049 : ℕ).Prime ∧ logScale (3049 : ℚ) = 11 ∧
      (80225689441 : ℤ) = ⌊logCenter (3049 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3049 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3049 : Reach 3049 29884637611888 143258146835 := by
  have hr := row_3049
  have hl := log_bounds hr.1
    (by change logScale (3049 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3041) (T := 29804411922447) (U := 143211161545)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3041

theorem row_3061 :
    (3061 : ℕ).Prime ∧ logScale (3061 : ℚ) = 11 ∧
      (80264969360 : ℤ) = ⌊logCenter (3061 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3061 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3061 : Reach 3061 29964902581248 143304963223 := by
  have hr := row_3061
  have hl := log_bounds hr.1
    (by change logScale (3061 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3049) (T := 29884637611888) (U := 143258146835)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3049

theorem row_3067 :
    (3067 : ℕ).Prime ∧ logScale (3067 : ℚ) = 11 ∧
      (80284551612 : ℤ) = ⌊logCenter (3067 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3067 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3067 : Reach 3067 30045187132860 143351703264 := by
  have hr := row_3067
  have hl := log_bounds hr.1
    (by change logScale (3067 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3061) (T := 29964902581248) (U := 143304963223)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3061

theorem row_3079 :
    (3079 : ℕ).Prime ∧ logScale (3079 : ℚ) = 11 ∧
      (80323601450 : ℤ) = ⌊logCenter (3079 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3079 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3079 : Reach 3079 30125510734310 143398276268 := by
  have hr := row_3079
  have hl := log_bounds hr.1
    (by change logScale (3079 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3067) (T := 30045187132860) (U := 143351703264)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3067

theorem row_3083 :
    (3083 : ℕ).Prime ∧ logScale (3083 : ℚ) = 11 ∧
      (80336584250 : ℤ) = ⌊logCenter (3083 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3083 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3083 : Reach 3083 30205847318560 143444803938 := by
  have hr := row_3083
  have hl := log_bounds hr.1
    (by change logScale (3083 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3079) (T := 30125510734310) (U := 143398276268)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3079

theorem row_3089 :
    (3089 : ℕ).Prime ∧ logScale (3089 : ℚ) = 11 ∧
      (80356026900 : ℤ) = ⌊logCenter (3089 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3089 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3089 : Reach 3089 30286203345460 143491256271 := by
  have hr := row_3089
  have hl := log_bounds hr.1
    (by change logScale (3089 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3083) (T := 30205847318560) (U := 143444803938)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3083

theorem row_3109 :
    (3109 : ℕ).Prime ∧ logScale (3109 : ℚ) = 11 ∧
      (80420564071 : ℤ) = ⌊logCenter (3109 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3109 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3109 : Reach 3109 30366623909531 143537424629 := by
  have hr := row_3109
  have hl := log_bounds hr.1
    (by change logScale (3109 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3089) (T := 30286203345460) (U := 143491256271)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3089

theorem row_3119 :
    (3119 : ℕ).Prime ∧ logScale (3119 : ℚ) = 11 ∧
      (80452677137 : ℤ) = ⌊logCenter (3119 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3119 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3119 : Reach 3119 30447076586668 143583459724 := by
  have hr := row_3119
  have hl := log_bounds hr.1
    (by change logScale (3119 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3109) (T := 30366623909531) (U := 143537424629)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3109

#print axioms reach_3119

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
