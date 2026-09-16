import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0240

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_6047 :
    (6047 : ℕ).Prime ∧ logScale (6047 : ℚ) = 12 ∧
      (87073175571 : ℤ) = ⌊logCenter (6047 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6047 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6047 : Reach 6047 59455234545493 155286882863 := by
  have hr := row_6047
  have hl := log_bounds hr.1
    (by change logScale (6047 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6043) (T := 59368161369922) (U := 155261202875)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6043

theorem row_6053 :
    (6053 : ℕ).Prime ∧ logScale (6053 : ℚ) = 12 ∧
      (87083092927 : ℤ) = ⌊logCenter (6053 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6053 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6053 : Reach 6053 59542317638420 155312541635 := by
  have hr := row_6053
  have hl := log_bounds hr.1
    (by change logScale (6053 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6047) (T := 59455234545493) (U := 155286882863)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6047

theorem row_6067 :
    (6067 : ℕ).Prime ∧ logScale (6067 : ℚ) = 12 ∧
      (87106195248 : ℤ) = ⌊logCenter (6067 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6067 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6067 : Reach 6067 59629423833668 155338145418 := by
  have hr := row_6067
  have hl := log_bounds hr.1
    (by change logScale (6067 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6053) (T := 59542317638420) (U := 155312541635)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6053

theorem row_6073 :
    (6073 : ℕ).Prime ∧ logScale (6073 : ℚ) = 12 ∧
      (87116079927 : ℤ) = ⌊logCenter (6073 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6073 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6073 : Reach 6073 59716539913595 155363728117 := by
  have hr := row_6073
  have hl := log_bounds hr.1
    (by change logScale (6073 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6067) (T := 59629423833668) (U := 155338145418)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6067

theorem row_6079 :
    (6079 : ℕ).Prime ∧ logScale (6079 : ℚ) = 12 ∧
      (87125954846 : ℤ) = ⌊logCenter (6079 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6079 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6079 : Reach 6079 59803665868441 155389289771 := by
  have hr := row_6079
  have hl := log_bounds hr.1
    (by change logScale (6079 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6073) (T := 59716539913595) (U := 155363728117)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6073

theorem row_6089 :
    (6089 : ℕ).Prime ∧ logScale (6089 : ℚ) = 12 ∧
      (87142391404 : ℤ) = ⌊logCenter (6089 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6089 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6089 : Reach 6089 59890808259845 155414813636 := by
  have hr := row_6089
  have hl := log_bounds hr.1
    (by change logScale (6089 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6079) (T := 59803665868441) (U := 155389289771)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6079

theorem row_6091 :
    (6091 : ℕ).Prime ∧ logScale (6091 : ℚ) = 12 ∧
      (87145675477 : ℤ) = ⌊logCenter (6091 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6091 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6091 : Reach 6091 59977953935322 155440333310 := by
  have hr := row_6091
  have hl := log_bounds hr.1
    (by change logScale (6091 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6089) (T := 59890808259845) (U := 155414813636)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6089

theorem row_6101 :
    (6101 : ℕ).Prime ∧ logScale (6101 : ℚ) = 12 ∧
      (87162079680 : ℤ) = ⌊logCenter (6101 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (6101 : ℚ) = 12 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_6101 : Reach 6101 60065116015002 155465815332 := by
  have hr := row_6101
  have hl := log_bounds hr.1
    (by change logScale (6101 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 6091) (T := 59977953935322) (U := 155440333310)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_6091

#print axioms reach_6101

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
