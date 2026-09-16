import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block013

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_3911 :
    (3911 : ℕ).Prime ∧ logScale (3911 : ℚ) = 11 ∧
      (82715483718 : ℤ) = ⌊logCenter (3911 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3911 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3911 : Reach 3911 38366338542854 147612224168 := by
  have hr := row_3911
  have hl := log_bounds hr.1
    (by change logScale (3911 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3907) (T := 38283623059136) (U := 147574481333)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3907

theorem row_3917 :
    (3917 : ℕ).Prime ∧ logScale (3917 : ℚ) = 11 ∧
      (82730813308 : ℤ) = ⌊logCenter (3917 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3917 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3917 : Reach 3917 38449069356162 147649918812 := by
  have hr := row_3917
  have hl := log_bounds hr.1
    (by change logScale (3917 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3911) (T := 38366338542854) (U := 147612224168)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3911

theorem row_3919 :
    (3919 : ℕ).Prime ∧ logScale (3919 : ℚ) = 11 ∧
      (82735917953 : ℤ) = ⌊logCenter (3919 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3919 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3919 : Reach 3919 38531805274115 147687603835 := by
  have hr := row_3919
  have hl := log_bounds hr.1
    (by change logScale (3919 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3917) (T := 38449069356162) (U := 147649918812)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3917

theorem row_3923 :
    (3923 : ℕ).Prime ∧ logScale (3923 : ℚ) = 11 ∧
      (82746119433 : ℤ) = ⌊logCenter (3923 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3923 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3923 : Reach 3923 38614551393548 147725260032 := by
  have hr := row_3923
  have hl := log_bounds hr.1
    (by change logScale (3923 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3919) (T := 38531805274115) (U := 147687603835)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3919

theorem row_3929 :
    (3929 : ℕ).Prime ∧ logScale (3929 : ℚ) = 11 ∧
      (82761402166 : ℤ) = ⌊logCenter (3929 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3929 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3929 : Reach 3929 38697312795714 147762868296 := by
  have hr := row_3929
  have hl := log_bounds hr.1
    (by change logScale (3929 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3923) (T := 38614551393548) (U := 147725260032)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3923

theorem row_3931 :
    (3931 : ℕ).Prime ∧ logScale (3931 : ℚ) = 11 ∧
      (82766491225 : ℤ) = ⌊logCenter (3931 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3931 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3931 : Reach 3931 38780079286939 147800466991 := by
  have hr := row_3931
  have hl := log_bounds hr.1
    (by change logScale (3931 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3929) (T := 38697312795714) (U := 147762868296)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3929

theorem row_3943 :
    (3943 : ℕ).Prime ∧ logScale (3943 : ℚ) = 11 ∧
      (82796971310 : ℤ) = ⌊logCenter (3943 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3943 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3943 : Reach 3943 38862876258249 147837960768 := by
  have hr := row_3943
  have hl := log_bounds hr.1
    (by change logScale (3943 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3931) (T := 38780079286939) (U := 147800466991)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3931

theorem row_3947 :
    (3947 : ℕ).Prime ∧ logScale (3947 : ℚ) = 11 ∧
      (82807110728 : ℤ) = ⌊logCenter (3947 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (3947 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_3947 : Reach 3947 38945683368977 147875426040 := by
  have hr := row_3947
  have hl := log_bounds hr.1
    (by change logScale (3947 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 3943) (T := 38862876258249) (U := 147837960768)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_3943

#print axioms reach_3947

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
