import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block008

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem row_2909 :
    (2909 : ℕ).Prime ∧ logScale (2909 : ℚ) = 11 ∧
      (79755646556 : ℤ) = ⌊logCenter (2909 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2909 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2909 : Reach 2909 28604382084360 142492304138 := by
  have hr := row_2909
  have hl := log_bounds hr.1
    (by change logScale (2909 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2903) (T := 28524626437804) (U := 142443320877)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2903

theorem row_2917 :
    (2917 : ℕ).Prime ∧ logScale (2917 : ℚ) = 11 ∧
      (79783109670 : ℤ) = ⌊logCenter (2917 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2917 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2917 : Reach 2917 28684165194030 142541169812 := by
  have hr := row_2917
  have hl := log_bounds hr.1
    (by change logScale (2917 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2909) (T := 28604382084360) (U := 142492304138)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2909

theorem row_2927 :
    (2927 : ℕ).Prime ∧ logScale (2927 : ℚ) = 11 ∧
      (79817332838 : ℤ) = ⌊logCenter (2927 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2927 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2927 : Reach 2927 28763982526868 142589885182 := by
  have hr := row_2927
  have hl := log_bounds hr.1
    (by change logScale (2927 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2917) (T := 28684165194030) (U := 142541169812)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2917

theorem row_2939 :
    (2939 : ℕ).Prime ∧ logScale (2939 : ℚ) = 11 ∧
      (79858246635 : ℤ) = ⌊logCenter (2939 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2939 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2939 : Reach 2939 28843840773503 142638418159 := by
  have hr := row_2939
  have hl := log_bounds hr.1
    (by change logScale (2939 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2927) (T := 28763982526868) (U := 142589885182)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2927

theorem row_2953 :
    (2953 : ℕ).Prime ∧ logScale (2953 : ℚ) = 11 ∧
      (79905768788 : ℤ) = ⌊logCenter (2953 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2953 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2953 : Reach 2953 28923746542291 142686737407 := by
  have hr := row_2953
  have hl := log_bounds hr.1
    (by change logScale (2953 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2939) (T := 28843840773503) (U := 142638418159)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2939

theorem row_2957 :
    (2957 : ℕ).Prime ∧ logScale (2957 : ℚ) = 11 ∧
      (79919305169 : ℤ) = ⌊logCenter (2957 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2957 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2957 : Reach 2957 29003665847460 142735007616 := by
  have hr := row_2957
  have hl := log_bounds hr.1
    (by change logScale (2957 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2953) (T := 28923746542291) (U := 142686737407)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2953

theorem row_2963 :
    (2963 : ℕ).Prime ∧ logScale (2963 : ℚ) = 11 ∧
      (79939575447 : ℤ) = ⌊logCenter (2963 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2963 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2963 : Reach 2963 29083605422907 142783196343 := by
  have hr := row_2963
  have hl := log_bounds hr.1
    (by change logScale (2963 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2957) (T := 29003665847460) (U := 142735007616)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2957

theorem row_2969 :
    (2969 : ℕ).Prime ∧ logScale (2969 : ℚ) = 11 ∧
      (79959804719 : ℤ) = ⌊logCenter (2969 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2969 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2969 : Reach 2969 29163565227626 142831303889 := by
  have hr := row_2969
  have hl := log_bounds hr.1
    (by change logScale (2969 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2963) (T := 29083605422907) (U := 142783196343)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2963

#print axioms reach_2969

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
