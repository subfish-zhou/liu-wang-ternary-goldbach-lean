import LiuWang.Proof.MajorArcApproximation.Error

/-! # 三次强展开误差进入实际 M1 积分 -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.MajorArcApproximation

def errorIntegral (N : ℕ) : ℝ :=
  ∑ i ∈ coreIndices N, ∫ eta in -deltaRadius N i.1..deltaRadius N i.1,
    cubicCost (Chebyshev.psi (N : ℝ)) (epsilon N i.2 i.1 eta)

theorem continuous_cubicCost_epsilon (N a q : ℕ) (B : ℝ) :
    Continuous (fun eta => cubicCost B (epsilon N a q eta)) := by
  unfold cubicCost
  exact (continuous_epsilon N a q).mul
    ((continuous_const.add (continuous_const.mul (continuous_epsilon N a q))).add
      ((continuous_epsilon N a q).pow 2))

theorem arc_error_integrable {N : ℕ} (hN : 0 < N) (a q : ℕ) (l r : ℝ) :
    IntervalIntegrable (fun eta =>
      (S N (rationalCenter a q + eta)^3 - model N a q eta^3) * arcPhase N a q eta)
      volume l r := by
  have hs : Continuous (fun eta => S N (rationalCenter a q + eta)^3 * arcPhase N a q eta) :=
    (ArcGeometry.continuous_circleKernel N).comp (continuous_const.add continuous_id)
  simpa only [sub_mul] using hs.intervalIntegrable l r |>.sub (model_cube_integrable hN a q l r)

theorem major_sub_model_eq {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    majorIntegral N - modelIntegral N =
      ∑ i ∈ coreIndices N, ∫ eta in -deltaRadius N i.1..deltaRadius N i.1,
        (S N (rationalCenter i.2 i.1 + eta)^3 - model N i.2 i.1 eta^3) *
          arcPhase N i.2 i.1 eta := by
  rw [majorIntegral_eq_sum hN, modelIntegral, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hs : Continuous (fun eta => S N (rationalCenter i.2 i.1 + eta)^3 *
      arcPhase N i.2 i.1 eta) :=
    (ArcGeometry.continuous_circleKernel N).comp (continuous_const.add continuous_id)
  rw [← intervalIntegral.integral_sub (hs.intervalIntegrable _ _)
    (model_cube_integrable (nat_pos_of_exp_le hN) _ _ _ _)]
  simp only [sub_mul]

theorem norm_major_sub_model_le_errorIntegral {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) :
    ‖majorIntegral N - modelIntegral N‖ ≤ errorIntegral N := by
  rw [major_sub_model_eq hN]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  have hh := (mem_coreIndices hN i).mp hi
  have hq0 := ArcGeometry.sourceIndex_den_pos hh.2
  have hq1 := hh.1.trans (sourceP_le_sourceP1 hN)
  let : NeZero i.1 := ⟨Nat.ne_of_gt hq0⟩
  have hd := deltaRadius_pos hN hq0
  apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
    (Filter.Eventually.of_forall (fun eta _ => ?_))
    ((continuous_cubicCost_epsilon N i.2 i.1 _).intervalIntegrable _ _)
  rw [norm_mul, norm_arcPhase, mul_one]
  apply norm_cube_sub_le (Chebyshev.psi_nonneg _) (epsilon_nonneg hN hh.2 hq1 eta)
    (norm_S_le_psi N _)
  rw [epsilon_eq]
  exact norm_S_sub_model hN hh.2 hq1 eta

theorem errorIntegral_le_uniform {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    errorIntegral N ≤ totalLength N * cubicCost (7 * (N : ℝ)) (uniformError N) := by
  have hpsi : Chebyshev.psi (N : ℝ) ≤ 7 * (N : ℝ) := by
    apply (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg N)).trans
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg N)
  unfold errorIntegral totalLength
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hh := (mem_coreIndices hN i).mp hi
  have hd := deltaRadius_pos hN (ArcGeometry.sourceIndex_den_pos hh.2)
  calc
    _ ≤ ∫ _eta in -deltaRadius N i.1..deltaRadius N i.1,
        cubicCost (7 * (N : ℝ)) (uniformError N) := by
      apply intervalIntegral.integral_mono_on (by linarith)
        ((continuous_cubicCost_epsilon N i.2 i.1 _).intervalIntegrable _ _)
        intervalIntegrable_const
      intro eta heta
      apply cubicCost_mono (Chebyshev.psi_nonneg _)
        (epsilon_nonneg hN hh.2 (hh.1.trans (sourceP_le_sourceP1 hN)) eta) hpsi
      exact epsilon_le_core hN hh.2 hh.1 (abs_le.mpr heta)
    _ = _ := by simp only [intervalIntegral.integral_const, smul_eq_mul]; ring

theorem uniform_cubicCost_le {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    cubicCost (7 * (N : ℝ)) (uniformError N) ≤ 3380 * (N : ℝ)^3 / sourceL N^10 := by
  have he0 := uniformError_nonneg N
  have he := uniformError_le_N hN
  have hn := natCast_pos_of_exp_le hN
  calc
    _ ≤ uniformError N * (3*(7*(N : ℝ))^2 + 3*(7*(N : ℝ))*(N : ℝ) + (N : ℝ)^2) := by
      unfold cubicCost
      gcongr
    _ = _ := by unfold uniformError; ring

theorem errorIntegral_le_log_power {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    errorIntegral N ≤ 6760 * (N : ℝ)^2 / sourceL N^4 := by
  have hL := sourceL_pos hN
  have hn := natCast_pos_of_exp_le hN
  apply (errorIntegral_le_uniform hN).trans
  calc
    _ ≤ (2 * sourceP N^2 / (N : ℝ)) * (3380 * (N : ℝ)^3 / sourceL N^10) :=
      mul_le_mul (totalLength_le hN) (uniform_cubicCost_le hN)
        (cubicCost_nonneg (by positivity) (uniformError_nonneg N)) (by positivity)
    _ = _ := by
      unfold sourceP
      field_simp
      ring

theorem norm_major_sub_model_le_log_power {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) :
    ‖majorIntegral N - modelIntegral N‖ ≤ 6760 * (N : ℝ)^2 / sourceL N^4 :=
  (norm_major_sub_model_le_errorIntegral hN).trans (errorIntegral_le_log_power hN)

theorem log_power_le_decimal {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    6760 * (N : ℝ)^2 / sourceL N^4 ≤ 0.000000001 * (N : ℝ)^2 := by
  have hL := sourceL_pos hN
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2000) (sourceL_ge_2000 hN) 4
  have hc : (6760 : ℝ) ≤ 0.000000001 * sourceL N^4 := by norm_num at hp; linarith
  apply (div_le_iff₀ (pow_pos hL 4)).mpr
  nlinarith [mul_nonneg (sq_nonneg (N : ℝ)) (sub_nonneg.mpr hc)]

theorem norm_major_sub_model_le_decimal {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) :
    ‖majorIntegral N - modelIntegral N‖ ≤ 0.000000001 * (N : ℝ)^2 :=
  (norm_major_sub_model_le_log_power hN).trans (log_power_le_decimal hN)

end LiuWang.Proof.MajorArcApproximation
