import LiuWang.Proof.SingularIntegral.Main
import LiuWang.Proof.SingularIntegral.Conditions
import LiuWang.Proof.Parameters.Main

/-!
# 原有效域与实际 `J³` 消费者

`N ≥ exp 2000` 所需的正性由固定基线的参数生产者推出。
实部带条件不需要加强：主定理事实上适用于全部复参数。
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped Interval
open AnalyticNumberTheory.LargeSieve LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.SingularIntegral

theorem lemma4_1_2000 {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    (rho₁ rho₂ rho₃ : ℂ)
    (_h₁ : 0 < rho₁.re ∧ rho₁.re ≤ 1)
    (_h₂ : 0 < rho₂.re ∧ rho₂.re ≤ 1)
    (_h₃ : 0 < rho₃.re ∧ rho₃.re ≤ 1) :
    (∫ eta : ℝ, charReal (-(N : ℝ) * eta) *
      Jrho N rho₁ eta * Jrho N rho₂ eta * Jrho N rho₃ eta) =
      (N : ℂ) ^ 2 * (∫ x₁ in (0.001 : ℝ)..0.998,
        ∫ x₂ in (0.001 : ℝ)..(0.999 - x₁),
          (((N : ℝ) * x₁ : ℝ) : ℂ) ^ (rho₁ - 1) *
          (((N : ℝ) * x₂ : ℝ) : ℂ) ^ (rho₂ - 1) *
          (((N : ℝ) * (1 - x₁ - x₂) : ℝ) : ℂ) ^ (rho₃ - 1)) :=
  integral_Jrho_triple_eq_simplex (nat_pos_of_exp_le hN) rho₁ rho₂ rho₃

theorem integral_Jrho_triple_eq_sourceSimplex {N : ℕ} (hN : 0 < N)
    (rho₁ rho₂ rho₃ : ℂ) :
    (∫ eta : ℝ, charReal (-(N : ℝ) * eta) *
      Jrho N rho₁ eta * Jrho N rho₂ eta * Jrho N rho₃ eta) =
      (N : ℂ) ^ 2 * (∫ x in sourceSimplex,
          (((N : ℝ) * x.1 : ℝ) : ℂ) ^ (rho₁ - 1) *
          (((N : ℝ) * x.2 : ℝ) : ℂ) ^ (rho₂ - 1) *
          (((N : ℝ) * (1 - x.1 - x.2) : ℝ) : ℂ) ^ (rho₃ - 1)) := by
  rw [sourceSimplex_eq_triangle, integral_triangle_eq_iterated _
    (simplex_cpow_integrableOn N (Nat.cast_pos.mpr hN) rho₁ rho₂ rho₃)]
  exact integral_Jrho_triple_eq_simplex hN rho₁ rho₂ rho₃

theorem J_cube_integrable {N : ℕ} (hN : 0 < N) :
    Integrable (fun eta : ℝ => J N eta ^ 3 * charReal (-(N : ℝ) * eta)) := by
  have h := Jrho_triple_integrable hN 1 1 1
  simp only [Jrho_one_eq_J] at h
  convert h using 1
  ext eta
  ring

theorem integral_J_cube {N : ℕ} (hN : 0 < N) :
    (∫ eta : ℝ, J N eta ^ 3 * charReal (-(N : ℝ) * eta)) =
      (N : ℂ) ^ 2 * ((0.997 : ℂ) ^ 2 / 2) := by
  rw [← integral_J_triple hN]
  apply integral_congr_ae
  filter_upwards with eta
  ring

theorem integral_J_cube_2000 {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    (∫ eta : ℝ, J N eta ^ 3 * charReal (-(N : ℝ) * eta)) =
      (N : ℂ) ^ 2 * ((0.997 : ℂ) ^ 2 / 2) :=
  integral_J_cube (nat_pos_of_exp_le hN)

theorem J_cube_integrable_2000 {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    Integrable (fun eta : ℝ => J N eta ^ 3 * charReal (-(N : ℝ) * eta)) :=
  J_cube_integrable (nat_pos_of_exp_le hN)

example {N : ℕ} (hN : 0 < N) :
    (∫ eta : ℝ, charReal (-(N : ℝ) * eta) * J N eta * J N eta * J N eta) =
      (N : ℂ) ^ 2 * ((0.997 : ℂ) ^ 2 / 2) :=
  integral_J_triple hN

example : (volume sourceSimplex).toReal = (0.997 : ℝ) ^ 2 / 2 := by
  rw [sourceSimplex_volume, ENNReal.toReal_ofReal (by positivity)]

end LiuWang.Proof.SingularIntegral
