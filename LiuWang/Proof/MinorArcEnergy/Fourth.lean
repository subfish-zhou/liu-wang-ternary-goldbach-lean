import LiuWang.Proof.MinorArcEnergy.Energy
import LiuWang.Proof.VaughanRecovery.Consumer

/-! 实际第四弧积分：点态母界只乘一次真实二次能量。 -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LiuWang.Proof.MinorArcEnergy

open Interfaces Parameters ArcGeometry VaughanRecovery AnalyticNumberTheory.LargeSieve

theorem circleKernel_integrableOn (N : ℕ) {s : Set ℝ}
    (hs : s ⊆ sourceDomain N) :
    IntegrableOn (fun α : ℝ => S N α ^ 3 * charReal (-(N : ℝ) * α)) s :=
  (continuous_circleKernel N).integrableOn_Icc.mono_set hs

theorem norm_circleKernel (N : ℕ) (α : ℝ) :
    ‖S N α ^ 3 * charReal (-(N : ℝ) * α)‖ = ‖S N α‖ ^ 3 := by
  rw [norm_mul, norm_pow, VaughanTypeI.norm_charReal_eq_one, mul_one]

theorem norm_setIntegral_le_local_energy (N : ℕ) {s : Set ℝ} {B : ℝ}
    (hs : MeasurableSet s) (hsub : s ⊆ sourceDomain N)
    (hpoint : ∀ α ∈ s, ‖S N α‖ ≤ B) :
    ‖∫ α in s, S N α ^ 3 * charReal (-(N : ℝ) * α)‖ ≤
      B * ∫ α in s, ‖S N α‖ ^ 2 := by
  have hf := circleKernel_integrableOn N hsub
  have he := (energy_integrableOn N _ _).mono_set hsub
  calc
    _ ≤ ∫ α in s, ‖S N α ^ 3 * charReal (-(N : ℝ) * α)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ α in s, B * ‖S N α‖ ^ 2 := by
      apply setIntegral_mono_on hf.norm (he.const_mul B) hs
      intro α hα
      rw [norm_circleKernel]
      calc
        ‖S N α‖ ^ 3 = ‖S N α‖ * ‖S N α‖ ^ 2 := by ring
        _ ≤ B * ‖S N α‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hpoint α hα) (sq_nonneg _)
    _ = _ := integral_const_mul _ _

theorem norm_setIntegral_le_source_energy (N : ℕ) {s : Set ℝ} {B : ℝ}
    (hs : MeasurableSet s) (hsub : s ⊆ sourceDomain N) (hB : 0 ≤ B)
    (hpoint : ∀ α ∈ s, ‖S N α‖ ≤ B) :
    ‖∫ α in s, S N α ^ 3 * charReal (-(N : ℝ) * α)‖ ≤
      B * ∫ α in sourceDomain N, ‖S N α‖ ^ 2 :=
  (norm_setIntegral_le_local_energy N hs hsub hpoint).trans
    (mul_le_mul_of_nonneg_left (set_energy_le_source N hsub) hB)

theorem repaid_mother_nonneg {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    0 ≤ mother N 0.1741355 3.2354175 0.077006 := by
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  unfold mother middleRatio tailRatio
  positivity

theorem M4_integral_le_repaid_local_energy {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    ‖∫ α in M4 N, S N α ^ 3 * charReal (-(N : ℝ) * α)‖ ≤
      mother N 0.1741355 3.2354175 0.077006 *
        ∫ α in M4 N, ‖S N α‖ ^ 2 :=
  norm_setIntegral_le_local_energy N (measurableSet_M4 N) Set.sdiff_subset
    (fun _ hα => M4_le_repaid_mother hN hα)

theorem M4_integral_le_repaid_energy {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    ‖∫ α in M4 N, S N α ^ 3 * charReal (-(N : ℝ) * α)‖ ≤
      mother N 0.1741355 3.2354175 0.077006 *
        ∫ α in sourceDomain N, ‖S N α‖ ^ 2 :=
  (M4_integral_le_repaid_local_energy hN).trans
    (mul_le_mul_of_nonneg_left (set_energy_le_source N Set.sdiff_subset)
      (repaid_mother_nonneg hN))

theorem M4_integral_le_repaid_window {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    ‖∫ α in M4 N, S N α ^ 3 * charReal (-(N : ℝ) * α)‖ ≤
      mother N 0.1741355 3.2354175 0.077006 *
        ∑ n ∈ windowFinset N, ArithmeticFunction.vonMangoldt n ^ 2 := by
  simpa only [source_energy_eq] using M4_integral_le_repaid_energy hN

theorem M4_integral_le_repaid_explicit {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    ‖∫ α in M4 N, S N α ^ 3 * charReal (-(N : ℝ) * α)‖ ≤
      (0.1741355 * (N : ℝ) / sourceL N +
        3.2354175 * (N : ℝ) ^ ((4 : ℝ) / 5) * sourceL N ^ ((7 : ℝ) / 5) +
        0.077006 * (N : ℝ) ^ ((1 : ℝ) / 2) * sourceL N ^ ((11 : ℝ) / 2)) *
          ∑ n ∈ windowFinset N, ArithmeticFunction.vonMangoldt n ^ 2 := by
  have h := M4_integral_le_repaid_window hN
  rw [mother_eq (exp_2000_le_of_exp_3100_le hN)] at h
  simpa only [VaughanTypeIIBudget.termB, mul_assoc] using h

theorem M4_integral_le_1743_energy {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    ‖∫ α in M4 N, S N α ^ 3 * charReal (-(N : ℝ) * α)‖ ≤
      (0.1743 * (N : ℝ) / Real.log N) *
        ∫ α in sourceDomain N, ‖S N α‖ ^ 2 := by
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  exact norm_setIntegral_le_source_energy N (measurableSet_M4 N) Set.sdiff_subset
    (by change 0 ≤ 0.1743 * (N : ℝ) / sourceL N; positivity)
    (fun _ hα => M4_le_1743 hN hα)

theorem M4_integral_le_explicit {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    ‖∫ α in M4 N, S N α ^ 3 * charReal (-(N : ℝ) * α)‖ ≤
      0.17450916 * (N : ℝ) ^ 2 := by
  have hL : 0 < Real.log N := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  calc
    _ ≤ (0.1743 * (N : ℝ) / Real.log N) *
        ∫ α in sourceDomain N, ‖S N α‖ ^ 2 := M4_integral_le_1743_energy hN
    _ ≤ (0.1743 * (N : ℝ) / Real.log N) *
        (1.0012 * (N : ℝ) * Real.log N) :=
      mul_le_mul_of_nonneg_left (source_energy_le_sharp hN) (by positivity)
    _ = _ := by field_simp; ring

end LiuWang.Proof.MinorArcEnergy
