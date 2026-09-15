import LiuWang.Proof.MinorArcEnergy.Fourth

/-!
# 三片次弧共用一个能量账户

三片真实能量之和恰为并集能量，亦为整圆能量减去 M1 能量。
加权核接口的 M2/M3 点态界是明确的未付输入，不冒充无条件估计。
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LiuWang.Proof.MinorArcEnergy

open Interfaces Parameters ArcGeometry AnalyticNumberTheory.LargeSieve

theorem energy_fourArc {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    (∫ α in sourceDomain N, ‖S N α‖ ^ 2) =
      (∫ α in M1 N, ‖S N α‖ ^ 2) + (∫ α in M2 N, ‖S N α‖ ^ 2) +
      (∫ α in M3 N, ‖S N α‖ ^ 2) + (∫ α in M4 N, ‖S N α‖ ^ 2) := by
  have hc := (Complex.continuous_ofReal.comp (continuous_energy N)).integrableOn_Icc
    (μ := volume) (a := 1 / sourceQ N) (b := 1 + 1 / sourceQ N)
  have h := integral_fourArc hN hc
  simpa only [Function.comp_def, integral_complex_ofReal, Complex.add_re, Complex.ofReal_re] using
    congrArg Complex.re h

theorem minor_union_subset_source {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    (M2 N ∪ M3 N) ∪ M4 N ⊆ sourceDomain N :=
  Set.union_subset (Set.union_subset (M2_subset_sourceDomain hN)
    (M3_subset_sourceDomain hN)) Set.sdiff_subset

theorem minor_energy_eq_union {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    (∫ α in M2 N, ‖S N α‖ ^ 2) + (∫ α in M3 N, ‖S N α‖ ^ 2) +
      (∫ α in M4 N, ‖S N α‖ ^ 2) =
        ∫ α in (M2 N ∪ M3 N) ∪ M4 N, ‖S N α‖ ^ 2 := by
  have he := energy_integrableOn N (1 / sourceQ N) (1 + 1 / sourceQ N)
  have h₂ := he.mono_set (M2_subset_sourceDomain hN)
  have h₃ := he.mono_set (M3_subset_sourceDomain hN)
  have h₄ := he.mono_set (show M4 N ⊆ sourceDomain N from Set.sdiff_subset)
  have hd : Disjoint (M2 N ∪ M3 N) (M4 N) := by
    apply (disjoint_firstThree_M4 N).mono_left
    intro α hα
    rcases hα with h₂ | h₃
    · exact Or.inl (Or.inr h₂)
    · exact Or.inr h₃
  rw [setIntegral_union hd (measurableSet_M4 N) (h₂.union h₃) h₄,
    setIntegral_union (disjoint_M2_M3 hN) (measurableSet_M3 N) h₂ h₃]

theorem minor_energy_eq_source_sub_major {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) :
    (∫ α in M2 N, ‖S N α‖ ^ 2) + (∫ α in M3 N, ‖S N α‖ ^ 2) +
      (∫ α in M4 N, ‖S N α‖ ^ 2) =
        (∫ α in sourceDomain N, ‖S N α‖ ^ 2) -
          (∫ α in M1 N, ‖S N α‖ ^ 2) := by
  linarith [energy_fourArc hN]

theorem minor_energy_le_source {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    (∫ α in M2 N, ‖S N α‖ ^ 2) + (∫ α in M3 N, ‖S N α‖ ^ 2) +
      (∫ α in M4 N, ‖S N α‖ ^ 2) ≤
        ∫ α in sourceDomain N, ‖S N α‖ ^ 2 := by
  rw [minor_energy_eq_union hN]
  exact set_energy_le_source N (minor_union_subset_source hN)

theorem minor_energy_le_window {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    (∫ α in M2 N, ‖S N α‖ ^ 2) + (∫ α in M3 N, ‖S N α‖ ^ 2) +
      (∫ α in M4 N, ‖S N α‖ ^ 2) ≤
        ∑ n ∈ windowFinset N, ArithmeticFunction.vonMangoldt n ^ 2 := by
  simpa only [source_energy_eq] using minor_energy_le_source hN

theorem minor_energy_le_sharp {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∫ α in M2 N, ‖S N α‖ ^ 2) + (∫ α in M3 N, ‖S N α‖ ^ 2) +
      (∫ α in M4 N, ‖S N α‖ ^ 2) ≤
        1.0012 * (N : ℝ) * Real.log N :=
  (minor_energy_le_source (exp_2000_le_of_exp_3100_le hN)).trans
    (source_energy_le_sharp hN)

theorem minor_integrals_le_weighted_energy {N : ℕ} {B₂ B₃ B₄ : ℝ}
    (hN : Real.exp 2000 ≤ (N : ℝ))
    (h₂ : ∀ α ∈ M2 N, ‖S N α‖ ≤ B₂)
    (h₃ : ∀ α ∈ M3 N, ‖S N α‖ ≤ B₃)
    (h₄ : ∀ α ∈ M4 N, ‖S N α‖ ≤ B₄) :
    ‖∫ α in M2 N, S N α ^ 3 * charReal (-(N : ℝ) * α)‖ +
      ‖∫ α in M3 N, S N α ^ 3 * charReal (-(N : ℝ) * α)‖ +
      ‖∫ α in M4 N, S N α ^ 3 * charReal (-(N : ℝ) * α)‖ ≤
        B₂ * (∫ α in M2 N, ‖S N α‖ ^ 2) +
        B₃ * (∫ α in M3 N, ‖S N α‖ ^ 2) +
        B₄ * (∫ α in M4 N, ‖S N α‖ ^ 2) :=
  add_le_add (add_le_add
    (norm_setIntegral_le_local_energy N (measurableSet_M2 N)
      (M2_subset_sourceDomain hN) h₂)
    (norm_setIntegral_le_local_energy N (measurableSet_M3 N)
      (M3_subset_sourceDomain hN) h₃))
    (norm_setIntegral_le_local_energy N (measurableSet_M4 N) Set.sdiff_subset h₄)

theorem weighted_energy_le_single_budget {N : ℕ} {B₂ B₃ B₄ B : ℝ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hB : 0 ≤ B)
    (h₂ : B₂ ≤ B) (h₃ : B₃ ≤ B) (h₄ : B₄ ≤ B) :
    B₂ * (∫ α in M2 N, ‖S N α‖ ^ 2) +
      B₃ * (∫ α in M3 N, ‖S N α‖ ^ 2) +
      B₄ * (∫ α in M4 N, ‖S N α‖ ^ 2) ≤
        B * ∫ α in sourceDomain N, ‖S N α‖ ^ 2 := by
  calc
    _ ≤ B * (∫ α in M2 N, ‖S N α‖ ^ 2) +
        B * (∫ α in M3 N, ‖S N α‖ ^ 2) +
        B * (∫ α in M4 N, ‖S N α‖ ^ 2) :=
      add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right h₂ (set_energy_nonneg N _))
        (mul_le_mul_of_nonneg_right h₃ (set_energy_nonneg N _)))
        (mul_le_mul_of_nonneg_right h₄ (set_energy_nonneg N _))
    _ = B * ((∫ α in M2 N, ‖S N α‖ ^ 2) +
        (∫ α in M3 N, ‖S N α‖ ^ 2) + (∫ α in M4 N, ‖S N α‖ ^ 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (minor_energy_le_source hN) hB

theorem minor_integrals_le_max_single_budget {N : ℕ} {B₂ B₃ B₄ : ℝ}
    (hN : Real.exp 2000 ≤ (N : ℝ))
    (hB : 0 ≤ max B₂ (max B₃ B₄))
    (h₂ : ∀ α ∈ M2 N, ‖S N α‖ ≤ B₂)
    (h₃ : ∀ α ∈ M3 N, ‖S N α‖ ≤ B₃)
    (h₄ : ∀ α ∈ M4 N, ‖S N α‖ ≤ B₄) :
    ‖∫ α in M2 N, S N α ^ 3 * charReal (-(N : ℝ) * α)‖ +
      ‖∫ α in M3 N, S N α ^ 3 * charReal (-(N : ℝ) * α)‖ +
      ‖∫ α in M4 N, S N α ^ 3 * charReal (-(N : ℝ) * α)‖ ≤
        max B₂ (max B₃ B₄) * ∫ α in sourceDomain N, ‖S N α‖ ^ 2 :=
  (minor_integrals_le_weighted_energy hN h₂ h₃ h₄).trans
    (weighted_energy_le_single_budget hN hB (le_max_left _ _)
      ((le_max_left _ _).trans (le_max_right _ _))
      ((le_max_right _ _).trans (le_max_right _ _)))

theorem minor_integrals_le_weighted_repaid {N : ℕ} {B₂ B₃ : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (h₂ : ∀ α ∈ M2 N, ‖S N α‖ ≤ B₂)
    (h₃ : ∀ α ∈ M3 N, ‖S N α‖ ≤ B₃) :
    ‖∫ α in M2 N, S N α ^ 3 * charReal (-(N : ℝ) * α)‖ +
      ‖∫ α in M3 N, S N α ^ 3 * charReal (-(N : ℝ) * α)‖ +
      ‖∫ α in M4 N, S N α ^ 3 * charReal (-(N : ℝ) * α)‖ ≤
        B₂ * (∫ α in M2 N, ‖S N α‖ ^ 2) +
        B₃ * (∫ α in M3 N, ‖S N α‖ ^ 2) +
        VaughanRecovery.mother N 0.1741355 3.2354175 0.077006 *
          (∫ α in M4 N, ‖S N α‖ ^ 2) :=
  minor_integrals_le_weighted_energy (exp_2000_le_of_exp_3100_le hN) h₂ h₃
    (fun _ hα => VaughanRecovery.M4_le_repaid_mother hN hα)

end LiuWang.Proof.MinorArcEnergy
