import LiuWang.Proof.NearOneDensity.DirichletKernel
import LiuWang.Proof.Interfaces.Main
import PrimeNumberTheoremAnd.Mathlib.Analysis.Meromorphic.DivisorSupport

set_option autoImplicit false
noncomputable section

open Classical
open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.NearOneDensity

theorem finite_entire_zeros_in_ball {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : f ≠ 0) (R : ℝ) :
    {z : ℂ | ‖z‖ ≤ R ∧ f z = 0}.Finite := by
  have hfiniteOrder (z : ℂ) : analyticOrderAt f z ≠ ⊤ :=
    (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z (fun w => hf.analyticAt w)).not.mpr hne
  have hfin := MeromorphicOn.divisor_support_inter_compact_finite f
    (U := Set.univ) (isCompact_closedBall (0 : ℂ) R) (Set.subset_univ _)
  apply hfin.subset
  intro z hz
  refine ⟨by simpa using hz.1, ?_⟩
  change MeromorphicOn.divisor f Set.univ z ≠ 0
  rw [(hf.differentiableOn.analyticOnNhd isOpen_univ).meromorphicOn.divisor_apply
    (Set.mem_univ z), (hf.analyticAt z).meromorphicOrderAt_eq]
  have hn0 := (hf.analyticAt z).analyticOrderAt_ne_zero.mpr hz.2
  simp [WithTop.untop₀_eq_zero, ENat.map_eq_top_iff, hn0, hfiniteOrder z]

theorem finite_ordinary_zero_window {q : ℕ} [NeZero q] (χ : Character q) (y : ℝ) :
    {ρ : ℂ | χ.LFunction ρ = 0 ∧ 1 / 2 ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ y}.Finite := by
  obtain ⟨f, hf, hne, hzeros⟩ : ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ f ≠ 0 ∧
      ∀ ρ : ℂ, ρ ≠ 1 → χ.LFunction ρ = 0 → f ρ = 0 := by
    by_cases hχ : χ = 1
    · subst χ
      refine ⟨DirichletCharacter.LFunctionTrivChar₁ q,
        DirichletCharacter.differentiable_LFunctionTrivChar₁ q, ?_, ?_⟩
      · intro h
        exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q
          (congrFun h 1)
      · intro ρ hρ hz
        rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hρ]
        change (ρ - 1) * (1 : Character q).LFunction ρ = 0
        rw [hz, mul_zero]
    · refine ⟨χ.LFunction, DirichletCharacter.differentiable_LFunction hχ, ?_,
        fun _ _ hz => hz⟩
      intro h
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ)
        (by norm_num : 1 ≤ (2 : ℂ).re) (congrFun h 2)
  apply (finite_entire_zeros_in_ball hf hne (1 + |y|)).subset
  intro ρ hρ
  refine ⟨?_, hzeros ρ (by intro h; simp [h] at hρ) hρ.1⟩
  calc
    ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 1 + |y| := by
      rw [abs_of_nonneg (by linarith [hρ.2.1])]
      linarith [hρ.2.2.1, hρ.2.2.2, le_abs_self y]

end LiuWang.Proof.NearOneDensity
