import LiuWang.Proof.NearOneDensity.ZeroFiniteness

set_option autoImplicit false
noncomputable section

open Classical Filter Topology
open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.NearOneDensity

theorem analytic_ordinary_L_of_ne_one {q : ℕ} [NeZero q] (χ : Character q)
    {ρ : ℂ} (hρ : ρ ≠ 1) : AnalyticAt ℂ χ.LFunction ρ := by
  have hA : AnalyticOnNhd ℂ χ.LFunction {1}ᶜ :=
    DifferentiableOn.analyticOnNhd
      (fun z hz => (DirichletCharacter.differentiableAt_LFunction χ z
        (.inl hz)).differentiableWithinAt) isOpen_compl_singleton
  exact hA ρ hρ

theorem ordinary_analyticOrder_ne_top {q : ℕ} [NeZero q] (χ : Character q)
    {ρ : ℂ} (hρ : ρ ≠ 1) : analyticOrderAt χ.LFunction ρ ≠ ⊤ := by
  by_cases hχ : χ = 1
  · subst χ
    let f := DirichletCharacter.LFunctionTrivChar₁ q
    have hf : Differentiable ℂ f := DirichletCharacter.differentiable_LFunctionTrivChar₁ q
    have hne : f ≠ 0 := by
      intro h
      exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q (congrFun h 1)
    have hfin : analyticOrderAt f ρ ≠ ⊤ :=
      (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero ρ (fun z => hf.analyticAt z)).not.mpr hne
    have he : f =ᶠ[𝓝 ρ] (fun z => z - 1) * (1 : Character q).LFunction := by
      filter_upwards [eventually_ne_nhds hρ] with z hz
      exact Function.update_of_ne hz _ _
    have ho := analyticOrderAt_congr he
    rw [analyticOrderAt_mul (by fun_prop) (analytic_ordinary_L_of_ne_one 1 hρ),
      (by fun_prop : AnalyticAt ℂ (fun z : ℂ => z - 1) ρ).analyticOrderAt_eq_zero.mpr
        (sub_ne_zero.mpr hρ), zero_add] at ho
    rwa [← ho]
  · have hf := DirichletCharacter.differentiable_LFunction hχ
    apply (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero ρ
      (fun z => hf.analyticAt z)).not.mpr
    intro h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ)
      (by norm_num : 1 ≤ (2 : ℂ).re) (congrFun h 2)

theorem ordinary_zero_multiplicity_pos {q : ℕ} [NeZero q] (χ : Character q)
    {ρ : ℂ} (hρ : ρ ≠ 1) (hz : χ.LFunction ρ = 0) :
    0 < analyticOrderNatAt χ.LFunction ρ := by
  have hn := (analytic_ordinary_L_of_ne_one χ hρ).analyticOrderAt_ne_zero.mpr hz
  have hf := ordinary_analyticOrder_ne_top χ hρ
  apply Nat.pos_of_ne_zero
  intro h
  apply hn
  rw [← Nat.cast_analyticOrderNatAt hf, h]
  rfl

end LiuWang.Proof.NearOneDensity
