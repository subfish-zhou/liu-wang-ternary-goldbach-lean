import LiuWang.Proof.NearOneDensity.Continuation.PrincipalSeparation

set_option autoImplicit false
noncomputable section

open Classical
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.NearOneDensity.Continuation

instance conductor_neZero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : NeZero χ.conductor :=
  ⟨χ.conductor_ne_zero⟩

theorem effective_level_le {q : ℕ} [NeZero q] {z y : ℝ}
    (hqy : (q : ℝ) * max 1 y ≤ z) : (q : ℝ) ≤ z := by
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hh := mul_le_mul_of_nonneg_left (le_max_left (1 : ℝ) y) hq
  linarith

theorem effective_log_height {d q : ℕ} [NeZero d] [NeZero q] (hdq : d ∣ q)
    {z y t : ℝ} (hqy : (q : ℝ) * max 1 y ≤ z) (ht : |t| ≤ y) :
    Real.log d + Real.log (max 1 |t|) ≤ Real.log z := by
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hdqR : (d : ℝ) ≤ q := by exact_mod_cast Nat.le_of_dvd (NeZero.pos q) hdq
  have hm : max 1 |t| ≤ max 1 y := max_le_max_left 1 ht
  have hh := mul_le_mul hdqR hm (by positivity) (Nat.cast_nonneg q)
  have hm0 : 0 < max 1 |t| := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hlog := Real.log_le_log (mul_pos hd hm0) (hh.trans hqy)
  rwa [Real.log_mul hd.ne' hm0.ne'] at hlog

theorem inducing_row_selected_cost (r : DensityRow) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {z lam y : ℝ} {ρ : ℂ}
    (hz : 100000000000 ≤ z) (hqy : (q : ℝ) * max 1 y ≤ z)
    (hlam : 0 ≤ lam) (hlam₁ : lam ≤ rowLambda r)
    (hzero : χ.LFunction ρ = 0) (hre : 1 - lam / Real.log z ≤ ρ.re)
    (hright : ρ.re < 1) (ht : |ρ.im| ≤ y) :
    let σ := 1 + rowA r / Real.log z
    logKernel σ (stechkinSigma σ) stechkinK χ.primitiveCharacter ρ.im ≤
      -(Real.log z * zeroBudget (rowA r) lam stechkinConductorCoeff (1 / Real.log z)) := by
  by_cases hχ : χ = 1
  · subst χ
    have hα := source_alpha_ge_half hz (hlam₁.trans (row_basic_certificate r).2.1)
    have hzeta := (PrincipalPsi.principal_zero_iff_zeta_zero
      (show 0 < ρ.re by linarith)
      (show ρ ≠ 1 by intro hh; simp [hh] at hright)).mp hzero
    have hheight := effective_log_height (d := 1) (q := q) (one_dvd q) hqy ht
    simp only [Nat.cast_one, Real.log_one, zero_add] at hheight
    have hh := zeta_row_selected_cost r hz hlam hlam₁ hzeta hre hright hheight
    have he (d : ℕ) [NeZero d] (hd : d = 1) (σ τ c t : ℝ) :
        logKernel σ τ c (1 : DirichletCharacter ℂ d) t =
          logKernel σ τ c (1 : DirichletCharacter ℂ 1) t := by subst d; rfl
    dsimp only
    rw [DirichletCharacter.primitiveCharacter_one, he _ DirichletCharacter.conductor_one]
    exact hh
  · exact nonprincipal_inducing_row_selected_cost r χ hχ hz hlam hlam₁ hzero hre hright
      (effective_log_height χ.conductor_dvd_level hqy ht)

theorem inducing_row_cross_cost (r : DensityRow) {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) {z y t u : ℝ}
    (hz : 100000000000 ≤ z) (hqy : (q : ℝ) * max 1 y ≤ z)
    (ht : |t| ≤ y) (hu : |u| ≤ y)
    (hsep : χ = ψ → 2 * (rowRadius r / Real.log z) ≤ |t - u|) :
    let σ := 1 + rowA r / Real.log z
    logKernel σ (stechkinSigma σ) stechkinK
      (mixedQuotient χ.primitiveCharacter ψ.primitiveCharacter) (t - u) ≤
        Real.log z * crossBudget stechkinConductorCoeff (1 / Real.log z) := by
  have hdiv : Nat.lcm χ.conductor ψ.conductor ∣ q :=
    Nat.lcm_dvd χ.conductor_dvd_level ψ.conductor_dvd_level
  have hlog : Real.log (Nat.lcm χ.conductor ψ.conductor) ≤ Real.log q :=
    Real.log_le_log (by exact_mod_cast NeZero.pos (Nat.lcm χ.conductor ψ.conductor))
      (by exact_mod_cast Nat.le_of_dvd (NeZero.pos q) hdiv)
  have hh := height_difference_log hz hqy ht hu
  have hheight : Real.log (Nat.lcm χ.conductor ψ.conductor) +
      Real.log (max 1 |t - u|) ≤ Real.log z + Real.log 2 := by linarith
  by_cases heq : χ = ψ
  · subst ψ
    dsimp only
    rw [mixedQuotient_self]
    apply principal_row_separated_cost r hz _ hheight (hsep rfl)
    have hlevel := Real.log_le_log (show (0 : ℝ) < q by exact_mod_cast NeZero.pos q)
      (effective_level_le hqy)
    linarith
  · exact nonprincipal_row_cross_cost r _ (inducing_mixed_ne_one heq) hz hheight

end LiuWang.Proof.NearOneDensity.Continuation
