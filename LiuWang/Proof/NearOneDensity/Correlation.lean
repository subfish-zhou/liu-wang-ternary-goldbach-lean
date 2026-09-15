import LiuWang.Proof.NearOneDensity.DirichletKernel

set_option autoImplicit false
noncomputable section

open scoped BigOperators ComplexConjugate
open Classical

namespace LiuWang.Proof.NearOneDensity

def quotientCharacter {q : ℕ} (χ ψ : DirichletCharacter ℂ q) : DirichletCharacter ℂ q :=
  χ * ψ.ringHomComp (starRingEnd ℂ)

theorem phase_correlation {q : ℕ} (χ ψ : DirichletCharacter ℂ q) (t u : ℝ) (n : ℕ) :
    phase χ t n * conj (phase ψ u n) = phase (quotientCharacter χ ψ) (t - u) n := by
  by_cases hn : n = 0
  · simp [phase, hn]
  · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have harg : (n : ℂ).arg ≠ Real.pi := by
      rw [Complex.natCast_arg]
      exact Real.pi_ne_zero.symm
    have hc : conj ((n : ℂ) ^ ((u : ℂ) * Complex.I)) =
        (n : ℂ) ^ (-((u : ℂ) * Complex.I)) := by
      simpa using (Complex.cpow_conj (n : ℂ) ((u : ℂ) * Complex.I) harg).symm
    simp only [phase, if_neg hn, map_div₀]
    rw [hc, div_mul_div_comm, ← Complex.cpow_add _ _ hnC]
    congr 1
    congr 1
    push_cast
    ring

theorem correlation_eq_logKernel {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (t u : ℝ)
    {σ τ c : ℝ} (hσ : 1 < σ) (hτ : 1 < τ) :
    (∑' n, dampedWeight σ τ c n * (phase χ t n * conj (phase ψ u n)).re) =
      logKernel σ τ c (quotientCharacter χ ψ) (t - u) := by
  rw [logKernel_eq_series _ _ hσ hτ]
  exact tsum_congr (fun n => by rw [phase_correlation])

theorem logKernel_quadratic {ι : Type*} {q : ℕ} [NeZero q] (s : Finset ι)
    (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    {σ τ c : ℝ} (hσ : 1 < σ) (hτ : 1 < τ) (hστ : σ ≤ τ) (hc : c ≤ 1) :
    (∑ i ∈ s, logKernel σ τ c (χ i) (t i)) ^ 2 ≤
      (∑' n, dampedWeight σ τ c n) * ∑ i ∈ s, ∑ j ∈ s,
        logKernel σ τ c (quotientCharacter (χ i) (χ j)) (t i - t j) := by
  simpa only [correlation_eq_logKernel _ _ _ _ hσ hτ] using
    dirichlet_quadratic s χ t hσ hτ hστ hc

theorem logKernel_diagonal_le_mass {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q)
    {σ τ c : ℝ} (hσ : 1 < σ) (hτ : 1 < τ) (hστ : σ ≤ τ) (hc : c ≤ 1) :
    logKernel σ τ c (quotientCharacter χ χ) 0 ≤ ∑' n, dampedWeight σ τ c n := by
  have he := correlation_eq_logKernel χ χ 0 0 (c := c) hσ hτ
  simp only [sub_self] at he
  rw [← he]
  apply (summable_weight_correlation (fun _ : Unit => χ) (fun _ => 0)
    hσ hτ hστ hc () ()).tsum_le_tsum _ (summable_dampedWeight hσ hτ)
  intro n
  have hnorm : ‖phase χ 0 n * conj (phase χ 0 n)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_one₀ (norm_phase_le_one _ _ _) (norm_nonneg _) (norm_phase_le_one _ _ _)
  exact mul_le_of_le_one_right (dampedWeight_nonneg hστ hc n)
    ((Complex.re_le_norm _).trans hnorm)

theorem count_of_logKernel {ι : Type*} {q : ℕ} [NeZero q] (s : Finset ι)
    (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    {σ τ c A B D : ℝ} (hσ : 1 < σ) (hτ : 1 < τ) (hστ : σ ≤ τ) (hc : c ≤ 1)
    (hA : 0 ≤ A) (hBA : B ≤ A) (hD : 0 ≤ D)
    (hmass : (∑' n, dampedWeight σ τ c n) ≤ A)
    (hzero : ∀ i ∈ s, logKernel σ τ c (χ i) (t i) ≤ -D)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      logKernel σ τ c (quotientCharacter (χ i) (χ j)) (t i - t j) ≤ B)
    (hgap : 0 < D ^ 2 - A * B) :
    (s.card : ℝ) ≤ (A ^ 2 - A * B) / (D ^ 2 - A * B) := by
  apply count_of_series s (dampedWeight σ τ c) (fun i => phase (χ i) (t i))
    (dampedWeight_nonneg hστ hc) (summable_dampedWeight hσ hτ)
    (fun i _ => summable_weight_phase_re (χ i) (t i) hσ hτ)
    (fun i _ j _ => summable_weight_correlation χ t hσ hτ hστ hc i j)
    hA hBA hD hmass
  · simpa only [← logKernel_eq_series _ _ hσ hτ] using hzero
  · intro i _
    rw [correlation_eq_logKernel _ _ _ _ hσ hτ, sub_self]
    exact (logKernel_diagonal_le_mass (χ i) hσ hτ hστ hc).trans hmass
  · simpa only [correlation_eq_logKernel _ _ _ _ hσ hτ] using hoff
  · exact hgap

end LiuWang.Proof.NearOneDensity
