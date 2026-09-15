import LiuWang.Proof.NearOneDensity.CrossConsumer

set_option autoImplicit false
noncomputable section

open scoped BigOperators ComplexConjugate
open Classical

namespace LiuWang.Proof.NearOneDensity.Continuation

instance lcm_neZero (d e : ℕ) [NeZero d] [NeZero e] : NeZero (Nat.lcm d e) :=
  ⟨Nat.lcm_ne_zero (NeZero.ne d) (NeZero.ne e)⟩

def mixedQuotient {d e : ℕ} (χ : DirichletCharacter ℂ d) (ψ : DirichletCharacter ℂ e) :
    DirichletCharacter ℂ (Nat.lcm d e) :=
  quotientCharacter (χ.changeLevel (Nat.dvd_lcm_left d e))
    (ψ.changeLevel (Nat.dvd_lcm_right d e))

theorem changeLevel_nat_apply {d D n : ℕ} (χ : DirichletCharacter ℂ d)
    (hd : d ∣ D) (hn : n.Coprime D) :
    χ.changeLevel hd n = χ n := by
  have hh := χ.changeLevel_eq_cast_of_dvd hd (ZMod.unitOfCoprime n hn)
  simpa only [ZMod.coe_unitOfCoprime, ZMod.cast_natCast hd] using hh

theorem mixedQuotient_nat_apply {d e : ℕ} (χ : DirichletCharacter ℂ d)
    (ψ : DirichletCharacter ℂ e) (n : ℕ) :
    mixedQuotient χ ψ n = χ n * conj (ψ n) := by
  by_cases hd : n.Coprime d
  · by_cases he : n.Coprime e
    · have hde := (hd.mul_right he).of_dvd_right (Nat.lcm_dvd_mul d e)
      simp only [mixedQuotient, quotientCharacter, MulChar.mul_apply, MulChar.ringHomComp_apply,
        changeLevel_nat_apply χ (Nat.dvd_lcm_left d e) hde,
        changeLevel_nat_apply ψ (Nat.dvd_lcm_right d e) hde]
    · have he' : ¬ n.Coprime (Nat.lcm d e) :=
        fun h => he (h.of_dvd_right (Nat.dvd_lcm_right d e))
      have hz : ψ n = 0 := MulChar.map_nonunit _ (fun h => he ((ZMod.isUnit_iff_coprime _ _).mp h))
      have hz' : ψ.changeLevel (Nat.dvd_lcm_right d e) n = 0 :=
        MulChar.map_nonunit _ (fun h => he' ((ZMod.isUnit_iff_coprime _ _).mp h))
      simp [mixedQuotient, quotientCharacter, MulChar.mul_apply, hz, hz']
  · have hd' : ¬ n.Coprime (Nat.lcm d e) :=
      fun h => hd (h.of_dvd_right (Nat.dvd_lcm_left d e))
    have hz : χ n = 0 := MulChar.map_nonunit _ (fun h => hd ((ZMod.isUnit_iff_coprime _ _).mp h))
    have hz' : χ.changeLevel (Nat.dvd_lcm_left d e) n = 0 :=
      MulChar.map_nonunit _ (fun h => hd' ((ZMod.isUnit_iff_coprime _ _).mp h))
    simp [mixedQuotient, quotientCharacter, MulChar.mul_apply, hz, hz']

theorem mixed_phase_correlation {d e : ℕ} (χ : DirichletCharacter ℂ d)
    (ψ : DirichletCharacter ℂ e) (t u : ℝ) (n : ℕ) :
    phase χ t n * conj (phase ψ u n) = phase (mixedQuotient χ ψ) (t - u) n := by
  by_cases hn : n = 0
  · simp [phase, hn]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have harg : (n : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]
    exact Real.pi_ne_zero.symm
  have hc : conj ((n : ℂ) ^ ((u : ℂ) * Complex.I)) = (n : ℂ) ^ (-((u : ℂ) * Complex.I)) := by
    simpa using (Complex.cpow_conj (n : ℂ) ((u : ℂ) * Complex.I) harg).symm
  simp only [phase, if_neg hn, map_div₀]
  rw [hc, div_mul_div_comm, ← Complex.cpow_add _ _ hnC, mixedQuotient_nat_apply]
  congr 1
  congr 1
  push_cast
  ring

theorem mixed_correlation_eq_logKernel {d e : ℕ} [NeZero d] [NeZero e]
    (χ : DirichletCharacter ℂ d) (ψ : DirichletCharacter ℂ e) (t u : ℝ)
    {σ τ c : ℝ} (hσ : 1 < σ) (hτ : 1 < τ) :
    (∑' n, dampedWeight σ τ c n * (phase χ t n * conj (phase ψ u n)).re) =
      logKernel σ τ c (mixedQuotient χ ψ) (t - u) := by
  rw [logKernel_eq_series _ _ hσ hτ]
  exact tsum_congr (fun n => by rw [mixed_phase_correlation])

theorem mixed_quotient_changeLevel {d e q : ℕ} (χ : DirichletCharacter ℂ d)
    (ψ : DirichletCharacter ℂ e) (hd : d ∣ q) (he : e ∣ q) :
    (mixedQuotient χ ψ).changeLevel (Nat.lcm_dvd hd he) =
      quotientCharacter (χ.changeLevel hd) (ψ.changeLevel he) := by
  change (χ.changeLevel _ * star (ψ.changeLevel _)).changeLevel _ =
    χ.changeLevel hd * star (ψ.changeLevel he)
  rw [MulChar.star_eq_inv, MulChar.star_eq_inv, map_mul, map_inv,
    ← DirichletCharacter.changeLevel_trans, ← DirichletCharacter.changeLevel_trans]

theorem inducing_mixed_ne_one {q : ℕ} [NeZero q] {χ ψ : DirichletCharacter ℂ q}
    (hne : χ ≠ ψ) :
    mixedQuotient χ.primitiveCharacter ψ.primitiveCharacter ≠ 1 := by
  intro hh
  have h := mixed_quotient_changeLevel χ.primitiveCharacter ψ.primitiveCharacter
    χ.conductor_dvd_level ψ.conductor_dvd_level
  rw [hh, map_one, DirichletCharacter.changeLevel_primitiveCharacter,
    DirichletCharacter.changeLevel_primitiveCharacter] at h
  exact quotientCharacter_ne_one hne h.symm

theorem mixedQuotient_self {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) :
    mixedQuotient χ χ = 1 := by
  apply DirichletCharacter.changeLevel_injective (Nat.lcm_dvd (dvd_refl d) (dvd_refl d))
  rw [mixed_quotient_changeLevel χ χ (dvd_refl d) (dvd_refl d), map_one]
  change χ.changeLevel _ * star (χ.changeLevel _) = 1
  rw [MulChar.star_eq_inv, mul_inv_cancel]

theorem mixed_summable {d e : ℕ} (χ : DirichletCharacter ℂ d) (ψ : DirichletCharacter ℂ e)
    (t u : ℝ) {σ τ c : ℝ} (hσ : 1 < σ) (hτ : 1 < τ) (hστ : σ ≤ τ) (hc : c ≤ 1) :
    Summable (fun n => dampedWeight σ τ c n * (phase χ t n * conj (phase ψ u n)).re) := by
  apply (summable_dampedWeight (c := c) hσ hτ).of_norm_bounded
  intro n
  have hnorm : ‖phase χ t n * conj (phase ψ u n)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_one₀ (norm_phase_le_one _ _ _) (norm_nonneg _) (norm_phase_le_one _ _ _)
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (dampedWeight_nonneg hστ hc n)]
  exact mul_le_of_le_one_right (dampedWeight_nonneg hστ hc n)
    ((Complex.abs_re_le_norm _).trans hnorm)

theorem mixed_count {ι : Type*} (s : Finset ι) (d : ι → ℕ) [∀ i, NeZero (d i)]
    (χ : (i : ι) → DirichletCharacter ℂ (d i)) (t : ι → ℝ)
    {σ τ c A B D : ℝ} (hσ : 1 < σ) (hτ : 1 < τ) (hστ : σ ≤ τ) (hc : c ≤ 1)
    (hA : 0 ≤ A) (hBA : B ≤ A) (hD : 0 ≤ D)
    (hmass : (∑' n, dampedWeight σ τ c n) ≤ A)
    (hzero : ∀ i ∈ s, logKernel σ τ c (χ i) (t i) ≤ -D)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      logKernel σ τ c (mixedQuotient (χ i) (χ j)) (t i - t j) ≤ B)
    (hgap : 0 < D ^ 2 - A * B) :
    (s.card : ℝ) ≤ (A ^ 2 - A * B) / (D ^ 2 - A * B) := by
  apply count_of_series s (dampedWeight σ τ c) (fun i => phase (χ i) (t i))
    (dampedWeight_nonneg hστ hc) (summable_dampedWeight hσ hτ)
    (fun i _ => summable_weight_phase_re (χ i) (t i) hσ hτ)
    (fun i _ j _ => mixed_summable (χ i) (χ j) (t i) (t j) hσ hτ hστ hc)
    hA hBA hD hmass
  · simpa only [← logKernel_eq_series _ _ hσ hτ] using hzero
  · intro i _
    have hh : (∑' n, dampedWeight σ τ c n *
        (phase (χ i) (t i) n * conj (phase (χ i) (t i) n)).re) ≤ ∑' n, dampedWeight σ τ c n := by
      apply (mixed_summable (χ i) (χ i) (t i) (t i) hσ hτ hστ hc).tsum_le_tsum _
        (summable_dampedWeight hσ hτ)
      intro n
      have hn : ‖phase (χ i) (t i) n * conj (phase (χ i) (t i) n)‖ ≤ 1 := by
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_one₀ (norm_phase_le_one _ _ _) (norm_nonneg _) (norm_phase_le_one _ _ _)
      exact mul_le_of_le_one_right (dampedWeight_nonneg hστ hc n) ((Complex.re_le_norm _).trans hn)
    exact hh.trans hmass
  · simpa only [mixed_correlation_eq_logKernel _ _ _ _ hσ hτ] using hoff
  · exact hgap

end LiuWang.Proof.NearOneDensity.Continuation
