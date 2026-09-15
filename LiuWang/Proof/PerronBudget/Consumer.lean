import LiuWang.Proof.PerronBudget.Main

/-!
# Original-domain consumers with the actual finite psi sum

The high-zero set is a set of multiplicity labels, not distinct zero values.
Both boundary equalities are included, and the fiber cardinality is the
analytic multiplicity of the actual character L-function.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.ExplicitPerron LiuWang.Proof.FixedHeightZeroSum

namespace LiuWang.Proof.PerronBudget.Consumer

theorem closed_error_original_domain {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) {t Hminus Hplus : ℝ}
    (htlo : (N : ℝ) / 1000 ≤ t) (hthi : t ≤ (N : ℝ))
    (hminus : |Hminus + (Real.log (N : ℝ)) ^ (15 : ℕ)| ≤ 1)
    (hplus : |Hplus - (Real.log (N : ℝ)) ^ (15 : ℕ)| ≤ 1) :
    let L := Real.log (N : ℝ)
    let T := L ^ (15 : ℕ)
    let b := 1 + 1 / L
    closedRealEndpointError t b T Hminus Hplus ≤ 1.38022 * t / T * L ^ (2 : ℕ) :=
  closedRealEndpointError_le_source hN htlo hthi hminus hplus

theorem all_character_right_perron {N q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hN : Real.exp 2000 ≤ (N : ℝ))
    {t Hminus Hplus : ℝ} (htlo : (N : ℝ) / 1000 ≤ t) (hthi : t ≤ (N : ℝ))
    (hminus : |Hminus + (Real.log (N : ℝ)) ^ (15 : ℕ)| ≤ 1)
    (hplus : |Hplus - (Real.log (N : ℝ)) ^ (15 : ℕ)| ≤ 1) :
    let L := Real.log (N : ℝ)
    let T := L ^ (15 : ℕ)
    let b := 1 + 1 / L
    let F : ℂ → ℂ := fun s =>
      (-logDeriv chi.LFunction s) * ((t : ℂ) ^ s - (2.5 : ℂ) ^ s) / s
    ‖(1 / (2 * (Real.pi : ℂ))) *
        (∫ u in Hminus..Hplus, F ((b : ℂ) + (u : ℂ) * Complex.I)) -
        ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * chi n‖ ≤
      1.38022 * t / T * L ^ (2 : ℕ) := by
  intro L T b F
  have h := sourceDomain_right_perron_paid chi hN htlo hthi hminus hplus
  rw [centered_vertical_eq_actual_right] at h
  simpa only [L, T, b, F, sourceL, sourceT, actualRightVerticalIntegral, psi_eq_sum,
    Complex.ofReal_ofScientific] using h

theorem high_zero_fiber_card {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {T : ℝ} {rho : ℂ}
    (hrho : rho ∈ (highZeroIndices chi T).image completedZeroValue) :
    ((highZeroIndices chi T).filter (fun p => completedZeroValue p = rho)).card =
      analyticOrderNatAt chi.LFunction rho := by
  classical
  obtain ⟨p, hp, hpv⟩ := Finset.mem_image.mp hrho
  obtain ⟨hpT, hpre⟩ := (mem_highZeroIndices hchi hPrimitive T p).mp hp
  have hrre : 1 / 2 ≤ rho.re := by simpa only [hpv] using hpre
  have hfixed : rho ∈ fixedZeroValues chi T := by
    exact Finset.mem_image.mpr ⟨p, (mem_fixedZeroIndices hchi hPrimitive T p).mpr hpT, hpv⟩
  have hf :
      (highZeroIndices chi T).filter (fun r => completedZeroValue r = rho) =
        (fixedZeroIndices chi T).filter (fun r => completedZeroValue r = rho) := by
    ext r
    simp only [Finset.mem_filter, mem_highZeroIndices hchi hPrimitive,
      mem_fixedZeroIndices hchi hPrimitive]
    constructor
    · rintro ⟨⟨hrT, _⟩, hv⟩
      exact ⟨hrT, hv⟩
    · rintro ⟨hrT, hv⟩
      exact ⟨⟨hrT, by simpa only [hv] using hrre⟩, hv⟩
  rw [hf]
  exact fixedZeroFiber_card hchi hPrimitive hfixed

theorem primitive_nonprincipal_psi_fixed_high_zeros
    {N q : ℕ} [NeZero q] (hN : Real.exp 2000 ≤ (N : ℝ))
    (hq : 3 ≤ q) (hqUpper : (q : ℝ) ≤ (Real.log (N : ℝ)) ^ (6 : ℕ))
    {chi : DirichletCharacter ℂ q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) :
    let L := Real.log (N : ℝ)
    let T := L ^ (15 : ℕ)
    let b := 1 + 1 / L
    ∃ Hplus Hminus : ℝ, ∃ Zhigh : Finset (CompletedZeroIndex chi),
      |Hplus - T| ≤ 1 ∧ |Hminus + T| ≤ 1 ∧
      (∀ p : CompletedZeroIndex chi,
        (1.7769 * Real.log ((q : ℝ) * T))⁻¹ ≤ |(completedZeroValue p).im - Hplus| ∧
        (1.7769 * Real.log ((q : ℝ) * T))⁻¹ ≤ |(completedZeroValue p).im - Hminus|) ∧
      (∀ p : CompletedZeroIndex chi, p ∈ Zhigh ↔
        |(completedZeroValue p).im| ≤ T ∧ 1 / 2 ≤ (completedZeroValue p).re) ∧
      (∀ rho ∈ Zhigh.image completedZeroValue,
        (Zhigh.filter (fun p => completedZeroValue p = rho)).card =
          analyticOrderNatAt chi.LFunction rho) ∧
      ∀ t : ℝ, (N : ℝ) / 1000 ≤ t → t ≤ (N : ℝ) →
        let F : ℂ → ℂ := fun s =>
          (-logDeriv chi.LFunction s) * ((t : ℂ) ^ s - (2.5 : ℂ) ^ s) / s
        let PS : ℂ := ∑ n ∈ Finset.Icc 1 ⌊t⌋₊,
          (ArithmeticFunction.vonMangoldt n : ℂ) * chi n
        let ZH : ℂ := ∑ p ∈ Zhigh, (t : ℂ) ^ completedZeroValue p / completedZeroValue p
        ‖(1 / (2 * (Real.pi : ℂ))) *
            (∫ u in Hminus..Hplus, F ((b : ℂ) + (u : ℂ) * Complex.I)) - PS‖ ≤
          1.38022 * t / T * L ^ (2 : ℕ) ∧
        ‖(1 / (2 * (Real.pi : ℂ))) *
            (∫ u in Hminus..Hplus, F ((b : ℂ) + (u : ℂ) * Complex.I)) + ZH‖ ≤
          0.000171 * t / T * L ^ (2 : ℕ) ∧
        ‖PS + ZH‖ ≤ 1.380391 * t / T * L ^ (2 : ℕ) := by
  classical
  intro L T b
  obtain ⟨Hp, Hm, hh, hall⟩ := exists_paid_estimates_all_real_endpoints hN hq hqUpper hchi hPrimitive
  refine ⟨Hp, Hm, highZeroIndices chi T, hh.1, hh.2.1, hh.2.2,
    mem_highZeroIndices hchi hPrimitive T, ?_, ?_⟩
  · exact fun _ hrho => high_zero_fiber_card hchi hPrimitive hrho
  · intro t htlo hthi F PS ZH
    simpa only [L, T, b, F, PS, ZH, sourceL, sourceT, actualRightVerticalIntegral,
      highZeroSum, psi_eq_sum, Complex.ofReal_ofScientific] using hall t htlo hthi

theorem primitive_nonprincipal_psi_sum
    {N q : ℕ} [NeZero q] (hN : Real.exp 2000 ≤ (N : ℝ))
    (hq : 3 ≤ q) (hqUpper : (q : ℝ) ≤ (Real.log (N : ℝ)) ^ (6 : ℕ))
    {chi : DirichletCharacter ℂ q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {t : ℝ} (htlo : (N : ℝ) / 1000 ≤ t) (hthi : t ≤ (N : ℝ)) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * chi n) +
        ∑ p ∈ highZeroIndices chi ((Real.log (N : ℝ)) ^ (15 : ℕ)),
          (t : ℂ) ^ completedZeroValue p / completedZeroValue p‖ ≤
      1.380391 * t / (Real.log (N : ℝ)) ^ (15 : ℕ) *
        (Real.log (N : ℝ)) ^ (2 : ℕ) := by
  simpa only [psi_eq_sum, highZeroSum, sourceL, sourceT] using
    psi_highZeroSum_source_le hN hq hqUpper hchi hPrimitive htlo hthi

end LiuWang.Proof.PerronBudget.Consumer
