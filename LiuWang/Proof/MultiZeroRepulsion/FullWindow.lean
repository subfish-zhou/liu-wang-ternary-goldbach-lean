import LiuWang.Proof.MultiZeroRepulsion.TripleProduct

/-! Actual full closed-height selected masses and their two/three-phase Euler consumers. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.MultiZeroRepulsion

def strictZeroValues {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (alpha y : ℝ) : Finset ℂ :=
  (DirichletZeroCount.zeroValues chi alpha y).filter (fun rho => alpha < rho.re)

theorem mem_strictZeroValues {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    {alpha y : ℝ} {rho : ℂ} :
    rho ∈ strictZeroValues chi alpha y ↔
      chi.LFunction rho = 0 ∧ 0 < rho.re ∧ alpha < rho.re ∧ rho.re < 1 ∧ |rho.im| ≤ y := by
  simp only [strictZeroValues, Finset.mem_filter, DirichletZeroCount.mem_zeroValues]
  constructor
  · rintro ⟨⟨hz, ⟨h0, h1, ht⟩, _⟩, ha⟩
    exact ⟨hz, h0, ha, h1, ht⟩
  · rintro ⟨hz, h0, ha, h1, ht⟩
    exact ⟨⟨hz, ⟨h0, h1, ht⟩, ha.le⟩, ha⟩

def ordinaryMass {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (sigma t : ℝ) (v : Finset ℂ) : ℝ :=
  ∑ rho ∈ v, (analyticOrderNatAt chi.LFunction rho : ℝ) * reflectedKernel sigma t rho

def ordinaryCost {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (sigma t : ℝ) : ℝ :=
  if chi = 1 then
    poleDifference sigma t +
      stechkinConductorCoeff * (Real.log (max 1 |t|) - Real.log Real.pi) +
        23 / 40 - 11 * stechkinK / 30 + principalPrimeCost q sigma
  else
    stechkinConductorCoeff *
      (Real.log chi.conductor + Real.log (max 1 |t|) - Real.log Real.pi) +
        4 / 15 + badPrimeCost chi sigma

theorem ordinary_selected_bound {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (t : ℝ) (v : Finset ℂ)
    (hr : ∀ rho ∈ v, 1 / 2 < rho.re ∧ rho.re < 1) :
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK t + ordinaryMass chi sigma t v ≤
      ordinaryCost chi sigma t := by
  by_cases hc : chi = 1
  · subst chi
    simpa only [ordinaryCost, if_pos rfl, ite_true, ordinaryMass] using
      principal_ordinary_selected_bound q hs hs1 t v hr
  · simpa only [ordinaryCost, if_neg hc, ordinaryMass] using
      nonprincipal_ordinary_selected_bound chi hc hs hs1 t v (fun rho h => (hr rho h).1)

theorem polynomial_selected_bound {q : ℕ} [NeZero q] {ι : Type*}
    (s : Finset ι) (chi : ι → DirichletCharacter ℂ q) (t c : ι → ℝ)
    (hc : ∀ j ∈ s, 0 ≤ c j)
    (hp : ∀ n : ℕ, n ≠ 0 → IsUnit (n : ZMod q) →
      0 ≤ ∑ j ∈ s, c j * (phase (chi j) (t j) n).re)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20)
    (v : ι → Finset ℂ) (hr : ∀ j ∈ s, ∀ rho ∈ v j, 1 / 2 < rho.re ∧ rho.re < 1) :
    (∑ j ∈ s, c j * ordinaryMass (chi j) sigma (t j) (v j)) ≤
      ∑ j ∈ s, c j * ordinaryCost (chi j) sigma (t j) := by
  have he := damped_polynomial_nonneg s chi t c hp hs (stechkinSigma_ge hs) stechkinK_mem
  have hh := Finset.sum_le_sum (fun j hj =>
    mul_le_mul_of_nonneg_left (ordinary_selected_bound (chi j) hs hs1 (t j) (v j) (hr j hj))
      (hc j hj))
  simp only [mul_add, Finset.sum_add_distrib] at hh
  linarith

theorem pair_selected_bound {q : ℕ} [NeZero q] (chi psi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (t u : ℝ)
    (v : Fin 5 → Finset ℂ) (hr : ∀ j rho, rho ∈ v j → 1 / 2 < rho.re ∧ rho.re < 1) :
    (∑ j : Fin 5, pairCoefficients j *
      ordinaryMass (pairCharacters chi psi j) sigma (pairHeights t u j) (v j)) ≤
      ∑ j : Fin 5, pairCoefficients j *
        ordinaryCost (pairCharacters chi psi j) sigma (pairHeights t u j) := by
  refine polynomial_selected_bound Finset.univ _ _ _ ?_ ?_ hs hs1 v ?_
  · intro j _
    fin_cases j <;> norm_num [pairCoefficients]
  · intro n hn hu
    exact pair_phase_nonneg chi psi hn hu t u
  · intro j _ rho h
    exact hr j rho h

theorem triple_selected_bound {q : ℕ} [NeZero q] (chi psi eta : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (t u w : ℝ)
    (v : Fin 14 → Finset ℂ) (hr : ∀ j rho, rho ∈ v j → 1 / 2 < rho.re ∧ rho.re < 1) :
    (∑ j : Fin 14, tripleCoefficients j *
      ordinaryMass (tripleCharacters chi psi eta j) sigma (tripleHeights t u w j) (v j)) ≤
      ∑ j : Fin 14, tripleCoefficients j *
        ordinaryCost (tripleCharacters chi psi eta j) sigma (tripleHeights t u w j) := by
  refine polynomial_selected_bound Finset.univ _ _ _ ?_ ?_ hs hs1 v ?_
  · intro j _
    fin_cases j <;> norm_num [tripleCoefficients]
  · intro n hn hu
    exact triple_phase_nonneg chi psi eta hn hu t u w
  · intro j _ rho h
    exact hr j rho h

theorem pair_full_window_bound {q : ℕ} [NeZero q] (chi psi : DirichletCharacter ℂ q)
    {sigma alpha : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (ha : 1 / 2 ≤ alpha)
    (y t u : ℝ) :
    (∑ j : Fin 5, pairCoefficients j *
      ordinaryMass (pairCharacters chi psi j) sigma (pairHeights t u j)
        (strictZeroValues (pairCharacters chi psi j) alpha y)) ≤
      ∑ j : Fin 5, pairCoefficients j *
        ordinaryCost (pairCharacters chi psi j) sigma (pairHeights t u j) := by
  apply pair_selected_bound chi psi hs hs1 t u
  intro j rho hr
  have hh := mem_strictZeroValues.mp hr
  exact ⟨ha.trans_lt hh.2.2.1, hh.2.2.2.1⟩

theorem triple_full_window_bound {q : ℕ} [NeZero q]
    (chi psi eta : DirichletCharacter ℂ q) {sigma alpha : ℝ}
    (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (ha : 1 / 2 ≤ alpha) (y t u w : ℝ) :
    (∑ j : Fin 14, tripleCoefficients j *
      ordinaryMass (tripleCharacters chi psi eta j) sigma (tripleHeights t u w j)
        (strictZeroValues (tripleCharacters chi psi eta j) alpha y)) ≤
      ∑ j : Fin 14, tripleCoefficients j *
        ordinaryCost (tripleCharacters chi psi eta j) sigma (tripleHeights t u w j) := by
  apply triple_selected_bound chi psi eta hs hs1 t u w
  intro j rho hr
  have hh := mem_strictZeroValues.mp hr
  exact ⟨ha.trans_lt hh.2.2.1, hh.2.2.2.1⟩

end LiuWang.Proof.MultiZeroRepulsion
