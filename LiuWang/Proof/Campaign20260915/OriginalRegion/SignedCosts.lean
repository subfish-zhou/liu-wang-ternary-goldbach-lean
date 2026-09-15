import LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1.PrincipalIdentity
import LiuWang.Proof.MultiZeroRepulsion.FullWindow

/-! Actual signed explicit-formula costs, before absolute Euler/Gamma bounds. -/

set_option autoImplicit false
noncomputable section

open Complex
open scoped BigOperators Classical
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1
open LiuWang.Proof.MultiZeroRepulsion

namespace LiuWang.Proof.Campaign20260915.OriginalRegion

def levelEulerDifference {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (sigma t : ℝ) : ℝ :=
  (logDeriv (levelCorrection chi) ((sigma : ℂ) + I * t) -
    (stechkinK : ℂ) *
      logDeriv (levelCorrection chi) ((stechkinSigma sigma : ℂ) + I * t)).re

def signedCost {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (sigma t : ℝ) : ℝ :=
  if chi = 1 then
    poleDifference sigma t - kappa * Real.log Real.pi + gammaTerm 2 sigma t -
      principalEulerDifference q sigma t
  else
    kappa * Real.log ((chi.conductor : ℝ) / Real.pi) +
      gammaTerm (parityShift chi.primitiveCharacter) sigma t -
        levelEulerDifference chi sigma t

def fullZeroMass {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (sigma t : ℝ) : ℝ :=
  if chi = 1 then zetaZeroSum sigma t else zeroSum chi sigma t

theorem f_eq_primitive_sub_signed {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor] (hc : chi ≠ 1)
    {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    f chi sigma t = f chi.primitiveCharacter sigma t -
      levelEulerDifference chi sigma t := by
  simp only [f_eq_damped, dampedLogDeriv]
  rw [logDeriv_LFunction_eq_primitive_add_levelCorrection chi hc
      (by simpa [mul_re] using hs.le),
    logDeriv_LFunction_eq_primitive_add_levelCorrection chi hc
      (by simpa [mul_re] using (hs.trans_le (stechkinSigma_ge hs)).le)]
  simp only [levelEulerDifference, add_re, sub_re, mul_re, ofReal_re,
    ofReal_im, zero_mul, sub_zero]
  ring

theorem signed_full_identity {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    f chi sigma t + fullZeroMass chi sigma t = signedCost chi sigma t := by
  by_cases hc : chi = 1
  · subst chi
    simp only [fullZeroMass, signedCost, ite_true]
    rw [l24_principal_identity hs]
    ring
  · let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
    have hpr := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hc
    simp only [fullZeroMass, signedCost, if_neg hc]
    rw [f_eq_primitive_sub_signed chi hc hs,
      l25_primitive_identity hpr chi.primitiveCharacter_isPrimitive hs,
      zeroSum_eq_primitive chi hc]
    ring

theorem ordinaryMass_le_fullZeroMass {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {sigma : ℝ} (hs : 1 < sigma)
    (t : ℝ) (v : Finset ℂ)
    (hr : ∀ rho ∈ v, 1 / 2 < rho.re ∧ rho.re < 1) :
    ordinaryMass chi sigma t v ≤ fullZeroMass chi sigma t := by
  by_cases hc : chi = 1
  · subst chi
    simpa only [ordinaryMass, fullZeroMass, ite_true] using
      principal_ordinary_mass_le q hs t v hr
  · let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
    have hpr := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hc
    simp only [fullZeroMass, if_neg hc]
    rw [zeroSum_eq_primitive chi hc,
      zeroSum_eq_completed hpr chi.primitiveCharacter_isPrimitive]
    have hh := primitive_ordinary_mass_le hpr chi.primitiveCharacter_isPrimitive
      hs t v (fun rho h => (hr rho h).1)
    convert hh using 1
    apply Finset.sum_congr rfl
    intro rho hrv
    rw [analyticOrderNatAt_LFunction_eq_primitive chi hc (by linarith [(hr rho hrv).1])]

theorem signed_ordinary_selected_bound {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {sigma : ℝ} (hs : 1 < sigma)
    (t : ℝ) (v : Finset ℂ)
    (hr : ∀ rho ∈ v, 1 / 2 < rho.re ∧ rho.re < 1) :
    f chi sigma t + ordinaryMass chi sigma t v ≤ signedCost chi sigma t := by
  rw [← signed_full_identity chi hs t]
  exact add_le_add le_rfl (ordinaryMass_le_fullZeroMass chi hs t v hr)

theorem signed_polynomial_selected_bound {q : ℕ} [NeZero q] {ι : Type*}
    (s : Finset ι) (chi : ι → DirichletCharacter ℂ q) (t c : ι → ℝ)
    (hc : ∀ j ∈ s, 0 ≤ c j)
    (hp : ∀ n : ℕ, n ≠ 0 → IsUnit (n : ZMod q) →
      0 ≤ ∑ j ∈ s, c j * (phase (chi j) (t j) n).re)
    {sigma : ℝ} (hs : 1 < sigma)
    (v : ι → Finset ℂ)
    (hr : ∀ j ∈ s, ∀ rho ∈ v j, 1 / 2 < rho.re ∧ rho.re < 1) :
    (∑ j ∈ s, c j * ordinaryMass (chi j) sigma (t j) (v j)) ≤
      ∑ j ∈ s, c j * signedCost (chi j) sigma (t j) := by
  have he := damped_polynomial_nonneg s chi t c hp hs (stechkinSigma_ge hs) stechkinK_mem
  have hh := Finset.sum_le_sum (fun j hj =>
    mul_le_mul_of_nonneg_left
      (signed_ordinary_selected_bound (chi j) hs (t j) (v j) (hr j hj)) (hc j hj))
  simp only [f_eq_damped, mul_add, Finset.sum_add_distrib] at hh
  linarith

theorem signedCost_le_ordinaryCost {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {sigma : ℝ}
    (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (t : ℝ) :
    signedCost chi sigma t ≤ ordinaryCost chi sigma t := by
  rw [← signed_full_identity chi hs t, f_eq_damped]
  by_cases hc : chi = 1
  · subst chi
    simpa only [fullZeroMass, ordinaryCost, ite_true] using
      principal_full_zero_sum_bound (q := q) hs hs1 t
  · let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
    have hpr := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hc
    simp only [fullZeroMass, ordinaryCost, if_neg hc]
    rw [zeroSum_eq_primitive chi hc,
      zeroSum_eq_completed hpr chi.primitiveCharacter_isPrimitive]
    exact imprimitive_full_zero_sum_bound chi hc hs hs1 t

theorem signed_principal_real_cost {q : ℕ} [NeZero q] {sigma : ℝ}
    (hs : 1 < sigma) :
    signedCost (1 : DirichletCharacter ℂ q) sigma 0 =
      poleDifference sigma 0 + shiftedGammaDifference sigma 0 -
        principalPrimeCost q sigma := by
  rw [← signed_full_identity _ hs, principal_at_zero_identity hs, s_eq]
  simp only [fullZeroMass, ite_true]
  have hh := zeta_full_zero_sum_identity hs 0
  simp only [zetaDamped, ofReal_zero, mul_zero, add_zero] at hh
  linarith

end LiuWang.Proof.Campaign20260915.OriginalRegion
