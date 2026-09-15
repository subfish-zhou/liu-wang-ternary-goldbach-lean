import LiuWang.Proof.Campaign20260915.OriginalRegion.SelectedKernels
import LiuWang.Proof.Campaign20260915.OriginalRegion.SignedEnvelope

/-! Type-checked unpaid goals only; none of the following #checks proves its proposition. -/

set_option autoImplicit false
noncomputable section

open Complex
open scoped BigOperators Classical
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1
open LiuWang.Proof.MultiZeroRepulsion

namespace LiuWang.Proof.Campaign20260915.OriginalRegion

-- Original strict-real, closed-height classification with no preselected source.
#check (∀ (x : ℝ) (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q) (rho : ℂ),
  10 ≤ x → (q : ℝ) ≤ x → rho.re ∈ Set.Ioo (0 : ℝ) 1 →
  |rho.im| ≤ x / q → 1 - 1 / (9.645908801 * Real.log x) < rho.re →
  chi.LFunction rho = 0 → chi ≠ 1 ∧ chi ^ 2 = 1 ∧ rho.im = 0 : Prop)

-- A signed analytic separation certificate, still unpaid in the excluded branches.
#check (∀ (x : ℝ) (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q) (rho : ℂ),
  10 ≤ x → (q : ℝ) ≤ x → rho.re ∈ Set.Ioo (0 : ℝ) 1 →
  |rho.im| ≤ x / q → 1 - 1 / (9.645908801 * Real.log x) < rho.re →
  chi.LFunction rho = 0 → (chi = 1 ∨ chi ^ 2 ≠ 1 ∨ rho.im ≠ 0) →
  ∃ (sigma : ℝ) (s : Finset ℕ) (psi : ℕ → DirichletCharacter ℂ q)
    (t c : ℕ → ℝ) (v : ℕ → Finset ℂ),
    1 < sigma ∧ sigma < 1.15 ∧
    (∀ j ∈ s, 0 ≤ c j) ∧
    (∀ n : ℕ, n ≠ 0 → IsUnit (n : ZMod q) →
      0 ≤ ∑ j ∈ s, c j * (phase (psi j) (t j) n).re) ∧
    (∀ j ∈ s, ∀ tau ∈ v j,
      1 / 2 < tau.re ∧ tau.re < 1 ∧ (psi j).LFunction tau = 0) ∧
    (∑ j ∈ s, c j * signedCost (psi j) sigma (t j)) <
      ∑ j ∈ s, c j * ordinaryMass (psi j) sigma (t j) (v j) : Prop)

-- Concrete diagnostic for the existing polynomial, not an asserted McCurley certificate.
#check (∀ (x : ℝ) (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q) (rho : ℂ),
  10 ≤ x → (q : ℝ) ≤ x → rho.re ∈ Set.Ioo (0 : ℝ) 1 →
  |rho.im| ≤ x / q → 1 - 1 / (9.645908801 * Real.log x) < rho.re →
  chi.LFunction rho = 0 → (chi = 1 ∨ chi ^ 2 ≠ 1 ∨ rho.im ≠ 0) →
  ∃ sigma : ℝ, 1 < sigma ∧ sigma < 1.15 ∧
    14379 * signedCost (1 : DirichletCharacter ℂ q) sigma 0 +
      24480 * signedCost chi sigma rho.im +
      14900 * signedCost (chi ^ 2) sigma (2 * rho.im) +
      6000 * signedCost (chi ^ 3) sigma (3 * rho.im) +
      1250 * signedCost (chi ^ 4) sigma (4 * rho.im) -
      24480 * reflectedKernel sigma rho.im rho < 0 : Prop)

-- The proved strict envelope budget makes this non-strict scalar certificate sufficient.
#check (∀ (x : ℝ) (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q) (rho : ℂ),
  10 ≤ x → (q : ℝ) ≤ x → rho.re ∈ Set.Ioo (0 : ℝ) 1 →
  |rho.im| ≤ x / q → 1 - 1 / (9.645908801 * Real.log x) < rho.re →
  chi.LFunction rho = 0 → (chi = 1 ∨ chi ^ 2 ≠ 1 ∨ rho.im ≠ 0) →
  ∃ sigma : ℝ, 1 < sigma ∧ sigma < 1.15 ∧
    14379 * signedEnvelope (1 : DirichletCharacter ℂ q) sigma 0 +
      24480 * signedEnvelope chi sigma rho.im +
      14900 * signedEnvelope (chi ^ 2) sigma (2 * rho.im) +
      6000 * signedEnvelope (chi ^ 3) sigma (3 * rho.im) +
      1250 * signedEnvelope (chi ^ 4) sigma (4 * rho.im) ≤
      24480 * reflectedKernel sigma rho.im rho : Prop)

end LiuWang.Proof.Campaign20260915.OriginalRegion
