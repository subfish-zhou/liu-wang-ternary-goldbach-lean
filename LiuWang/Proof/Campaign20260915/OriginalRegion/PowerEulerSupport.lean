import LiuWang.Proof.Campaign20260915.OriginalRegion.LecturePolynomial
import LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.EulerShare

/-! Simultaneous missing-prime support of consecutive powers of a primitive character. -/

set_option autoImplicit false
noncomputable section

open Complex Finset
open scoped BigOperators Classical
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.ZeroRegionFamily.Uniform
open LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation

namespace LiuWang.Proof.Campaign20260915.OriginalRegion

theorem consecutive_power_corrections_disjoint {q p : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hc : chi.IsPrimitive)
    (hp : p.Prime) (hpq : p ∣ q) (k : ℕ) :
    (chi ^ k).primitiveCharacter p = 0 ∨
      (chi ^ (k + 1)).primitiveCharacter p = 0 := by
  by_contra hh
  push Not at hh
  have h0 := badPrime_support_missing (chi ^ k) hp hh.1
  have h1 := badPrime_support_missing (chi ^ (k + 1)) hp hh.2
  have he : chi ^ (k + 1) * (chi ^ k)⁻¹ = chi := by rw [pow_succ]; group
  have hd := DirichletCharacter.conductor_mul_dvd_lcm_conductor
    (chi ^ (k + 1)) (chi ^ k)⁻¹
  rw [he, hc, DirichletCharacter.conductor_inv] at hd
  have hmul := hpq.trans (hd.trans (Nat.lcm_dvd_mul _ _))
  exact (hp.dvd_mul.mp hmul).elim h1 h0

theorem lecture_badPrimeCost_joint {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hc : chi.IsPrimitive)
    {sigma : ℝ} (hs : 1 < sigma) :
    11.67618784 * badPrimeCost (chi ^ 2) sigma +
      4.7568 * badPrimeCost (chi ^ 3) sigma + badPrimeCost (chi ^ 4) sigma ≤
      12.67618784 * principalPrimeCost q sigma := by
  simp only [badPrimeCost, principalPrimeCost, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hpq
  have hp := Nat.prime_of_mem_primeFactors hpq
  have hd := Nat.dvd_of_mem_primeFactors hpq
  have h23 := consecutive_power_corrections_disjoint chi hc hp hd 2
  have h34 := consecutive_power_corrections_disjoint chi hc hp hd 3
  have hcost := primeCost_nonneg hp hs
  by_cases h3 : (chi ^ 3).primitiveCharacter p = 0
  · simp only [h3, ite_true, mul_zero, add_zero]
    split_ifs <;> linarith
  · have h2 : (chi ^ 2).primitiveCharacter p = 0 := h23.resolve_right h3
    have h4 : (chi ^ 4).primitiveCharacter p = 0 := h34.resolve_left h3
    simp only [h2, h3, h4, ite_true, if_false, mul_zero, zero_add, add_zero]
    linarith

theorem conductor_euler_support_share {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {sigma : ℝ} (hs : 1 < sigma) :
    stechkinConductorCoeff * Real.log chi.conductor + badPrimeCost chi sigma ≤
      stechkinConductorCoeff * Real.log q + (14379 / 22150) * badPrimeCost chi sigma := by
  let s := q.primeFactors.filter (fun p : ℕ => chi.primitiveCharacter p ≠ 0)
  have hsub : s ⊆ q.primeFactors := filter_subset _ _
  have hp : ∀ p ∈ s, p.Prime := fun p h => Nat.prime_of_mem_primeFactors (hsub h)
  have he : badPrimeCost chi sigma = ∑ p ∈ s, primeCost p sigma := by
    unfold badPrimeCost s
    rw [sum_filter]
    apply sum_congr rfl
    intro p _
    split_ifs <;> simp_all
  have hm := missing_prime_log_mass chi.conductor_ne_zero chi.conductor_dvd_level s hsub
    (fun p h => badPrime_support_missing chi (hp p h) (mem_filter.mp h).2)
  have hsum := sum_le_sum (fun p h => primeCost_share (hp p h) hs)
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at hsum
  have hmul := mul_le_mul_of_nonneg_left hm conductorCoeff_bounds.1
  rw [he]
  linarith

theorem lecture_conductor_euler_joint {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hc : chi.IsPrimitive)
    {sigma : ℝ} (hs : 1 < sigma) :
    11.67618784 * (stechkinConductorCoeff * Real.log (chi ^ 2).conductor +
      badPrimeCost (chi ^ 2) sigma) +
    4.7568 * (stechkinConductorCoeff * Real.log (chi ^ 3).conductor +
      badPrimeCost (chi ^ 3) sigma) +
    (stechkinConductorCoeff * Real.log (chi ^ 4).conductor + badPrimeCost (chi ^ 4) sigma) ≤
      17.43298784 * stechkinConductorCoeff * Real.log q +
        9 * principalPrimeCost q sigma := by
  have h2 := conductor_euler_support_share (chi ^ 2) hs
  have h3 := conductor_euler_support_share (chi ^ 3) hs
  have h4 := conductor_euler_support_share (chi ^ 4) hs
  have hj := lecture_badPrimeCost_joint chi hc hs
  have hp := principalPrimeCost_nonneg q hs
  nlinarith

theorem lecture_principal_euler_reserve {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hc : chi.IsPrimitive)
    {sigma : ℝ} (hs : 1 < sigma) :
    11.67618784 * (stechkinConductorCoeff * Real.log (chi ^ 2).conductor +
      badPrimeCost (chi ^ 2) sigma) +
    4.7568 * (stechkinConductorCoeff * Real.log (chi ^ 3).conductor +
      badPrimeCost (chi ^ 3) sigma) +
    (stechkinConductorCoeff * Real.log (chi ^ 4).conductor + badPrimeCost (chi ^ 4) sigma) -
      11.1859355312082048 * principalPrimeCost q sigma ≤
      17.43298784 * stechkinConductorCoeff * Real.log q -
        2 * principalPrimeCost q sigma := by
  have hh := lecture_conductor_euler_joint chi hc hs
  have hp := principalPrimeCost_nonneg q hs
  linarith

end LiuWang.Proof.Campaign20260915.OriginalRegion
