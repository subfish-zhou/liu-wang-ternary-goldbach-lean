import LiuWang.Proof.ZeroRegionFamily.LowOrderClosure.Consumer

/-! # 小素数仅支付超过导子节省的部分 -/

set_option autoImplicit false
noncomputable section

open Complex Finset
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.ZeroRegionFamily.Uniform
open scoped Classical

namespace LiuWang.Proof.ZeroRegionFamily.ApplicationScale

theorem conductorCoeff_lower : 11/40 ≤ stechkinConductorCoeff := by
  dsimp [stechkinConductorCoeff]
  linarith [stechkinK_le]

theorem primeCost_excess {p : ℕ} (hp : p.Prime) {sigma : ℝ} (hs : 1 < sigma) :
    primeCost p sigma ≤ stechkinConductorCoeff*Real.log p+
      (if p=2 then (29/40)*Real.log 2 else 0)+
      (if p=3 then (9/40)*Real.log 3 else 0) := by
  have hh := primeCost_le_log_div hp hs
  have hk := mul_le_mul_of_nonneg_right conductorCoeff_lower (Real.log_natCast_nonneg p)
  by_cases h2 : p=2
  · subst p; norm_num at hh hk ⊢; linarith
  by_cases h3 : p=3
  · subst p; norm_num at hh hk ⊢; linarith
  have hp5 : 5 ≤ p := by
    have ht := hp.two_le
    have h4 : p ≠ 4 := by intro h; subst p; norm_num at hp
    omega
  have hp4 : (4 : ℝ) ≤ (p : ℝ)-1 := by
    have h : (5 : ℝ) ≤ p := by exact_mod_cast hp5
    linarith
  have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hp4
  have hm := mul_le_mul_of_nonneg_right hi (Real.log_natCast_nonneg p)
  simp only [h2, h3, if_false, add_zero]
  simp only [div_eq_mul_inv] at hh hm
  nlinarith [Real.log_natCast_nonneg p]

theorem sum_primeCost_refined (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime)
    {sigma : ℝ} (hs : 1 < sigma) :
    (∑ p ∈ s, primeCost p sigma) ≤ stechkinConductorCoeff*(∑ p ∈ s, Real.log p)+151/200 := by
  have hh := sum_le_sum (fun p h => primeCost_excess (hp p h) hs)
  have h2 : (∑ p ∈ s, if p=2 then (29/40)*Real.log 2 else 0) ≤ (29/40)*Real.log 2 := by
    simp only [sum_ite_eq']
    split_ifs
    · exact le_rfl
    · positivity
  have h3 : (∑ p ∈ s, if p=3 then (9/40)*Real.log 3 else 0) ≤ (9/40)*Real.log 3 := by
    simp only [sum_ite_eq']
    split_ifs
    · exact le_rfl
    · positivity
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum] at hh
  linarith [Real.log_two_lt_d9, Real.log_three_lt_d9]

theorem conductor_euler_refined {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 < sigma) :
    stechkinConductorCoeff*Real.log chi.conductor+badPrimeCost chi sigma ≤
      stechkinConductorCoeff*Real.log q+151/200 := by
  let s := q.primeFactors.filter (fun p : ℕ => chi.primitiveCharacter p ≠ 0)
  have hsub : s ⊆ q.primeFactors := filter_subset _ _
  have he : badPrimeCost chi sigma=∑ p ∈ s, primeCost p sigma := by
    unfold badPrimeCost s
    rw [sum_filter]
    apply sum_congr rfl
    intro p _
    split_ifs <;> simp_all
  have hp : ∀ p ∈ s, p.Prime := fun p h => Nat.prime_of_mem_primeFactors (hsub h)
  have hm := missing_prime_log_mass chi.conductor_ne_zero chi.conductor_dvd_level s hsub
    (fun p h => badPrime_support_missing chi (hp p h) (mem_filter.mp h).2)
  have hh := sum_primeCost_refined s hp hs
  have hmul := mul_le_mul_of_nonneg_left hm conductorCoeff_bounds.1
  rw [he]
  nlinarith

theorem principal_euler_refined (q : ℕ) [NeZero q] {sigma : ℝ} (hs : 1 < sigma) :
    principalPrimeCost q sigma ≤ stechkinConductorCoeff*Real.log q+151/200 := by
  have hh := sum_primeCost_refined q.primeFactors (fun _ hp => Nat.prime_of_mem_primeFactors hp) hs
  have hl := mul_le_mul_of_nonneg_left (sum_log_primeFactors_le_log q) conductorCoeff_bounds.1
  dsimp [principalPrimeCost]
  linarith

end LiuWang.Proof.ZeroRegionFamily.ApplicationScale
