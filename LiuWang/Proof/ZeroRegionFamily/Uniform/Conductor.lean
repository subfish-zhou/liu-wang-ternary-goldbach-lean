import LiuWang.Proof.ZeroRegionFamily.RealClosure.SourceUniqueness
import Mathlib.Data.Nat.GCD.BigOperators

/-! # 导子缺失素因子与真实同权重Euler费用的联合付款 -/

set_option autoImplicit false
noncomputable section

open Complex Finset
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.ZeroRegionFamily.RealClosure
open scoped Classical

namespace LiuWang.Proof.ZeroRegionFamily.Uniform

theorem primeCost_le_log_div {p : ℕ} (hp : p.Prime) {sigma : ℝ} (hs : 1 < sigma) :
    primeCost p sigma ≤ Real.log p/(p-1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpow : (p : ℝ) ≤ (p : ℝ)^sigma := by
    simpa using Real.rpow_le_rpow_of_exponent_le hp1.le hs.le
  have hge := stechkinSigma_ge hs
  have hpow1 : (p : ℝ) ≤ (p : ℝ)^(stechkinSigma sigma) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hp1.le (hs.le.trans hge)
  rw [primeCost_eq_positive_power hp]
  have hsub : 0 ≤ stechkinK/((p : ℝ)^stechkinSigma sigma-1) :=
    div_nonneg stechkinK_mem.1 (by linarith)
  have hi := one_div_le_one_div_of_le (show 0 < (p : ℝ)-1 by linarith)
    (show (p : ℝ)-1 ≤ (p : ℝ)^sigma-1 by linarith)
  have hm := mul_le_mul_of_nonneg_left (show
    1/((p : ℝ)^sigma-1)-stechkinK/((p : ℝ)^stechkinSigma sigma-1) ≤ 1/((p : ℝ)-1)
      by linarith) (Real.log_natCast_nonneg p)
  simpa only [mul_one_div] using hm

theorem primeCost_small_excess {p : ℕ} (hp : p.Prime) {sigma : ℝ} (hs : 1 < sigma) :
    primeCost p sigma ≤ stechkinConductorCoeff*Real.log p+
      (if p=2 then Real.log 2 else 0)+(if p=3 then Real.log 3/2 else 0) := by
  have hh := primeCost_le_log_div hp hs
  have hn := mul_nonneg conductorCoeff_bounds.1 (Real.log_natCast_nonneg p)
  by_cases h2 : p=2
  · subst p
    norm_num at hh hn ⊢
    linarith
  by_cases h3 : p=3
  · subst p
    norm_num at hh hn ⊢
    linarith
  have hp5 : 5 ≤ p := by
    have ht := hp.two_le
    have h4 : p ≠ 4 := by intro he; subst p; norm_num at hp
    omega
  have hp4 : (4 : ℝ) ≤ (p : ℝ)-1 := by
    have h : (5 : ℝ) ≤ p := by exact_mod_cast hp5
    linarith
  have hi : 1/((p : ℝ)-1) ≤ 1/4 := one_div_le_one_div_of_le (by norm_num) hp4
  have hk : (1/4 : ℝ) ≤ stechkinConductorCoeff := by
    dsimp [stechkinConductorCoeff]
    linarith [stechkinK_le]
  have hm := mul_le_mul_of_nonneg_right (hi.trans hk) (Real.log_natCast_nonneg p)
  simp only [h2, h3, if_false, add_zero]
  simp only [div_eq_mul_inv] at hh hm
  nlinarith

theorem sum_primeCost_le (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime)
    {sigma : ℝ} (hs : 1 < sigma) :
    (∑ p ∈ s, primeCost p sigma) ≤
      stechkinConductorCoeff*(∑ p ∈ s, Real.log p)+Real.log 2+Real.log 3/2 := by
  have hh := sum_le_sum (fun p h => primeCost_small_excess (hp p h) hs)
  have h2 : (∑ p ∈ s, if p=2 then Real.log 2 else 0) ≤ Real.log 2 := by
    simp only [sum_ite_eq']
    split_ifs <;> linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  have h3 : (∑ p ∈ s, if p=3 then Real.log 3/2 else 0) ≤ Real.log 3/2 := by
    simp only [sum_ite_eq']
    split_ifs <;> linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)]
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum] at hh
  linarith

theorem missing_prime_log_mass {q r : ℕ} [NeZero q] (hr0 : r ≠ 0) (hrq : r ∣ q)
    (s : Finset ℕ) (hsub : s ⊆ q.primeFactors) (hmiss : ∀ p ∈ s, ¬p ∣ r) :
    Real.log r+(∑ p ∈ s, Real.log p) ≤ Real.log q := by
  have hpp : ∀ p ∈ s, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hsub hp)
  have hprod : (∏ p ∈ s, p) ∣ q :=
    (prod_dvd_prod_of_subset _ _ _ hsub).trans (Nat.prod_primeFactors_dvd q)
  have hcop : Nat.Coprime (∏ p ∈ s, p) r :=
    Nat.coprime_prod_left_iff.mpr (fun p hp => (hpp p hp).coprime_iff_not_dvd.mpr (hmiss p hp))
  have hdiv := hcop.symm.mul_dvd_of_dvd_of_dvd hrq hprod
  have hp0 : 0 < ∏ p ∈ s, p := prod_pos (fun p hp => (hpp p hp).pos)
  have hle : r*(∏ p ∈ s, p) ≤ q := Nat.le_of_dvd (NeZero.pos q) hdiv
  have he : Real.log (∏ p ∈ s, (p : ℝ))=∑ p ∈ s, Real.log p :=
    Real.log_prod (fun p hp => by exact_mod_cast (hpp p hp).ne_zero)
  rw [← he, ← Real.log_mul (by exact_mod_cast hr0)
    (by rw [← Nat.cast_prod]; exact_mod_cast (ne_of_gt hp0)), ← Nat.cast_prod, ← Nat.cast_mul]
  exact Real.log_le_log (by exact_mod_cast Nat.mul_pos (Nat.pos_of_ne_zero hr0) hp0)
    (by exact_mod_cast hle)

theorem badPrime_support_missing {q p : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hp : p.Prime) (hv : chi.primitiveCharacter p ≠ 0) : ¬p ∣ chi.conductor := by
  intro hd
  have hc : ¬Nat.Coprime p chi.conductor := by
    simpa only [hp.coprime_iff_not_dvd, not_not] using hd
  have hu : ¬IsUnit (p : ZMod chi.conductor) := by
    simpa only [ZMod.isUnit_iff_coprime] using hc
  exact hv (MulChar.map_nonunit _ hu)

theorem conductor_euler_joint {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 < sigma) :
    stechkinConductorCoeff*Real.log chi.conductor+badPrimeCost chi sigma ≤
      stechkinConductorCoeff*Real.log q+Real.log 2+Real.log 3/2 := by
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
  have hh := sum_primeCost_le s hp hs
  have hmul := mul_le_mul_of_nonneg_left hm conductorCoeff_bounds.1
  rw [he]
  nlinarith

theorem small_prime_log_cost_le_two : Real.log 2+Real.log 3/2 ≤ 2 := by
  have h3 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
  linarith [Real.log_two_lt_d9]

theorem principal_euler_joint (q : ℕ) [NeZero q] {sigma : ℝ} (hs : 1 < sigma) :
    principalPrimeCost q sigma ≤ stechkinConductorCoeff*Real.log q+Real.log 2+Real.log 3/2 := by
  have hh := sum_primeCost_le q.primeFactors (fun _ hp => Nat.prime_of_mem_primeFactors hp) hs
  have hl := mul_le_mul_of_nonneg_left (sum_log_primeFactors_le_log q) conductorCoeff_bounds.1
  dsimp [principalPrimeCost]
  linarith

end LiuWang.Proof.ZeroRegionFamily.Uniform
