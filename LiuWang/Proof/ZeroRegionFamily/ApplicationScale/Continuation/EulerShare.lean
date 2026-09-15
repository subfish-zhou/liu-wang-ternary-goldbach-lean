import LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Consumer

/-! # 同权重Euler费用可由主实轴的一份费用支付 -/

set_option autoImplicit false
noncomputable section

open Complex Finset
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.ZeroRegionFamily.Uniform
open scoped Classical

namespace LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation

theorem stechkinK_tight : 447/1000 ≤ stechkinK ∧ stechkinK ≤ 2237/5000 := by
  have hp : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  dsimp [stechkinK]
  constructor
  · apply (le_div_iff₀ hp).mpr
    nlinarith
  · apply (div_le_iff₀ hp).mpr
    nlinarith

theorem sigma_shift_five_eighths {sigma : ℝ} (hs : 1 < sigma) :
    stechkinSigma sigma ≤ sigma+5/8 := by
  have hsq := Real.sq_sqrt (show 0 ≤ 1+4*sigma^2 by positivity)
  have hp := Real.sqrt_nonneg (1+4*sigma^2)
  dsimp [stechkinSigma]
  nlinarith

theorem two_rpow_five_eighths : (2 : ℝ)^(5/8 : ℝ) ≤ 31/20 := by
  apply (Real.rpow_le_rpow_iff (by positivity) (by norm_num) (by norm_num : (0 : ℝ) < 8)).mp
  rw [← Real.rpow_mul (by norm_num)]
  norm_num

theorem primeCost_le_63_80_log {p : ℕ} (hp : p.Prime) {sigma : ℝ} (hs : 1 < sigma) :
    primeCost p sigma ≤ (63/80)*Real.log p := by
  by_cases h2 : p=2
  · subst p
    let a : ℝ := (2 : ℝ)^sigma
    let b : ℝ := (2 : ℝ)^(stechkinSigma sigma)
    have ha : 2 ≤ a := by
      simpa [a] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hs.le
    have hb : 2 ≤ b := by
      simpa [b] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (hs.le.trans (stechkinSigma_ge hs))
    have hab : b ≤ (31/20)*a := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (sigma_shift_five_eighths hs)
      rw [Real.rpow_add (by norm_num)] at h
      exact h.trans (by
        simpa [a, mul_comm] using mul_le_mul_of_nonneg_left two_rpow_five_eighths
          (Real.rpow_nonneg (by norm_num) sigma))
    have hsmall : 447/1000/((31/20)*a-1) ≤ stechkinK/(b-1) := by
      apply div_le_div₀ stechkinK_mem.1 stechkinK_tight.1 (by linarith) (by linarith)
    have hpaid : 1/(a-1)-(447/1000)/((31/20)*a-1) ≤ 63/80 := by
      rw [div_sub_div _ _ (by linarith : a-1 ≠ 0) (by linarith : (31/20)*a-1 ≠ 0)]
      apply (div_le_iff₀ (mul_pos (by linarith) (by linarith))).mpr
      nlinarith [sq_nonneg (a-2)]
    rw [primeCost_eq_positive_power (by norm_num : Nat.Prime 2)]
    have h := mul_le_mul_of_nonneg_left (show 1/(a-1)-stechkinK/(b-1) ≤ 63/80 by linarith)
      (Real.log_natCast_nonneg 2)
    simpa [a, b, mul_comm] using h
  · have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hp2 : (2 : ℝ) ≤ (p : ℝ)-1 := by
      have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      linarith
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2
    have hh := primeCost_le_log_div hp hs
    have hm := mul_le_mul_of_nonneg_right hi (Real.log_natCast_nonneg p)
    simp only [div_eq_mul_inv] at hh hm
    nlinarith [Real.log_natCast_nonneg p]

theorem primeCost_share {p : ℕ} (hp : p.Prime) {sigma : ℝ} (hs : 1 < sigma) :
    primeCost p sigma ≤ stechkinConductorCoeff*Real.log p+
      (14379/22150)*primeCost p sigma := by
  have h := mul_le_mul_of_nonneg_left (primeCost_le_63_80_log hp hs)
    (by norm_num : (0 : ℝ) ≤ 7771/22150)
  have hk : (2763/10000 : ℝ) ≤ stechkinConductorCoeff := by
    dsimp [stechkinConductorCoeff]
    linarith [stechkinK_tight.2]
  have hh := mul_le_mul_of_nonneg_right hk (Real.log_natCast_nonneg p)
  nlinarith [Real.log_natCast_nonneg p]

theorem conductor_euler_share {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 < sigma) :
    stechkinConductorCoeff*Real.log chi.conductor+badPrimeCost chi sigma ≤
      stechkinConductorCoeff*Real.log q+(14379/22150)*principalPrimeCost q sigma := by
  let s := q.primeFactors.filter (fun p : ℕ => chi.primitiveCharacter p ≠ 0)
  have hsub : s ⊆ q.primeFactors := filter_subset _ _
  have hp : ∀ p ∈ s, p.Prime := fun _ h => Nat.prime_of_mem_primeFactors (hsub h)
  have he : badPrimeCost chi sigma=∑ p ∈ s, primeCost p sigma := by
    unfold badPrimeCost s
    rw [sum_filter]
    apply sum_congr rfl
    intro p _
    split_ifs <;> simp_all
  have hm := missing_prime_log_mass chi.conductor_ne_zero chi.conductor_dvd_level s hsub
    (fun p h => badPrime_support_missing chi (hp p h) (mem_filter.mp h).2)
  have hsum := sum_le_sum (fun p h => primeCost_share (hp p h) hs)
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at hsum
  have hsubsum : (∑ p ∈ s, primeCost p sigma) ≤ principalPrimeCost q sigma :=
    sum_le_sum_of_subset_of_nonneg hsub (fun p h _ => primeCost_nonneg (Nat.prime_of_mem_primeFactors h) hs)
  have hmul := mul_le_mul_of_nonneg_left hm conductorCoeff_bounds.1
  rw [he]
  linarith

theorem principal_euler_share (q : ℕ) [NeZero q] {sigma : ℝ} (hs : 1 < sigma) :
    principalPrimeCost q sigma ≤ stechkinConductorCoeff*Real.log q+
      (14379/22150)*principalPrimeCost q sigma := by
  have hh := sum_le_sum (s := q.primeFactors)
    (fun p h => primeCost_share (Nat.prime_of_mem_primeFactors h) hs)
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at hh
  have hl := mul_le_mul_of_nonneg_left (sum_log_primeFactors_le_log q) conductorCoeff_bounds.1
  dsimp [principalPrimeCost]
  linarith

end LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation
