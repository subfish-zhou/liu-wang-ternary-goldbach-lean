import LiuWang.Proof.MultiZeroRepulsion.Continuation.GeneralEulerCost

set_option autoImplicit false
noncomputable section

open scoped Classical
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.NearOneDensity
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1

theorem lwd_kappa_bounds :
    0.2763932 ≤ stechkinConductorCoeff ∧ stechkinConductorCoeff ≤ 0.2764 ∧
      0.4472 ≤ stechkinK := by
  have hr : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hr2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hk : stechkinK = Real.sqrt 5 / 5 := by
    dsimp [stechkinK]
    apply (div_eq_div_iff hr.ne' (by norm_num)).mpr
    nlinarith
  rw [stechkinConductorCoeff, hk]
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem lwd_sigma_shift {sigma : ℝ} (hs : 1 < sigma) :
    stechkinSigma sigma ≤ sigma + 34 / 55 := by
  have ht := stechkinSigma_ge hs
  have he := stechkinSigma_equation sigma
  nlinarith

theorem lwd_fixed_prime_cost {p : ℕ} (hp : p.Prime) {sigma B c : ℝ}
    (hs : 1 < sigma) (hB : 0 < B) (hc : 0 ≤ c)
    (hpow : (p : ℝ) ^ (34 / 55 : ℝ) ≤ B)
    (hvalue : 0 ≤ c * ((p : ℝ) - 1) * (B * p - 1) -
      (B * p - 1) + 0.4472 * ((p : ℝ) - 1))
    (hslope : 0 ≤ 2 * c * B * p - c * (B + 1) - B + 0.4472) :
    primeCost p sigma ≤ c * Real.log p := by
  let a : ℝ := (p : ℝ) ^ sigma
  let b : ℝ := (p : ℝ) ^ stechkinSigma sigma
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have ha : (p : ℝ) ≤ a := by
    simpa [a] using Real.rpow_le_rpow_of_exponent_le hp1.le hs.le
  have hb : (p : ℝ) ≤ b := by
    simpa [b] using Real.rpow_le_rpow_of_exponent_le hp1.le
      (hs.le.trans (stechkinSigma_ge hs))
  have hba : b ≤ B * a := by
    have h := Real.rpow_le_rpow_of_exponent_le hp1.le (lwd_sigma_shift hs)
    rw [Real.rpow_add (by linarith : (0 : ℝ) < p)] at h
    exact h.trans (by
      simpa [a, mul_comm] using mul_le_mul_of_nonneg_left hpow
        (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ p) sigma))
  have hsmall : 0.4472 / (B * a - 1) ≤ stechkinK / (b - 1) :=
    div_le_div₀ stechkinK_mem.1 lwd_kappa_bounds.2.2 (by linarith) (by linarith)
  have hpaid : 1 / (a - 1) - 0.4472 / (B * a - 1) ≤ c := by
    rw [div_sub_div _ _ (by linarith : a - 1 ≠ 0) (by linarith : B * a - 1 ≠ 0)]
    apply (div_le_iff₀ (mul_pos (by linarith) (by linarith))).mpr
    have hquad := mul_nonneg (mul_nonneg hc hB.le) (sq_nonneg (a - p))
    have hlin := mul_nonneg hslope (show 0 ≤ a - p by linarith)
    nlinarith
  rw [primeCost_eq_positive_power hp]
  have hh := mul_le_mul_of_nonneg_left
    (show 1 / (a - 1) - stechkinK / (b - 1) ≤ c by linarith)
    (Real.log_natCast_nonneg p)
  simpa only [a, b, mul_comm] using hh

theorem lwd_prime_two {sigma : ℝ} (hs : 1 < sigma) :
    primeCost 2 sigma ≤ 0.784 * Real.log 2 := by
  apply lwd_fixed_prime_cost (by norm_num) hs (B := 30703 / 20000)
  · norm_num
  · norm_num
  · apply (Real.rpow_le_rpow_iff (by positivity) (by norm_num)
      (by norm_num : (0 : ℝ) < 55)).mp
    rw [← Real.rpow_mul (by norm_num)]
    norm_num
  all_goals norm_num

theorem lwd_prime_three {sigma : ℝ} (hs : 1 < sigma) :
    primeCost 3 sigma ≤ 0.4091 * Real.log 3 := by
  apply lwd_fixed_prime_cost (by norm_num) hs (B := 1973 / 1000)
  · norm_num
  · norm_num
  · apply (Real.rpow_le_rpow_iff (by positivity) (by norm_num)
      (by norm_num : (0 : ℝ) < 55)).mp
    rw [← Real.rpow_mul (by norm_num)]
    norm_num
  all_goals norm_num

theorem lwd_prime_cost_le_log_div {p : ℕ} (hp : p.Prime) {sigma : ℝ} (hs : 1 < sigma) :
    primeCost p sigma ≤ Real.log p / ((p : ℝ) - 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have ha : (p : ℝ) ≤ (p : ℝ) ^ sigma := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hp1.le hs.le
  have hb := Real.one_lt_rpow hp1
    (show 0 < stechkinSigma sigma by linarith [stechkinSigma_ge hs])
  have hi := one_div_le_one_div_of_le (by linarith : (0 : ℝ) < p - 1)
    (by linarith : (p : ℝ) - 1 ≤ (p : ℝ) ^ sigma - 1)
  have hn : 0 ≤ stechkinK / ((p : ℝ) ^ stechkinSigma sigma - 1) :=
    div_nonneg stechkinK_mem.1 (by linarith)
  rw [primeCost_eq_positive_power hp]
  have hh := mul_le_mul_of_nonneg_left
    (show 1 / ((p : ℝ) ^ sigma - 1) -
      stechkinK / ((p : ℝ) ^ stechkinSigma sigma - 1) ≤ 1 / ((p : ℝ) - 1) by linarith)
    (Real.log_natCast_nonneg p)
  simpa only [mul_one_div] using hh

theorem lwd_prime_allowance {p : ℕ} (hp : p.Prime) {sigma : ℝ} (hs : 1 < sigma) :
    primeCost p sigma ≤ stechkinConductorCoeff * Real.log p +
      (if p = 2 then (0.784 - stechkinConductorCoeff) * Real.log 2 else 0) +
      (if p = 3 then (0.4091 - stechkinConductorCoeff) * Real.log 3 else 0) := by
  by_cases h2 : p = 2
  · subst p
    simp only [ite_true, show (2 : ℕ) ≠ 3 by decide, ite_false, add_zero]
    nlinarith only [lwd_prime_two hs]
  by_cases h3 : p = 3
  · subst p
    simp only [show (3 : ℕ) ≠ 2 by decide, ite_false, ite_true, add_zero]
    nlinarith only [lwd_prime_three hs]
  · simp only [if_neg h2, if_neg h3, add_zero]
    have hp5 : (5 : ℝ) ≤ p := by exact_mod_cast hp.five_le_of_ne_two_of_ne_three h2 h3
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4)
      (by linarith : (4 : ℝ) ≤ p - 1)
    have hm := mul_le_mul_of_nonneg_right
      (hi.trans (by linarith [lwd_kappa_bounds.1] : (1 / 4 : ℝ) ≤ stechkinConductorCoeff))
      (Real.log_natCast_nonneg p)
    exact (lwd_prime_cost_le_log_div hp hs).trans (by
      simpa only [one_div_mul_eq_div] using hm)

theorem lwd_2_3_finite (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime)
    {sigma : ℝ} (hs : 1 < sigma) :
    (∑ p ∈ s, primeCost p sigma) ≤
      stechkinConductorCoeff * (∑ p ∈ s, Real.log p) + 0.4977 := by
  have hh := Finset.sum_le_sum (fun p h => lwd_prime_allowance (hp p h) hs)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hh
  have h2 : (∑ p ∈ s, if p = 2 then (0.784 - stechkinConductorCoeff) * Real.log 2 else 0) ≤
      (0.784 - stechkinConductorCoeff) * Real.log 2 := by
    simp only [Finset.sum_ite_eq']
    split
    · exact le_rfl
    · exact mul_nonneg (by linarith [lwd_kappa_bounds.2.1]) (Real.log_natCast_nonneg 2)
  have h3 : (∑ p ∈ s, if p = 3 then (0.4091 - stechkinConductorCoeff) * Real.log 3 else 0) ≤
      (0.4091 - stechkinConductorCoeff) * Real.log 3 := by
    simp only [Finset.sum_ite_eq']
    split
    · exact le_rfl
    · exact mul_nonneg (by linarith [lwd_kappa_bounds.2.1]) (Real.log_natCast_nonneg 3)
  have hc2 := mul_le_mul
    (show 0.784 - stechkinConductorCoeff ≤ 0.784 - 0.2763932 by linarith [lwd_kappa_bounds.1])
    Real.log_two_lt_d9.le (Real.log_natCast_nonneg 2) (by norm_num)
  have hc3 := mul_le_mul
    (show 0.4091 - stechkinConductorCoeff ≤ 0.4091 - 0.2763932 by linarith [lwd_kappa_bounds.1])
    Real.log_three_lt_d9.le (Real.log_natCast_nonneg 3) (by norm_num)
  linarith

theorem lwd_2_3 (q : ℕ) [NeZero q] {sigma : ℝ} (hs : 1 < sigma) :
    principalPrimeCost q sigma ≤ stechkinConductorCoeff * Real.log q + 0.4977 := by
  have hh := lwd_2_3_finite q.primeFactors (fun _ h => Nat.prime_of_mem_primeFactors h) hs
  have hl := mul_le_mul_of_nonneg_left (sum_log_primeFactors_le_log q) conductorCoeff_bounds.1
  exact hh.trans (add_le_add hl le_rfl)

theorem lwd_2_9 {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 < sigma) :
    badPrimeCost chi sigma ≤
      stechkinConductorCoeff * (Real.log q - Real.log chi.conductor) + 0.4977 := by
  let s := q.primeFactors.filter (fun p : ℕ => chi.primitiveCharacter p ≠ 0)
  have hsub : s ⊆ q.primeFactors := Finset.filter_subset _ _
  have hc (p) (hp : p ∈ s) : p.Coprime chi.conductor :=
    (ZMod.isUnit_iff_coprime p chi.conductor).mp
      (MulChar.apply_ne_zero_iff.mp (Finset.mem_filter.mp hp).2)
  have hl := disjoint_prime_support_log (NeZero.pos q) (Nat.pos_of_ne_zero chi.conductor_ne_zero)
    chi.conductor_dvd_level s hsub hc
  have hm := mul_le_mul_of_nonneg_left hl conductorCoeff_bounds.1
  have hh := lwd_2_3_finite s (fun p hp => Nat.prime_of_mem_primeFactors (hsub hp)) hs
  have he : badPrimeCost chi sigma = ∑ p ∈ s, primeCost p sigma := by
    simp only [badPrimeCost, s, Finset.sum_filter, ne_eq, ite_not]
  rw [he]
  nlinarith

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1
