import LiuWang.Proof.NearOneDensity.EulerBudget
import LiuWang.Proof.MultiZeroRepulsion.Continuation.PrimitivePair

/-! Same-weight finite Euler costs on the full sigma interval used by the source. -/

set_option autoImplicit false
noncomputable section
open scoped Classical
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.NearOneDensity

namespace LiuWang.Proof.MultiZeroRepulsion.Continuation

theorem general_prime_rational {p : ℕ} (hp : p.Prime) {sigma : ℝ}
    (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) :
    primeCost p sigma ≤ Real.log p *
      (1 / ((p : ℝ) - 1) - stechkinK / ((p : ℝ) ^ 2 - 1)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have ha : (p : ℝ) ≤ (p : ℝ) ^ sigma := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hp1.le hs.le
  have ht := stechkinSigma_bounds hs hs1
  have ht0 : 1 < (p : ℝ) ^ stechkinSigma sigma :=
    Real.one_lt_rpow hp1 (by linarith [ht.1])
  have ht2 : (p : ℝ) ^ stechkinSigma sigma ≤ (p : ℝ) ^ 2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hp1.le
      (show stechkinSigma sigma ≤ 2 by linarith [ht.2])
  have hrec := one_div_le_one_div_of_le (show 0 < (p : ℝ) - 1 by linarith)
    (show (p : ℝ) - 1 ≤ (p : ℝ) ^ sigma - 1 by linarith)
  have hsub := mul_le_mul_of_nonneg_left
    (one_div_le_one_div_of_le (show 0 < (p : ℝ) ^ stechkinSigma sigma - 1 by linarith)
      (show (p : ℝ) ^ stechkinSigma sigma - 1 ≤ (p : ℝ) ^ 2 - 1 by linarith)) stechkinK_mem.1
  rw [primeCost_eq_positive_power hp]
  apply mul_le_mul_of_nonneg_left _ (Real.log_natCast_nonneg p)
  simpa only [mul_one_div] using sub_le_sub hrec hsub

theorem general_prime_log {p : ℕ} (hp : p.Prime) {sigma : ℝ}
    (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) :
    primeCost p sigma ≤ stechkinConductorCoeff * Real.log p +
      (if p = 2 then 161 / 400 else 0) + (if p = 3 then 297 / 1600 else 0) := by
  have hb := general_prime_rational hp hs hs1
  have hk : 11 / 40 ≤ stechkinConductorCoeff := by
    unfold stechkinConductorCoeff
    linarith [stechkinK_le]
  by_cases h2 : p = 2
  · subst p
    norm_num at hb ⊢
    have hlog : Real.log 2 ≤ 7 / 10 := by linarith [Real.log_two_lt_d9]
    have hprod := mul_le_mul_of_nonneg_right stechkinK_le (Real.log_natCast_nonneg 2)
    have hprod' := mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 23 / 40)
    unfold stechkinConductorCoeff
    nlinarith
  by_cases h3 : p = 3
  · subst p
    norm_num at hb ⊢
    have hlog : Real.log 3 ≤ 11 / 10 := by linarith [Real.log_three_lt_d9]
    have hprod := mul_le_mul_of_nonneg_right stechkinK_le (Real.log_natCast_nonneg 3)
    have hprod' := mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 27 / 160)
    unfold stechkinConductorCoeff
    nlinarith
  · simp only [if_neg h2, if_neg h3, add_zero]
    have hp5 : (5 : ℝ) ≤ p := by exact_mod_cast hp.five_le_of_ne_two_of_ne_three h2 h3
    have hrec := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4)
      (show 4 ≤ (p : ℝ) - 1 by linarith)
    have hpos : 0 ≤ stechkinK / ((p : ℝ) ^ 2 - 1) :=
      div_nonneg stechkinK_mem.1 (by nlinarith)
    have hh := mul_le_mul_of_nonneg_left (show
      1 / ((p : ℝ) - 1) - stechkinK / ((p : ℝ) ^ 2 - 1) ≤ stechkinConductorCoeff by linarith)
      (Real.log_natCast_nonneg p)
    nlinarith

theorem general_finite_prime_cost (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime) {sigma : ℝ}
    (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) :
    (∑ p ∈ s, primeCost p sigma) ≤
      stechkinConductorCoeff * (∑ p ∈ s, Real.log p) + 941 / 1600 := by
  have hh := Finset.sum_le_sum (fun p h => general_prime_log (hp p h) hs hs1)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hh
  have h2 : (∑ p ∈ s, if p = 2 then (161 / 400 : ℝ) else 0) ≤ 161 / 400 := by
    simp only [Finset.sum_ite_eq']; split <;> norm_num
  have h3 : (∑ p ∈ s, if p = 3 then (297 / 1600 : ℝ) else 0) ≤ 297 / 1600 := by
    simp only [Finset.sum_ite_eq']; split <;> norm_num
  linarith

theorem general_badPrimeCost {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) :
    badPrimeCost chi sigma ≤
      stechkinConductorCoeff * (Real.log q - Real.log chi.conductor) + 941 / 1600 := by
  let s := q.primeFactors.filter (fun p : ℕ => chi.primitiveCharacter p ≠ 0)
  have hsub : s ⊆ q.primeFactors := Finset.filter_subset _ _
  have hc (p) (hp : p ∈ s) : p.Coprime chi.conductor :=
    (ZMod.isUnit_iff_coprime p chi.conductor).mp
      (MulChar.apply_ne_zero_iff.mp (Finset.mem_filter.mp hp).2)
  have hl := disjoint_prime_support_log (NeZero.pos q) (Nat.pos_of_ne_zero chi.conductor_ne_zero)
    chi.conductor_dvd_level s hsub hc
  have hm := mul_le_mul_of_nonneg_left hl conductorCoeff_bounds.1
  have hh := general_finite_prime_cost s (fun p hp => Nat.prime_of_mem_primeFactors (hsub hp)) hs hs1
  have he : badPrimeCost chi sigma = ∑ p ∈ s, primeCost p sigma := by
    simp only [badPrimeCost, s, Finset.sum_filter, ne_eq, ite_not]
  rw [he]
  nlinarith

theorem general_nonprincipal_cost {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (t : ℝ) :
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK t ≤
      stechkinConductorCoeff * (Real.log q + Real.log (max 1 |t|) - Real.log Real.pi) +
        4 / 15 + 941 / 1600 := by
  have hh := imprimitive_damped_bound chi hc hs hs1 t
  have he := general_badPrimeCost chi hs hs1
  linarith

end LiuWang.Proof.MultiZeroRepulsion.Continuation
