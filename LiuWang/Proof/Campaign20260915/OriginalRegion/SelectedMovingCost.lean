import LiuWang.Proof.Campaign20260915.OriginalRegion.MovingBudget

/-! The fully selected signed budget, retaining the jointly paid Euler reserve. -/

set_option autoImplicit false
noncomputable section

open Complex
open scoped Classical BigOperators
open LiuWang.Proof.MultiZeroRepulsion
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.ZeroRegionFamily.RealClosure LiuWang.Proof.ZeroRegionFamily.Uniform
open LiuWang.Proof.ZeroRegionFamily.ApplicationScale
open LiuWang.Proof.ChebyshevBound.HighHeight

namespace LiuWang.Proof.Campaign20260915.OriginalRegion

theorem primitive_badPrimeCost {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hp : chi.IsPrimitive) (sigma : ℝ) : badPrimeCost chi sigma = 0 := by
  unfold badPrimeCost
  apply Finset.sum_eq_zero
  intro p h
  have hz : chi.primitiveCharacter p = 0 := by
    by_contra hn
    have hh := badPrime_support_missing chi (Nat.prime_of_mem_primeFactors h) hn
    rw [hp] at hh
    exact hh (Nat.dvd_of_mem_primeFactors h)
  simp only [hz, if_true]

theorem signedCost_le_harmonicBound {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {sigma : ℝ}
    (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (t : ℝ) :
    signedCost chi sigma t ≤ harmonicBound chi sigma t :=
  signedCost_le_ordinaryCost chi hs hs1 t

theorem signed_real_principal_strong {q : ℕ} [NeZero q] {sigma : ℝ}
    (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) :
    signedCost (1 : DirichletCharacter ℂ q) sigma 0 ≤
      1 / (sigma - 1) - 3 / 4 - principalPrimeCost q sigma := by
  rw [signed_principal_real_cost hs]
  linarith [poleDifference_real_le hs hs1, shiftedGamma_real_bound hs hs1]

theorem lecture_signed_moving_envelope {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (t : ℝ) :
    (∑ j : Fin 5, lectureCoefficients j * signedCost (chi ^ (j : ℕ)) sigma ((j : ℝ) * t)) +
      1 + 2 * principalPrimeCost q sigma ≤
      11.1859355312082048 / (sigma - 1) +
        36.506331844352 * stechkinConductorCoeff * (Real.log q + Real.log (max 1 |t|)) +
        11.67618784 * harmonicPole (chi ^ 2) sigma (2 * t) +
        4.7568 * harmonicPole (chi ^ 3) sigma (3 * t) +
        harmonicPole (chi ^ 4) sigma (4 * t) := by
  have hmain := signedCost_le_harmonicBound chi hs hs1 t
  simp only [harmonicBound, if_neg hc, primitive_badPrimeCost chi hp, add_zero] at hmain
  rw [show chi.conductor = q from hp] at hmain
  have hzero := signed_real_principal_strong (q := q) hs hs1
  have hc2 := (signedCost_le_harmonicBound (chi ^ 2) hs hs1 (2 * t)).trans
    (harmonic_support_upper (chi ^ 2) sigma (2 * t))
  have hc3 := (signedCost_le_harmonicBound (chi ^ 3) hs hs1 (3 * t)).trans
    (harmonic_support_upper (chi ^ 3) sigma (3 * t))
  have hc4 := (signedCost_le_harmonicBound (chi ^ 4) hs hs1 (4 * t)).trans
    (harmonic_support_upper (chi ^ 4) sigma (4 * t))
  have hj := lecture_principal_euler_reserve chi hp hs
  have hl2 := mul_le_mul_of_nonneg_left
    (log_max_multiple (t := t) (by norm_num : 1 ≤ (2 : ℕ))) conductorCoeff_bounds.1
  have hl3 := mul_le_mul_of_nonneg_left
    (log_max_multiple (t := t) (by norm_num : 1 ≤ (3 : ℕ))) conductorCoeff_bounds.1
  have hl4 := mul_le_mul_of_nonneg_left
    (log_max_multiple (t := t) (by norm_num : 1 ≤ (4 : ℕ))) conductorCoeff_bounds.1
  norm_num only [Nat.cast_ofNat] at hl2 hl3 hl4
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hlog4] at hl4
  have hpi := mul_le_mul_of_nonneg_left log_pi_ge_one conductorCoeff_bounds.1
  have hl2u := mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le conductorCoeff_bounds.1
  have hl3u := mul_le_mul_of_nonneg_left Real.log_three_lt_d9.le conductorCoeff_bounds.1
  have hk : 11 / 40 ≤ stechkinConductorCoeff := by
    dsimp [stechkinConductorCoeff]
    linarith [stechkinK_le]
  have hk1 := conductorCoeff_bounds.2
  have hk0 := stechkinK_ge
  norm_num only [Fin.sum_univ_succ, lectureCoefficients_exact, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ, Fin.sum_univ_zero, pow_zero, pow_one,
    Nat.cast_zero, Nat.cast_add, Nat.cast_one, zero_mul, one_mul, Nat.cast_ofNat] at ⊢
  simp only [div_eq_mul_inv] at *
  nlinarith

end LiuWang.Proof.Campaign20260915.OriginalRegion
