import LiuWang.Proof.Campaign20260915.OriginalRegion.HigherOrderBudget

/-! Keep every moving principal pole while paying the simultaneous bad-prime costs. -/

set_option autoImplicit false
noncomputable section

open Complex
open scoped Classical
open LiuWang.Proof.MultiZeroRepulsion
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.ZeroRegionFamily.RealClosure LiuWang.Proof.ZeroRegionFamily.Uniform
open LiuWang.Proof.ZeroRegionFamily.ApplicationScale
open LiuWang.Proof.ChebyshevBound.HighHeight

namespace LiuWang.Proof.Campaign20260915.OriginalRegion

theorem principal_badPrimeCost (q : ℕ) [NeZero q] (sigma : ℝ) :
    badPrimeCost (1 : DirichletCharacter ℂ q) sigma = principalPrimeCost q sigma := by
  simp only [badPrimeCost, principalPrimeCost, DirichletCharacter.primitiveCharacter_one]
  apply Finset.sum_congr rfl
  intro p _
  have hu : IsUnit (p : ZMod (1 : DirichletCharacter ℂ q).conductor) := by
    rw [DirichletCharacter.conductor_one]
    rw [Subsingleton.elim (p : ZMod 1) 1]
    exact isUnit_one
  rw [MulChar.one_apply hu]
  simp

theorem harmonic_support_upper {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (sigma t : ℝ) :
    harmonicBound chi sigma t ≤ harmonicPole chi sigma t +
      stechkinConductorCoeff *
        (Real.log chi.conductor + Real.log (max 1 |t|) - Real.log Real.pi) +
      (23 / 40 - 11 * stechkinK / 30) + badPrimeCost chi sigma := by
  by_cases hc : chi = 1
  · subst chi
    simp [harmonicBound, harmonicPole, DirichletCharacter.conductor_one, principal_badPrimeCost]
    ring_nf
    rfl
  · simp only [harmonicBound, harmonicPole, if_neg hc, zero_add]
    linarith [stechkinK_le]

theorem lecture_moving_pole_budget {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    {rho : ℂ} (hr : 1 / 2 < rho.re) (hz : chi.LFunction rho = 0)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) :
    19.073344004352 / (sigma - rho.re) + 1 + 2 * principalPrimeCost q sigma ≤
      11.1859355312082048 / (sigma - 1) +
        36.506331844352 * stechkinConductorCoeff *
          (Real.log q + Real.log (max 1 |rho.im|)) +
        11.67618784 * harmonicPole (chi ^ 2) sigma (2 * rho.im) +
        4.7568 * harmonicPole (chi ^ 3) sigma (3 * rho.im) +
        harmonicPole (chi ^ 4) sigma (4 * rho.im) := by
  have hpos := lecture_damped_nonneg chi hs rho.im
  have hmain := primitive_actual_selected_bound hc hp hr hz hs hs1
  have hzero := principal_real_strong (q := q) hs hs1
  have hc2 := (harmonicBound_paid (chi ^ 2) hs hs1 (2 * rho.im)).trans
    (harmonic_support_upper (chi ^ 2) sigma (2 * rho.im))
  have hc3 := (harmonicBound_paid (chi ^ 3) hs hs1 (3 * rho.im)).trans
    (harmonic_support_upper (chi ^ 3) sigma (3 * rho.im))
  have hc4 := (harmonicBound_paid (chi ^ 4) hs hs1 (4 * rho.im)).trans
    (harmonic_support_upper (chi ^ 4) sigma (4 * rho.im))
  have hj := lecture_principal_euler_reserve chi hp hs
  have hl2 := mul_le_mul_of_nonneg_left
    (log_max_multiple (t := rho.im) (by norm_num : 1 ≤ (2 : ℕ))) conductorCoeff_bounds.1
  have hl3 := mul_le_mul_of_nonneg_left
    (log_max_multiple (t := rho.im) (by norm_num : 1 ≤ (3 : ℕ))) conductorCoeff_bounds.1
  have hl4 := mul_le_mul_of_nonneg_left
    (log_max_multiple (t := rho.im) (by norm_num : 1 ≤ (4 : ℕ))) conductorCoeff_bounds.1
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
  simp only [div_eq_mul_inv] at *
  nlinarith

theorem lecture_high_pole_free_budget {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    {rho : ℂ} (hr : 1 / 2 < rho.re) (hz : chi.LFunction rho = 0)
    (ht : 1 / 2 ≤ |rho.im|) {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) :
    19.073344004352 / (sigma - rho.re) ≤
      11.1859355312082048 / (sigma - 1) +
        36.506331844352 * stechkinConductorCoeff *
          (Real.log q + Real.log (max 1 |rho.im|)) := by
  have hh := lecture_moving_pole_budget hc hp hr hz hs hs1
  have h2 : harmonicPole (chi ^ 2) sigma (2 * rho.im) ≤ 0 := by
    unfold harmonicPole
    split_ifs
    · apply poleDifference_high_nonpos hs hs1
      rw [abs_mul]
      norm_num
      linarith
    · rfl
  have h3 : harmonicPole (chi ^ 3) sigma (3 * rho.im) ≤ 0 := by
    unfold harmonicPole
    split_ifs
    · apply poleDifference_high_nonpos hs hs1
      rw [abs_mul]
      norm_num
      linarith
    · rfl
  have h4 : harmonicPole (chi ^ 4) sigma (4 * rho.im) ≤ 0 := by
    unfold harmonicPole
    split_ifs
    · apply poleDifference_high_nonpos hs hs1
      rw [abs_mul]
      norm_num
      linarith
    · rfl
  have he := principalPrimeCost_nonneg q hs
  linarith

end LiuWang.Proof.Campaign20260915.OriginalRegion
