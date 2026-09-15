import LiuWang.Proof.ZeroRegionFamily.Sharp.Euler

/-! LWD (2.3), (2.9), and the Euler-factor step following (2.10), pp. 262--265. -/

set_option autoImplicit false
noncomputable section

open Complex Finset
open scoped Classical
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1

def kappa : ℝ := (5 - Real.sqrt 5) / 10

theorem kappa_eq : kappa = stechkinConductorCoeff := by
  have hp : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  unfold kappa stechkinConductorCoeff stechkinK
  field_simp
  nlinarith

def f {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (sigma t : ℝ) : ℝ :=
  ((1 / (Real.sqrt 5 : ℂ)) *
      logDeriv chi.LFunction ((stechkinSigma sigma : ℂ) + I * t) -
    logDeriv chi.LFunction ((sigma : ℂ) + I * t)).re

theorem f_eq_damped {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (sigma t : ℝ) :
    f chi sigma t = dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK t := by
  simp only [f, ← ofReal_one, ← ofReal_div, sub_re, mul_re, ofReal_re,
    ofReal_im, zero_mul, sub_zero, dampedLogDeriv, stechkinK]
  ring

def s (q : ℕ) (sigma : ℝ) : ℝ :=
  ∑ p ∈ q.primeFactors, Real.log p *
    (1 / ((p : ℝ) ^ sigma - 1) -
      1 / (Real.sqrt 5 * ((p : ℝ) ^ stechkinSigma sigma - 1)))

def badS (q1 q : ℕ) (sigma : ℝ) : ℝ :=
  ∑ p ∈ q.primeFactors.filter (fun p => ¬p ∣ q1), Real.log p *
    (1 / ((p : ℝ) ^ sigma - 1) -
      1 / (Real.sqrt 5 * ((p : ℝ) ^ stechkinSigma sigma - 1)))

theorem s_eq (q : ℕ) (sigma : ℝ) : s q sigma = principalPrimeCost q sigma := by
  unfold s principalPrimeCost
  apply sum_congr rfl
  intro p hp
  rw [primeCost_eq_positive_power (Nat.prime_of_mem_primeFactors hp)]
  simp only [stechkinK, div_div]

theorem badS_eq {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (sigma : ℝ) :
    badS chi.conductor q sigma = badPrimeCost chi sigma := by
  unfold badS badPrimeCost
  rw [sum_filter]
  apply sum_congr rfl
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have he : chi.primitiveCharacter p ≠ 0 ↔ ¬p ∣ chi.conductor := by
    rw [MulChar.apply_ne_zero_iff, ZMod.isUnit_iff_coprime,
      hprime.coprime_iff_not_dvd]
  by_cases hz : chi.primitiveCharacter p = 0
  · have hd : p ∣ chi.conductor := not_not.mp (fun hn => (he.mpr hn) hz)
    simp [hz, hd]
  · simp only [hz, he.mp hz, not_false_eq_true, ↓reduceIte]
    rw [primeCost_eq_positive_power hprime]
    simp only [stechkinK, div_div]

theorem badS_nonneg {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 < sigma) : 0 ≤ badS chi.conductor q sigma := by
  rw [badS_eq]
  apply sum_nonneg
  intro p hp
  split_ifs
  · exact le_rfl
  · exact primeCost_nonneg (Nat.prime_of_mem_primeFactors hp) hs

theorem abs_f_sub_primitive_le {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor] (hc : chi ≠ 1)
    {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    |f chi sigma t - f chi.primitiveCharacter sigma t| ≤
      badS chi.conductor q sigma := by
  let d := logDeriv (levelCorrection chi) ((sigma : ℂ) + I * t) -
    (stechkinK : ℂ) *
      logDeriv (levelCorrection chi) ((stechkinSigma sigma : ℂ) + I * t)
  have hd : f chi sigma t - f chi.primitiveCharacter sigma t = -d.re := by
    simp only [f_eq_damped, dampedLogDeriv]
    rw [logDeriv_LFunction_eq_primitive_add_levelCorrection chi hc
      (by simpa [mul_re] using hs.le),
      logDeriv_LFunction_eq_primitive_add_levelCorrection chi hc
        (by simpa [mul_re] using (hs.trans_le (stechkinSigma_ge hs)).le)]
    simp only [d, add_re, sub_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    ring
  rw [hd, abs_neg, badS_eq]
  exact (abs_re_le_norm d).trans (norm_level_difference_le chi hc hs t)

theorem abs_f_principal_sub_zeta_le {q : ℕ} [NeZero q]
    {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    |f (1 : DirichletCharacter ℂ q) sigma t -
      (-(logDeriv riemannZeta ((sigma : ℂ) + I * t)).re +
        stechkinK * (logDeriv riemannZeta ((stechkinSigma sigma : ℂ) + I * t)).re)| ≤
      s q sigma := by
  let d := logDeriv (principalLevelCorrection q) ((sigma : ℂ) + I * t) -
    (stechkinK : ℂ) *
      logDeriv (principalLevelCorrection q) ((stechkinSigma sigma : ℂ) + I * t)
  have hd : f (1 : DirichletCharacter ℂ q) sigma t -
      (-(logDeriv riemannZeta ((sigma : ℂ) + I * t)).re +
        stechkinK * (logDeriv riemannZeta ((stechkinSigma sigma : ℂ) + I * t)).re) =
      -d.re := by
    rw [f_eq_damped]
    unfold dampedLogDeriv
    rw [logDeriv_principal_eq_levelCorrection_add_riemannZeta
      (by simpa [mul_re] using hs),
      logDeriv_principal_eq_levelCorrection_add_riemannZeta
        (by simpa [mul_re] using hs.trans_le (stechkinSigma_ge hs))]
    simp only [d, add_re, sub_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    ring
  rw [hd, abs_neg, s_eq]
  exact (abs_re_le_norm d).trans (norm_principal_level_difference_le q hs t)

theorem principal_at_zero_identity {q : ℕ} [NeZero q]
    {sigma : ℝ} (hs : 1 < sigma) :
    f (1 : DirichletCharacter ℂ q) sigma 0 =
      -(logDeriv riemannZeta (sigma : ℂ)).re +
        stechkinK * (logDeriv riemannZeta (stechkinSigma sigma : ℂ)).re - s q sigma := by
  rw [f_eq_damped, s_eq]
  exact principal_real_damped_identity hs

end LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1
