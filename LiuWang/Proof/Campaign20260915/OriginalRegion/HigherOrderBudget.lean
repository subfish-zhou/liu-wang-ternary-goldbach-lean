import LiuWang.Proof.Campaign20260915.OriginalRegion.PowerEulerSupport

/-! The lecture polynomial's nonprincipal-power branch, with simultaneous Euler payment. -/

set_option autoImplicit false
noncomputable section

open Complex
open scoped BigOperators Classical
open LiuWang.Proof.MultiZeroRepulsion
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.ZeroRegionFamily.RealClosure
open LiuWang.Proof.ZeroRegionFamily.ApplicationScale
open LiuWang.Proof.ChebyshevBound.HighHeight

namespace LiuWang.Proof.Campaign20260915.OriginalRegion

theorem lecture_damped_nonneg {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    0 ≤ 11.1859355312082048 * dampedLogDeriv (1 : DirichletCharacter ℂ q)
        sigma (stechkinSigma sigma) stechkinK 0 +
      19.073344004352 * dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK t +
      11.67618784 * dampedLogDeriv (chi ^ 2) sigma (stechkinSigma sigma) stechkinK (2 * t) +
      4.7568 * dampedLogDeriv (chi ^ 3) sigma (stechkinSigma sigma) stechkinK (3 * t) +
      dampedLogDeriv (chi ^ 4) sigma (stechkinSigma sigma) stechkinK (4 * t) := by
  have hh := damped_polynomial_nonneg Finset.univ
    (fun j : Fin 5 => chi ^ (j : ℕ)) (fun j : Fin 5 => (j : ℝ) * t) lectureCoefficients
    (fun _ hn hu => lecture_phase_nonneg chi hn hu t)
    hs (stechkinSigma_ge hs) stechkinK_mem
  norm_num [Fin.sum_univ_succ, lectureCoefficients_exact] at hh
  linarith

theorem higher_order_lecture_budget {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    (h2 : chi ^ 2 ≠ 1) (h3 : chi ^ 3 ≠ 1) (h4 : chi ^ 4 ≠ 1)
    {rho : ℂ} (hr : 1 / 2 < rho.re) (hz : chi.LFunction rho = 0)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) :
    19.073344004352 / (sigma - rho.re) + 4 + 2 * principalPrimeCost q sigma ≤
      11.1859355312082048 / (sigma - 1) +
        36.506331844352 * stechkinConductorCoeff *
          (Real.log q + Real.log (max 1 |rho.im|)) := by
  have hpos := lecture_damped_nonneg chi hs rho.im
  have hmain := primitive_actual_selected_bound hc hp hr hz hs hs1
  have hzero := principal_real_strong (q := q) hs hs1
  have hc2 := imprimitive_damped_bound (chi ^ 2) h2 hs hs1 (2 * rho.im)
  have hc3 := imprimitive_damped_bound (chi ^ 3) h3 hs hs1 (3 * rho.im)
  have hc4 := imprimitive_damped_bound (chi ^ 4) h4 hs hs1 (4 * rho.im)
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
  simp only [div_eq_mul_inv] at *
  nlinarith

end LiuWang.Proof.Campaign20260915.OriginalRegion
