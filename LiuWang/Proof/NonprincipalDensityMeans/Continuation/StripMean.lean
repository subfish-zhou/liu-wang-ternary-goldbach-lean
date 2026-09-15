import LiuWang.Proof.NonprincipalDensityMeans.Continuation.Cancellation

/-!
# Direct high-sigma means with the actual Mobius cancellation

This is a finite-convolution and Abel-tail proof, not a three-lines theorem.
All characters remain at the original modulus, and X, M, sigma, y are explicit.
-/

set_option autoImplicit false
noncomputable section

open Finset MeasureTheory
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.NonprincipalDensityAdvance
open MathlibNt.SieveTheory.LiuWeight

namespace LiuWang.Proof.NonprincipalDensityMeans.Continuation

def stripError (q M : ℕ) (sigma y : ℝ) : ℝ :=
  2 * q * (1 + y) * (M : ℝ) ^ (-sigma)

theorem LFunction_truncation_strip {q M : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hM : 1 ≤ M) {sigma y t : ℝ}
    (hs : 1 / 2 ≤ sigma) (ht : |t| ≤ y) :
    ‖chi.LFunction ((sigma : ℂ) + t * Complex.I) -
      partialL chi M ((sigma : ℂ) + t * Complex.I)‖ ≤ stripError q M sigma y := by
  have hs0 : 0 < sigma := by linarith
  have hy : 0 ≤ y := (abs_nonneg t).trans ht
  have hr : ((sigma : ℂ) + t * Complex.I).re = sigma := by simp
  have h := DirichletCharacter.norm_LFunction_sub_sum_le_of_prefix_bound chi hchi
    ((sigma : ℂ) + t * Complex.I) (by rwa [hr]) (q : ℝ)
    (DirichletLWeakStripDerivative.norm_sum_range_character_le_modulus chi hchi) hM
  rw [← partialL_eq_Abel_sum hchi, hr] at h
  have hn : ‖(sigma : ℂ) + t * Complex.I‖ ≤ sigma + y := by
    have h := norm_add_le (sigma : ℂ) ((t : ℂ) * Complex.I)
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0,
      norm_mul, Complex.norm_I, mul_one] at h
    linarith
  have hd : ‖(sigma : ℂ) + t * Complex.I‖ / sigma ≤ 1 + 2 * y := by
    apply (div_le_iff₀ hs0).mpr
    nlinarith
  have hp := mul_le_mul_of_nonneg_right hd
    (Real.rpow_nonneg (Nat.cast_nonneg M) (-sigma))
  have hq := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg q)
  apply h.trans
  unfold stripError
  nlinarith only [hq]

theorem verticalCoefficient_sq_mono {n : ℕ} (hn : 0 < n) (c : ℕ → ℂ)
    {sigma : ℝ} (hs : 1 / 2 ≤ sigma) :
    ‖verticalCoefficient c sigma n‖ ^ 2 ≤ ‖verticalCoefficient c (1 / 2) n‖ ^ 2 := by
  rw [critical_weight_shift hn, critical_weight_shift hn]
  norm_num only [show (1 : ℝ) - 2 * (1 / 2) = 0 by norm_num, Real.rpow_zero, mul_one]
  have hp : (n : ℝ) ^ (1 - 2 * sigma) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le
      (Nat.one_le_cast.mpr hn) (show 1 - 2 * sigma ≤ 0 by linarith)
  exact (mul_le_mul_of_nonneg_left hp (by positivity)).trans_eq (mul_one _)

theorem Qmean_strip_le (q : ℕ) [NeZero q] (X : ℝ) {sigma y : ℝ}
    (hs : 1 / 2 ≤ sigma) (hy : 0 ≤ y) :
    Qmean q X sigma y ≤ mollifierMeanBound q X y := by
  have hE :
      unitEnergy q ((range ⌈X⌉₊).erase 0)
        (verticalCoefficient (fun n => (ArithmeticFunction.moebius n : ℂ)) sigma) ≤
          harmonicRange ⌈X⌉₊ := by
    apply (unitEnergy_le q _ _).trans
    have hp : (∑ n ∈ (range ⌈X⌉₊).erase 0,
        ‖verticalCoefficient (fun n => (ArithmeticFunction.moebius n : ℂ)) sigma n‖ ^ 2) ≤
      ∑ n ∈ (range ⌈X⌉₊).erase 0,
        ‖verticalCoefficient (fun n => (ArithmeticFunction.moebius n : ℂ)) (1 / 2) n‖ ^ 2 :=
      sum_le_sum fun _ hn => verticalCoefficient_sq_mono
        (Nat.pos_of_ne_zero (mem_erase.mp hn).1) _ hs
    rw [vertical_criticalCoefficient_eq] at hp
    exact hp.trans (criticalCoefficient_energy_le _)
  have h := dirichlet_mean_le q (Subset.refl ((range ⌈X⌉₊).erase 0))
    (fun n => (ArithmeticFunction.moebius n : ℂ)) sigma hy
  have hb := (h.trans (sub_le_self _ (div_nonneg
    (intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _))
    (Nat.cast_nonneg _)))).trans
    (mul_le_mul_of_nonneg_left hE (meanFactor_nonneg q _ hy))
  unfold Qmean mollifierMeanBound
  simp_rw [Q_eq_dirichletPolynomial]
  exact hb

theorem finiteDetector_strip_integrable {q : ℕ} (chi : Character q)
    (X : ℝ) {M : ℕ} (hM : 2 ≤ M) (hX : 1 < X) (sigma y : ℝ) :
    IntervalIntegrable (fun t =>
      ‖finiteDetector chi X M ((sigma : ℂ) + t * Complex.I)‖ ^ 2) volume (-y) y := by
  simp_rw [finiteDetector_eq_collected chi X hM hX]
  exact dirichletPolynomial_integrable chi _ (fun _ hn =>
    Nat.pos_of_ne_zero (mem_erase.mp hn).1) _ sigma y

theorem finiteDetector_strip_mean_le (q : ℕ) [NeZero q] (X : ℝ)
    {M : ℕ} (hX : 1 < X) (hNM : ⌈X⌉₊ ≤ M) {sigma y : ℝ}
    (hs : 1 / 2 ≤ sigma) (hy : 0 ≤ y) :
    (∑ chi ∈ nonprincipalCharacters q, ∫ t in -y..y,
      ‖finiteDetector chi X M ((sigma : ℂ) + t * Complex.I)‖ ^ 2) / q.totient ≤
        meanFactor q (M * ⌈X⌉₊ + 1) y * (⌈X⌉₊ : ℝ) ^ (1 - 2 * sigma) *
          liuHarmonic (M * ⌈X⌉₊) ^ 4 := by
  have hN : 2 ≤ ⌈X⌉₊ := by
    have : 1 < ⌈X⌉₊ := Nat.lt_ceil.mpr (by simpa using hX)
    omega
  have h := dirichlet_mean_le q (Subset.refl ((range (M * ⌈X⌉₊ + 1)).erase 0))
    (detectorCoefficient M ⌈X⌉₊) sigma hy
  have hE := (unitEnergy_le q _ _).trans (detectorCoefficient_strip_energy hN hNM hs)
  have hb := (h.trans (sub_le_self _ (div_nonneg
    (intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _))
    (Nat.cast_nonneg _)))).trans
    (mul_le_mul_of_nonneg_left hE (meanFactor_nonneg q _ hy))
  simp_rw [finiteDetector_eq_collected _ X (hN.trans hNM) hX]
  exact hb.trans_eq (by ring)

theorem Fmean_strip_le_finite_and_Q (q : ℕ) [NeZero q] (X : ℝ)
    {M : ℕ} (hM : 2 ≤ M) (hX : 1 < X) {sigma y : ℝ}
    (hs : 1 / 2 ≤ sigma) (hy : 0 ≤ y) :
    Fmean q X sigma y ≤
      2 * ((∑ chi ∈ nonprincipalCharacters q, ∫ t in -y..y,
        ‖finiteDetector chi X M ((sigma : ℂ) + t * Complex.I)‖ ^ 2) / q.totient) +
          2 * stripError q M sigma y ^ 2 * Qmean q X sigma y := by
  have hi (chi : Character q) (hchi : chi ≠ 1) :
      (∫ t in -y..y, ‖NonprincipalDensityAdvance.f chi X ((sigma : ℂ) + t * Complex.I)‖ ^ 2) ≤
        2 * (∫ t in -y..y, ‖finiteDetector chi X M ((sigma : ℂ) + t * Complex.I)‖ ^ 2) +
          2 * stripError q M sigma y ^ 2 *
            (∫ t in -y..y, ‖NonprincipalDensityAdvance.Q chi X ((sigma : ℂ) + t * Complex.I)‖ ^ 2) := by
    have hP := finiteDetector_strip_integrable chi X hM hX sigma y
    have hQ := Q_vertical_integrable chi X sigma y
    have hf := f_vertical_integrable hchi X sigma y
    have h := intervalIntegral.integral_mono_on (by linarith : -y ≤ y) hf
      ((hP.const_mul 2).add (hQ.const_mul (2 * stripError q M sigma y ^ 2))) (fun t ht => by
        have htail := pow_le_pow_left₀ (norm_nonneg _)
          (LFunction_truncation_strip hchi (by omega : 1 ≤ M) hs (abs_le.mpr ht)) 2
        have hR := mul_le_mul_of_nonneg_right htail
          (sq_nonneg ‖NonprincipalDensityAdvance.Q chi X ((sigma : ℂ) + t * Complex.I)‖)
        have h := norm_add_sq_le (finiteDetector chi X M ((sigma : ℂ) + t * Complex.I))
          (NonprincipalDensityAdvance.f chi X ((sigma : ℂ) + t * Complex.I) -
            finiteDetector chi X M ((sigma : ℂ) + t * Complex.I))
        rw [add_sub_cancel, f_sub_finiteDetector, norm_mul, mul_pow] at h
        nlinarith only [h, hR])
    rwa [intervalIntegral.integral_add (hP.const_mul 2) (hQ.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
  have h := sum_le_sum (s := nonprincipalCharacters q)
    (fun chi hchi => hi chi ((mem_nonprincipalCharacters chi).mp hchi))
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at h
  unfold Fmean Qmean
  exact (div_le_div_of_nonneg_right h (Nat.cast_nonneg q.totient)).trans_eq (by ring)

theorem Fmean_strip_bound (q : ℕ) [NeZero q] (X : ℝ)
    {M : ℕ} (hX : 1 < X) (hNM : ⌈X⌉₊ ≤ M) {sigma y : ℝ}
    (hs : 1 / 2 ≤ sigma) (hy : 0 ≤ y) :
    Fmean q X sigma y ≤
      2 * meanFactor q (M * ⌈X⌉₊ + 1) y * (⌈X⌉₊ : ℝ) ^ (1 - 2 * sigma) *
        liuHarmonic (M * ⌈X⌉₊) ^ 4 +
      2 * stripError q M sigma y ^ 2 * mollifierMeanBound q X y := by
  have hM : 2 ≤ M := by
    have : 1 < ⌈X⌉₊ := Nat.lt_ceil.mpr (by simpa using hX)
    omega
  have h := add_le_add
    (mul_le_mul_of_nonneg_left (finiteDetector_strip_mean_le q X hX hNM hs hy)
      (by norm_num : (0 : ℝ) ≤ 2))
    (mul_le_mul_of_nonneg_left (Qmean_strip_le q X hs hy)
      (by positivity : 0 ≤ 2 * stripError q M sigma y ^ 2))
  exact (Fmean_strip_le_finite_and_Q q X hM hX hs hy).trans (h.trans_eq (by ring))

end LiuWang.Proof.NonprincipalDensityMeans.Continuation
