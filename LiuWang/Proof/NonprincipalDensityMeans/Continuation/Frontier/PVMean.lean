import LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.FullFamilyPV

/-! # Consume the all-character PV prefix in actual L and mixed-detector tails -/

set_option autoImplicit false
noncomputable section

open Finset MeasureTheory Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.NonprincipalDensityAdvance
open MathlibNt.SieveTheory.LiuWeight

namespace LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier

def pvError (q M : ℕ) (sigma y : ℝ) : ℝ :=
  2 * prefixBudget q * (1 + y) * (M : ℝ) ^ (-sigma)

theorem LFunction_truncation_PV {q M : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hM : 1 ≤ M) {sigma y t : ℝ}
    (hs : 1 / 2 ≤ sigma) (ht : |t| ≤ y) :
    ‖chi.LFunction ((sigma : ℂ) + t * Complex.I) -
      partialL chi M ((sigma : ℂ) + t * Complex.I)‖ ≤ pvError q M sigma y := by
  have hs0 : 0 < sigma := by linarith
  have hy : 0 ≤ y := (abs_nonneg t).trans ht
  have hr : ((sigma : ℂ) + t * Complex.I).re = sigma := by simp
  have h := DirichletCharacter.norm_LFunction_sub_sum_le_of_prefix_bound chi hchi
    ((sigma : ℂ) + t * Complex.I) (by rwa [hr]) (prefixBudget q)
    (nonprincipal_prefix_budget q chi hchi) hM
  rw [← partialL_eq_Abel_sum hchi, hr] at h
  have hn : ‖(sigma : ℂ) + t * Complex.I‖ ≤ sigma + y := by
    have hb := norm_add_le (sigma : ℂ) ((t : ℂ) * Complex.I)
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0,
      norm_mul, Complex.norm_I, mul_one] at hb
    linarith
  have hd : ‖(sigma : ℂ) + t * Complex.I‖ / sigma ≤ 1 + 2 * y := by
    apply (div_le_iff₀ hs0).mpr
    nlinarith
  have hp := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hd (Real.rpow_nonneg (Nat.cast_nonneg M) (-sigma)))
    (prefixBudget_nonneg q)
  apply h.trans
  unfold pvError
  nlinarith only [hp]

theorem pvError_le_stripError (q : ℕ) [NeZero q] (M : ℕ) (sigma : ℝ) {y : ℝ}
    (hy : 0 ≤ y) : pvError q M sigma y ≤ stripError q M sigma y := by
  have h := mul_le_mul_of_nonneg_right (min_le_left (q : ℝ)
    (8 * Real.sqrt q * (1 + Real.log q)))
      (by positivity : 0 ≤ 2 * (1 + y) * (M : ℝ) ^ (-sigma))
  unfold pvError stripError prefixBudget
  nlinarith only [h]

theorem pvError_critical_sq (q M : ℕ) {y : ℝ} :
    pvError q M (1 / 2) y ^ 2 = 4 * prefixBudget q ^ 2 * (1 + y) ^ 2 / M := by
  unfold pvError
  rw [mul_pow, mul_pow, mul_pow, ← Real.rpow_natCast ((M : ℝ) ^ (-(1 / 2))) 2,
    ← Real.rpow_mul (Nat.cast_nonneg M)]
  norm_num only [Nat.cast_ofNat, show (-(1 / 2 : ℝ)) * 2 = -1 by norm_num,
    Real.rpow_neg_one]
  ring

theorem FremainderMean_PV (q : ℕ) [NeZero q] (X : ℝ)
    {M : ℕ} (hM : 1 ≤ M) {y : ℝ} (hy : 0 ≤ y) :
    FremainderMean q X M y ≤
      pvError q M (1 / 2) y ^ 2 * Qmean q X (1 / 2) y := by
  unfold FremainderMean
  have hi (chi : Character q) (hchi : chi ≠ 1) :
      (∫ t in -y..y, ‖NonprincipalDensityAdvance.f chi X ((1 / 2 : ℂ) + t * Complex.I) -
        finiteDetector chi X M ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) ≤
      pvError q M (1 / 2) y ^ 2 *
        (∫ t in -y..y, ‖NonprincipalDensityAdvance.Q chi X ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) := by
    have hQ : Continuous (fun t : ℝ =>
        NonprincipalDensityAdvance.Q chi X ((1 / 2 : ℂ) + t * Complex.I)) := by
      simp_rw [Q_critical_eq_wave]
      exact continuous_polynomial _ _ _ _
    have hR := Lremainder_critical_continuous hchi M
    simp_rw [f_sub_finiteDetector]
    have h := intervalIntegral.integral_mono_on (μ := volume) (by linarith : -y ≤ y)
      (((hR.mul hQ).norm.pow 2).intervalIntegrable _ _)
      (((hQ.norm.pow 2).intervalIntegrable (-y) y).const_mul (pvError q M (1 / 2) y ^ 2))
      (fun t ht => by
        simp only [Pi.pow_apply, Pi.mul_apply, norm_mul, mul_pow]
        have hp := LFunction_truncation_PV hchi hM (sigma := 1 / 2)
          le_rfl (abs_le.mpr ht)
        norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hp
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hp 2) (sq_nonneg _))
    simp only [Pi.pow_apply, Pi.mul_apply] at h
    rwa [intervalIntegral.integral_const_mul] at h
  have h := sum_le_sum (s := nonprincipalCharacters q)
    (fun chi hchi => hi chi ((mem_nonprincipalCharacters chi).mp hchi))
  rw [← mul_sum] at h
  apply (div_le_div_of_nonneg_right h (Nat.cast_nonneg q.totient)).trans_eq
  unfold Qmean
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

theorem Fmean_critical_PV (q : ℕ) [NeZero q] (X : ℝ)
    {M : ℕ} (hM : 2 ≤ M) (hX : 1 < X) {y : ℝ} (hy : 0 ≤ y) :
    Fmean q X (1 / 2) y ≤
      2 * meanFactor q (M * ⌈X⌉₊ + 1) y * liuHarmonic (M * ⌈X⌉₊) ^ 4 +
        8 * prefixBudget q ^ 2 * (1 + y) ^ 2 / M * mollifierMeanBound q X y := by
  have hR := (FremainderMean_PV q X (by omega : 1 ≤ M) hy).trans
    (mul_le_mul_of_nonneg_left (Qmean_critical_le q X hy) (sq_nonneg _))
  have h := add_le_add
    (mul_le_mul_of_nonneg_left (finiteDetectorMean_le q X hM hX hy) (by norm_num : (0 : ℝ) ≤ 2))
    (mul_le_mul_of_nonneg_left hR (by norm_num : (0 : ℝ) ≤ 2))
  rw [pvError_critical_sq] at h
  exact (Fmean_le_finite_and_remainder q X hM hX hy).trans (h.trans_eq (by ring))

theorem Fmean_critical_PV_explicit (q : ℕ) [NeZero q] (X : ℝ)
    {M : ℕ} (hM : 2 ≤ M) (hX : 1 < X) {y : ℝ} (hy : 0 ≤ y) :
    Fmean q X (1 / 2) y ≤
      2 * meanFactor q (M * ⌈X⌉₊ + 1) y * liuHarmonic (M * ⌈X⌉₊) ^ 4 +
        512 * q * (1 + Real.log q) ^ 2 * (1 + y) ^ 2 / M * mollifierMeanBound q X y := by
  have hP : prefixBudget q ^ 2 ≤ 64 * q * (1 + Real.log q) ^ 2 := by
    have h := pow_le_pow_left₀ (prefixBudget_nonneg q)
      (min_le_right (q : ℝ) (8 * Real.sqrt q * (1 + Real.log q))) 2
    apply h.trans_eq
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg q)]
    ring
  have hm := mul_le_mul_of_nonneg_right hP
    (mul_nonneg (by positivity : 0 ≤ 8 * (1 + y) ^ 2 / M)
      (mollifierMeanBound_nonneg q X hy))
  apply (Fmean_critical_PV q X hM hX hy).trans
  simp only [div_eq_mul_inv] at hm ⊢
  nlinarith only [hm]

end LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier
