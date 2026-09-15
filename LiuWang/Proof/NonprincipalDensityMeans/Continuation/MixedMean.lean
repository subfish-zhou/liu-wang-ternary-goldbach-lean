import LiuWang.Proof.NonprincipalDensityMeans.Continuation.CollectedProduct
import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeIIActualTensorMomentExplicit

/-!
# A paid mixed mean for the actual fixed-modulus detector

Collect L_M Q - 1 before using the q-spaced finite mean. The finite energy
cost is logarithmic to the fourth power, not a pointwise Q factor of size X.
The actual remainder is multiplied by the already paid Q family mean.
-/

set_option autoImplicit false
noncomputable section

open Finset MeasureTheory
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.NonprincipalDensityAdvance
open MathlibNt.SieveTheory.LiuWeight

namespace LiuWang.Proof.NonprincipalDensityMeans.Continuation

def finiteDetectorMean (q : ℕ) [NeZero q] (X : ℝ) (M : ℕ) (y : ℝ) : ℝ :=
  (∑ chi ∈ nonprincipalCharacters q, ∫ t in -y..y,
    ‖finiteDetector chi X M ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) / q.totient

theorem finiteDetector_critical_integrable {q : ℕ} (chi : Character q)
    (X : ℝ) {M : ℕ} (hM : 2 ≤ M) (hX : 1 < X) (y : ℝ) :
    IntervalIntegrable (fun t =>
      ‖finiteDetector chi X M ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) volume (-y) y := by
  simp_rw [finiteDetector_eq_collected chi X hM hX]
  simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
    dirichletPolynomial_integrable chi _ (fun _ hn =>
      Nat.pos_of_ne_zero (mem_erase.mp hn).1) (detectorCoefficient M ⌈X⌉₊) (1 / 2) y

theorem detectorCoefficient_critical_energy {M N : ℕ} (hM : 2 ≤ M) (hN : 2 ≤ N) :
    (∑ n ∈ (range (M * N + 1)).erase 0,
      ‖verticalCoefficient (detectorCoefficient M N) (1 / 2) n‖ ^ 2) ≤
        liuHarmonic (M * N) ^ 4 := by
  have hset : (range (M * N + 1)).erase 0 = Icc 1 (M * N) := by
    ext n
    simp only [mem_erase, mem_range, mem_Icc]
    omega
  rw [hset]
  apply le_trans _ (AnalyticNumberTheory.LargeSieve.divisorSquareWeightedPrefix_le_fourth_harmonic _)
  apply sum_le_sum
  intro n hn
  have hn0 : 0 < n := (mem_Icc.mp hn).1
  rw [verticalCoefficient, norm_div, Complex.norm_natCast_cpow_of_pos hn0,
    Complex.ofReal_re, ← Real.sqrt_eq_rpow, div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  simpa only [div_eq_mul_inv] using
    div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (detectorCoefficient_norm_le hM hN n) 2)
      (Nat.cast_nonneg n)

theorem finiteDetectorMean_le_with_principal (q : ℕ) [NeZero q] (X : ℝ)
    {M : ℕ} (hM : 2 ≤ M) (hX : 1 < X) {y : ℝ} (hy : 0 ≤ y) :
    finiteDetectorMean q X M y ≤
      meanFactor q (M * ⌈X⌉₊ + 1) y * liuHarmonic (M * ⌈X⌉₊) ^ 4 -
        (∫ t in -y..y, ‖finiteDetector (1 : Character q) X M
          ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) / q.totient := by
  have hN : 2 ≤ ⌈X⌉₊ := by
    have : 1 < ⌈X⌉₊ := Nat.lt_ceil.mpr (by simpa using hX)
    omega
  have hE := (unitEnergy_le q _ _).trans (detectorCoefficient_critical_energy hM hN)
  have h := dirichlet_mean_le q (Subset.refl ((range (M * ⌈X⌉₊ + 1)).erase 0))
    (detectorCoefficient M ⌈X⌉₊) (1 / 2) hy
  have hb := h.trans (sub_le_sub_right
    (mul_le_mul_of_nonneg_left hE (meanFactor_nonneg q _ hy)) _)
  unfold finiteDetectorMean
  simp_rw [finiteDetector_eq_collected _ X hM hX]
  simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using hb

theorem finiteDetectorMean_le (q : ℕ) [NeZero q] (X : ℝ)
    {M : ℕ} (hM : 2 ≤ M) (hX : 1 < X) {y : ℝ} (hy : 0 ≤ y) :
    finiteDetectorMean q X M y ≤
      meanFactor q (M * ⌈X⌉₊ + 1) y * liuHarmonic (M * ⌈X⌉₊) ^ 4 :=
  (finiteDetectorMean_le_with_principal q X hM hX hy).trans
    (sub_le_self _ (div_nonneg (intervalIntegral.integral_nonneg (by linarith)
      (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg _)))

theorem FremainderMean_le_Qmean (q : ℕ) [NeZero q] (X : ℝ)
    {M : ℕ} (hM : 1 ≤ M) {y : ℝ} (hy : 0 ≤ y) :
    FremainderMean q X M y ≤ truncationError q M y ^ 2 * Qmean q X (1 / 2) y := by
  have hi (chi : Character q) (hchi : chi ≠ 1) :
      (∫ t in -y..y, ‖NonprincipalDensityAdvance.f chi X ((1 / 2 : ℂ) + t * Complex.I) -
        finiteDetector chi X M ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) ≤
          truncationError q M y ^ 2 * (∫ t in -y..y,
            ‖NonprincipalDensityAdvance.Q chi X ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) := by
    have hQ : Continuous (fun t : ℝ =>
        NonprincipalDensityAdvance.Q chi X ((1 / 2 : ℂ) + t * Complex.I)) := by
      simp_rw [Q_critical_eq_wave]
      exact continuous_polynomial _ _ _ _
    have hR := Lremainder_critical_continuous hchi M
    simp_rw [f_sub_finiteDetector]
    have h := intervalIntegral.integral_mono_on (μ := volume) (by linarith : -y ≤ y)
      (((hR.mul hQ).norm.pow 2).intervalIntegrable _ _)
      (((hQ.norm.pow 2).intervalIntegrable (-y) y).const_mul (truncationError q M y ^ 2))
      (fun _ ht => by
        simp only [Pi.pow_apply, Pi.mul_apply, norm_mul, mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _)
          (LFunction_truncation_critical hchi hM (abs_le.mpr ht)) 2) (sq_nonneg _))
    simp only [Pi.pow_apply, Pi.mul_apply] at h
    rwa [intervalIntegral.integral_const_mul] at h
  have h := sum_le_sum (s := nonprincipalCharacters q)
    (fun chi hchi => hi chi ((mem_nonprincipalCharacters chi).mp hchi))
  rw [← mul_sum] at h
  apply (div_le_div_of_nonneg_right h (Nat.cast_nonneg q.totient)).trans_eq
  unfold Qmean
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

theorem Fmean_le_finite_and_remainder (q : ℕ) [NeZero q] (X : ℝ)
    {M : ℕ} (hM : 2 ≤ M) (hX : 1 < X) {y : ℝ} (hy : 0 ≤ y) :
    Fmean q X (1 / 2) y ≤
      2 * finiteDetectorMean q X M y + 2 * FremainderMean q X M y := by
  have hi (chi : Character q) (hchi : chi ≠ 1) :
      (∫ t in -y..y, ‖NonprincipalDensityAdvance.f chi X ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) ≤
        2 * (∫ t in -y..y, ‖finiteDetector chi X M ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) +
          2 * (∫ t in -y..y,
            ‖NonprincipalDensityAdvance.f chi X ((1 / 2 : ℂ) + t * Complex.I) -
              finiteDetector chi X M ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) := by
    have hP := finiteDetector_critical_integrable chi X hM hX y
    have hQ := (differentiable_Q chi X).continuous.comp
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
        : Continuous (fun t : ℝ => (1 / 2 : ℂ) + t * Complex.I))
    have hR : IntervalIntegrable (fun t =>
        ‖NonprincipalDensityAdvance.f chi X ((1 / 2 : ℂ) + t * Complex.I) -
          finiteDetector chi X M ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) volume (-y) y := by
      simp_rw [f_sub_finiteDetector]
      simpa only [Pi.pow_def, Pi.mul_def, Pi.add_def, Function.comp_def] using
        ((((Lremainder_critical_continuous hchi M).mul hQ).norm.pow 2).intervalIntegrable (-y) y)
    have hf := f_vertical_integrable hchi X (1 / 2) y
    norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hf
    have h := intervalIntegral.integral_mono_on (by linarith : -y ≤ y) hf
      ((hP.const_mul 2).add (hR.const_mul 2)) (fun t _ => by
        have h := norm_add_sq_le (finiteDetector chi X M ((1 / 2 : ℂ) + t * Complex.I))
          (NonprincipalDensityAdvance.f chi X ((1 / 2 : ℂ) + t * Complex.I) -
            finiteDetector chi X M ((1 / 2 : ℂ) + t * Complex.I))
        rwa [add_sub_cancel] at h)
    rwa [intervalIntegral.integral_add (hP.const_mul 2) (hR.const_mul 2),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
  have h := sum_le_sum (s := nonprincipalCharacters q)
    (fun chi hchi => hi chi ((mem_nonprincipalCharacters chi).mp hchi))
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at h
  unfold Fmean finiteDetectorMean FremainderMean
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  exact (div_le_div_of_nonneg_right h (Nat.cast_nonneg q.totient)).trans_eq (by ring)

theorem Fmean_mixed_bound (q : ℕ) [NeZero q] (X : ℝ)
    {M : ℕ} (hM : 2 ≤ M) (hX : 1 < X) {y : ℝ} (hy : 0 ≤ y) :
    Fmean q X (1 / 2) y ≤
      2 * meanFactor q (M * ⌈X⌉₊ + 1) y * liuHarmonic (M * ⌈X⌉₊) ^ 4 +
        2 * truncationError q M y ^ 2 * mollifierMeanBound q X y := by
  have hR := (FremainderMean_le_Qmean q X (by omega : 1 ≤ M) hy).trans
    (mul_le_mul_of_nonneg_left (Qmean_critical_le q X hy) (sq_nonneg _))
  have h := add_le_add
    (mul_le_mul_of_nonneg_left (finiteDetectorMean_le q X hM hX hy) (by norm_num : (0 : ℝ) ≤ 2))
    (mul_le_mul_of_nonneg_left hR (by norm_num : (0 : ℝ) ≤ 2))
  exact (Fmean_le_finite_and_remainder q X hM hX hy).trans (h.trans_eq (by ring))

@[simp] theorem finiteDetectorMean_one (X : ℝ) (M : ℕ) (y : ℝ) :
    finiteDetectorMean 1 X M y = 0 := by simp [finiteDetectorMean]

@[simp] theorem finiteDetectorMean_two (X : ℝ) (M : ℕ) (y : ℝ) :
    finiteDetectorMean 2 X M y = 0 := by simp [finiteDetectorMean]

end LiuWang.Proof.NonprincipalDensityMeans.Continuation
