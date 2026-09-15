import LiuWang.Proof.NonprincipalDensityMeans.Continuation.StripMean

/-! # Explicit logarithmic costs and summable actual mixed remainders -/

set_option autoImplicit false
noncomputable section

open Finset
open MathlibNt.SieveTheory.LiuWeight
open LiuWang.Proof.GlobalZeroDensity.Sharp

namespace LiuWang.Proof.NonprincipalDensityMeans.Continuation

def logarithmicMeanFactor (q N : ℕ) (y : ℝ) : ℝ :=
  2 * y + 4 * (N : ℝ) / q * (1 + Real.log (N / q + 1 : ℕ))

theorem meanFactor_le_logarithmic (q N : ℕ) (y : ℝ) :
    meanFactor q N y ≤ logarithmicMeanFactor q N y := by
  have h := mul_le_mul_of_nonneg_left (inverse_range_le_log (N / q + 1))
    (by positivity : 0 ≤ 4 * (N : ℝ) / q)
  unfold meanFactor logRowBound logarithmicMeanFactor
  change 2 * y + 2 * (2 * (N : ℝ) / q * harmonicRange (N / q + 1)) ≤ _
  simp only [harmonicRange, div_eq_mul_inv] at h ⊢
  nlinarith only [h]

theorem logarithmicMeanFactor_nonneg (q N : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ logarithmicMeanFactor q N y :=
  (meanFactor_nonneg q N hy).trans (meanFactor_le_logarithmic q N y)

theorem stripError_sq (q M : ℕ) (sigma y : ℝ) :
    stripError q M sigma y ^ 2 =
      4 * (q : ℝ) ^ 2 * (1 + y) ^ 2 * (M : ℝ) ^ (-2 * sigma) := by
  unfold stripError
  rw [mul_pow, mul_pow, mul_pow, ← Real.rpow_natCast ((M : ℝ) ^ (-sigma)) 2,
    ← Real.rpow_mul (Nat.cast_nonneg M)]
  norm_num only [Nat.cast_ofNat]
  rw [show (-sigma) * (2 : ℝ) = -2 * sigma by ring]

theorem Fmean_strip_log_bound (q : ℕ) [NeZero q] (X : ℝ)
    {M : ℕ} (hX : 1 < X) (hNM : ⌈X⌉₊ ≤ M) {sigma y : ℝ}
    (hs : 1 / 2 ≤ sigma) (hy : 0 ≤ y) :
    Fmean q X sigma y ≤
      2 * logarithmicMeanFactor q (M * ⌈X⌉₊ + 1) y *
        (⌈X⌉₊ : ℝ) ^ (1 - 2 * sigma) * (1 + Real.log (M * ⌈X⌉₊ : ℕ)) ^ 4 +
      8 * (q : ℝ) ^ 2 * (1 + y) ^ 2 * (M : ℝ) ^ (-2 * sigma) *
        logarithmicMeanFactor q ⌈X⌉₊ y * (1 + Real.log ⌈X⌉₊) := by
  have hN : 2 ≤ ⌈X⌉₊ := by
    have : 1 < ⌈X⌉₊ := Nat.lt_ceil.mpr (by simpa using hX)
    omega
  have hH : liuHarmonic (M * ⌈X⌉₊) ^ 4 ≤
      (1 + Real.log (M * ⌈X⌉₊ : ℕ)) ^ 4 := by
    apply pow_le_pow_left₀ _ (liuHarmonic_le_one_add_log _) 4
    unfold liuHarmonic
    positivity
  have hA := meanFactor_le_logarithmic q (M * ⌈X⌉₊ + 1) y
  have hP := mul_le_mul
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA (by norm_num : (0 : ℝ) ≤ 2))
      (by positivity : 0 ≤ (⌈X⌉₊ : ℝ) ^ (1 - 2 * sigma))) hH
    (by positivity)
    (mul_nonneg (mul_nonneg (by norm_num) (logarithmicMeanFactor_nonneg q _ hy))
      (by positivity))
  have hQ : mollifierMeanBound q X y ≤
      logarithmicMeanFactor q ⌈X⌉₊ y * (1 + Real.log ⌈X⌉₊) :=
    mul_le_mul (meanFactor_le_logarithmic q _ y) (inverse_range_le_log _)
      (harmonicRange_nonneg _) (logarithmicMeanFactor_nonneg q _ hy)
  have hR := mul_le_mul_of_nonneg_left hQ
    (by positivity : 0 ≤ 2 * stripError q M sigma y ^ 2)
  have h := (Fmean_strip_bound q X hX hNM hs hy).trans (add_le_add hP hR)
  rw [stripError_sq] at h
  exact h.trans_eq (by ring)

theorem FremainderMean_le_mixed_error (q : ℕ) [NeZero q] (X : ℝ)
    {M : ℕ} (hM : 1 ≤ M) {y : ℝ} (hy : 0 ≤ y) :
    FremainderMean q X M y ≤
      (4 * (q : ℝ) ^ 2 * (1 + y) ^ 2 * mollifierMeanBound q X y) / M := by
  have h := (FremainderMean_le_Qmean q X hM hy).trans
    (mul_le_mul_of_nonneg_left (Qmean_critical_le q X hy) (sq_nonneg _))
  apply h.trans_eq
  unfold truncationError
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg M)]
  ring

theorem FremainderMean_dyadic_mixed (q : ℕ) [NeZero q] (X : ℝ)
    {y : ℝ} (hy : 0 ≤ y) :
    Summable (fun k : ℕ => FremainderMean q X (2 ^ k) y) ∧
      (∑' k : ℕ, FremainderMean q X (2 ^ k) y) ≤
        8 * (q : ℝ) ^ 2 * (1 + y) ^ 2 * mollifierMeanBound q X y := by
  have h := dyadic_summable_of_reciprocal_bound (fun M => FremainderMean q X M y)
    (4 * (q : ℝ) ^ 2 * (1 + y) ^ 2 * mollifierMeanBound q X y)
    (fun M => FremainderMean_nonneg q X M hy)
    (fun _ hM => FremainderMean_le_mixed_error q X hM hy)
  exact ⟨h.1, h.2.trans_eq (by ring)⟩

end LiuWang.Proof.NonprincipalDensityMeans.Continuation
