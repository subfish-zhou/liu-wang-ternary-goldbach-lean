import LiuWang.Proof.Campaign20260915.ZetaIntegerEta.PolynomialLimits

set_option autoImplicit false
noncomputable section
open Complex

namespace LiuWang.Proof.Campaign20260915.ZetaIntegerEta
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

theorem gaussianJet_parity_factor (c : ℂ) {j k : ℕ} (hj : j ≤ k) :
    (-1 : ℂ) ^ j * gaussianJet c (k - j) =
      (-1 : ℂ) ^ k * gaussianJet c (k - j) := by
  rcases Nat.even_or_odd (k - j) with he | ho
  · have hk : (-1 : ℂ) ^ k = (-1 : ℂ) ^ j := by
      conv_lhs => rw [← Nat.add_sub_of_le hj, pow_add]
      rw [he.neg_one_pow, mul_one]
    rw [hk]
  · obtain ⟨a, ha⟩ := ho
    rw [show k - j = 2 * a + 1 by omega, gaussianJet_odd, mul_zero, mul_zero]

theorem correctionMoment_parity (k : ℕ) {z : ℝ} (hz : |z| < 3 / 2) :
    correctionMoment k (-z) = (-1 : ℂ) ^ k * correctionMoment k z := by
  have hp : (2 * Real.pi * I : ℂ) ^ k ≠ 0 := pow_ne_zero _ mordellFrequency_ne_zero
  apply mul_left_cancel₀ hp
  have hn := correctionMoment_phi_derivatives k (by simpa using hz : |-z| < 3 / 2)
  rw [ofReal_neg] at hn
  rw [hn, mul_left_comm, correctionMoment_phi_derivatives k hz, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [rsPhi_deriv_parity]
  push_cast
  have hg := gaussianJet_parity_factor (Real.pi * I / 2)
    (show j ≤ k by have := Finset.mem_range.mp hj; omega)
  linear_combination (k.choose j : ℂ) * (iteratedDeriv j rsPhi z : ℝ) * hg

theorem correctionMoment_endpoint_parity (k : ℕ) :
    correctionMoment k (-1) = (-1 : ℂ) ^ k * correctionMoment k 1 := by
  simpa only [ofReal_one] using correctionMoment_parity k (by norm_num : |(1 : ℝ)| < 3 / 2)

theorem sourcePolynomial_endpoint_jump (sigma : ℝ) (n N : ℕ) :
    (sourceGaussianPhase ((n : ℝ) + 1) (n + 1) *
      ∑ k ∈ Finset.range N, rsSaddleCoefficient sigma (rsSaddleScale * ((n : ℝ) + 1)) k *
        (rsSaddleScale : ℂ) ^ k * correctionMoment k (-1)) -
    (sourceGaussianPhase ((n : ℝ) + 1) n *
      ∑ k ∈ Finset.range N, rsSaddleCoefficient sigma (rsSaddleScale * ((n : ℝ) + 1)) k *
        (rsSaddleScale : ℂ) ^ k * correctionMoment k 1) =
    sourceGaussianPhase ((n : ℝ) + 1) (n + 1) *
      ∑ k ∈ Finset.range N, ((-1 : ℂ) ^ k + 1) *
        (rsSaddleCoefficient sigma (rsSaddleScale * ((n : ℝ) + 1)) k *
          (rsSaddleScale : ℂ) ^ k * correctionMoment k 1) := by
  simp_rw [correctionMoment_endpoint_parity]
  rw [sourceGaussianPhase_endpoint_jump, neg_mul, sub_neg_eq_add, ← mul_add,
    ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem sourcePolynomial_seven_endpoint_jump (n : ℕ) :
    (sourceGaussianPhase ((n : ℝ) + 1) (n + 1) *
      ∑ k ∈ Finset.range 7, rsSaddleCoefficient (1 / 2) (rsSaddleScale * ((n : ℝ) + 1)) k *
        (rsSaddleScale : ℂ) ^ k * correctionMoment k (-1)) -
    (sourceGaussianPhase ((n : ℝ) + 1) n *
      ∑ k ∈ Finset.range 7, rsSaddleCoefficient (1 / 2) (rsSaddleScale * ((n : ℝ) + 1)) k *
        (rsSaddleScale : ℂ) ^ k * correctionMoment k 1) =
    2 * sourceGaussianPhase ((n : ℝ) + 1) (n + 1) *
      (correctionMoment 0 1 +
        3 / (8 * (((n : ℝ) + 1 : ℝ) : ℂ) ^ 2) * correctionMoment 2 1 +
        (-(5 * Real.pi * I) / (6 * (((n : ℝ) + 1 : ℝ) : ℂ) ^ 2) +
          35 / (128 * (((n : ℝ) + 1 : ℝ) : ℂ) ^ 4)) * correctionMoment 4 1 +
        (-(2 * Real.pi ^ 2) / (9 * (((n : ℝ) + 1 : ℝ) : ℂ) ^ 2) -
          223 * Real.pi * I / (240 * (((n : ℝ) + 1 : ℝ) : ℂ) ^ 4) +
          231 / (1024 * (((n : ℝ) + 1 : ℝ) : ℂ) ^ 6)) * correctionMoment 6 1) := by
  have he : 0 < (n : ℝ) + 1 := by positivity
  rw [sourcePolynomial_endpoint_jump]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, pow_one, neg_mul, neg_neg, one_mul, mul_one, rsSaddle_coefficient_zero]
  rw [sourceSaddle_scaled_two he, sourceSaddle_scaled_four he, sourceSaddle_scaled_six he]
  ring

end LiuWang.Proof.Campaign20260915.ZetaIntegerEta
