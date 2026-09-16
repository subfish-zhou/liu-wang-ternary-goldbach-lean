import LiuWang.Proof.Campaign20260915.ZetaRealNormalization.CriticalAmplitude

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Set

namespace LiuWang.Proof.Campaign20260915.ZetaRealNormalization
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell
open LiuWang.Proof.Campaign20260915.ZetaJnCentral

theorem source_positive_moment_gaussian {eta : ℝ} {m : ℕ}
    (h0 : 0 < eta - m) (h1 : eta - m < 1) (n : ℕ) :
    ‖correctionMoment (n + 1) (sourcePhiParameter eta m)‖ ≤ exactGaussianBudget Real.pi n := by
  have hG : ‖sourceGaussianPhase eta m‖ = 1 := by
    rw [sourceGaussianPhase, norm_exp]
    simp [mul_re, mul_im, pow_two]
  have hI := congrArg norm (sourceGaussian_moment_integral h0 h1 (n + 1))
  rw [norm_neg, norm_mul, hG, one_mul] at hI
  rw [← hI]
  change ‖∫ y : ℝ, gaussianMonomial eta m n y‖ ≤ _
  have hp (y : ℝ) : ‖gaussianMonomial eta m n y‖ ≤ exactGaussianWeight Real.pi n y := by
    by_cases hy : y = 0
    · subst y
      simp only [gaussianMonomial, rsDescentPoint, ofReal_zero, mul_zero, add_zero,
        sub_self, zero_pow (Nat.succ_ne_zero n), mul_zero, norm_zero]
      unfold exactGaussianWeight
      positivity
    rw [gaussianMonomial, norm_mul, norm_mul, rsDescentDirection_norm, one_mul,
      norm_pow, rsDescentPoint_distance, pow_succ]
    have h := mul_le_mul_of_nonneg_right (gaussian_times_distance eta m hy h0.le h1.le)
      (pow_nonneg (abs_nonneg y) n)
    simpa only [exactGaussianWeight, mul_assoc, mul_comm, mul_left_comm] using h
  calc
    _ ≤ ∫ y : ℝ, ‖gaussianMonomial eta m n y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y : ℝ, exactGaussianWeight Real.pi n y :=
      integral_mono (gaussianMonomial_integrable eta m n h0.le h1.le).norm
        (exactGaussianWeight_integrable Real.pi_pos n) hp
    _ = _ := exactGaussianWeight_integral Real.pi_pos n

theorem source_positive_moment_rational {eta : ℝ} {m : ℕ}
    (h0 : 0 < eta - m) (h1 : eta - m < 1) (n : ℕ) :
    ‖correctionMoment (n + 1) (sourcePhiParameter eta m)‖ ≤
      rationalGaussianMoment (n + 1) + (250 / 1099) * rationalGaussianMoment n :=
  (source_positive_moment_gaussian h0 h1 n).trans (exactGaussianBudget_rational n)

theorem source_moments_one_to_six {eta : ℝ} {m : ℕ}
    (h0 : 0 < eta - m) (h1 : eta - m < 1) :
    ‖correctionMoment 1 (sourcePhiParameter eta m)‖ ≤ 3 / 5 ∧
    ‖correctionMoment 2 (sourcePhiParameter eta m)‖ ≤ 1 / 4 ∧
    ‖correctionMoment 3 (sourcePhiParameter eta m)‖ ≤ 1 / 5 ∧
    ‖correctionMoment 4 (sourcePhiParameter eta m)‖ ≤ 1 / 10 ∧
    ‖correctionMoment 5 (sourcePhiParameter eta m)‖ ≤ 1 / 10 ∧
    ‖correctionMoment 6 (sourcePhiParameter eta m)‖ ≤ 1 / 10 := by
  refine ⟨(source_positive_moment_rational h0 h1 0).trans ?_,
    (source_positive_moment_rational h0 h1 1).trans ?_,
    (source_positive_moment_rational h0 h1 2).trans ?_,
    (source_positive_moment_rational h0 h1 3).trans ?_,
    (source_positive_moment_rational h0 h1 4).trans ?_,
    (source_positive_moment_rational h0 h1 5).trans ?_⟩ <;>
    norm_num [rationalGaussianMoment]

theorem source_phi_one_amplitude {eta : ℝ} {m : ℕ}
    (h0 : 0 < eta - m) (h1 : eta - m < 1) :
    |rsPhiOne (sourcePhiParameter eta m)| ≤ 1 := by
  let z := sourcePhiParameter eta m
  have hm := source_moments_one_to_six h0 h1
  have h := norm_sub_le (correctionMoment 1 z / 2)
    ((2 / 3 : ℂ) * Real.pi * I * correctionMoment 3 z)
  rw [correctionMoment_one_three_phi (sourcePhiParameter_domain h0.le h1.le)] at h
  norm_num only [norm_real, Real.norm_eq_abs, norm_div, norm_mul, norm_ofNat,
    norm_I, mul_one, abs_of_pos Real.pi_pos] at h
  have h3 := mul_le_mul_of_nonneg_left hm.2.2.1 (by positivity : 0 ≤ (2 / 3 : ℝ) * Real.pi)
  have h1' := div_le_div_of_nonneg_right hm.1 (by norm_num : (0 : ℝ) ≤ 2)
  dsimp only [z] at h
  nlinarith [Real.pi_lt_four]

theorem source_phi_two_amplitude {eta : ℝ} {m : ℕ}
    (h0 : 0 < eta - m) (h1 : eta - m < 1) :
    |rsPhiTwo (sourcePhiParameter eta m)| ≤ 1 := by
  let z := sourcePhiParameter eta m
  have hz := sourcePhiParameter_domain h0.le h1.le
  have hm := source_moments_one_to_six h0 h1
  have h0' : ‖correctionMoment 0 z‖ ≤ 4 := by
    rw [correctionMoment_zero_phi hz, norm_real, Real.norm_eq_abs]
    exact criticalPhi_amplitude (sourcePhiParameter_mem h0.le h1.le)
  have h6 : ‖-(2 / 9 : ℂ) * Real.pi ^ 2 * correctionMoment 6 z‖ ≤ 16 / 45 := by
    have hp : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
    norm_num only [norm_mul, norm_neg, norm_div, norm_ofNat, norm_pow, norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    exact (mul_le_mul
      (mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2 / 9))
      hm.2.2.2.2.2 (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2 / 9 * 16)).trans_eq (by norm_num)
  have h4 : ‖(5 / 6 : ℂ) * Real.pi * I * correctionMoment 4 z‖ ≤ 1 / 3 := by
    norm_num only [norm_mul, norm_div, norm_ofNat, norm_I, norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one]
    exact (mul_le_mul
      (mul_le_mul_of_nonneg_left Real.pi_lt_four.le (by norm_num : (0 : ℝ) ≤ 5 / 6))
      hm.2.2.2.1 (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 5 / 6 * 4)).trans_eq (by norm_num)
  have h2 : ‖(3 / 8 : ℂ) * correctionMoment 2 z‖ ≤ 3 / 32 := by
    norm_num only [norm_mul, norm_div, norm_ofNat]
    exact (mul_le_mul_of_nonneg_left hm.2.1 (by norm_num : (0 : ℝ) ≤ 3 / 8)).trans_eq (by norm_num)
  have hzero : ‖I / (96 * Real.pi) * correctionMoment 0 z‖ ≤ 1 / 72 := by
    norm_num only [norm_mul, norm_div, norm_ofNat, norm_I, norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have hpi : 1 / (96 * Real.pi) ≤ (1 / 288 : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      linarith [Real.pi_gt_three]
    exact (mul_le_mul hpi h0' (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 288)).trans_eq
      (by norm_num)
  have h := ((norm_sub_le
    (-(2 / 9 : ℂ) * Real.pi ^ 2 * correctionMoment 6 z -
      (5 / 6 : ℂ) * Real.pi * I * correctionMoment 4 z +
        (3 / 8 : ℂ) * correctionMoment 2 z)
    (I / (96 * Real.pi) * correctionMoment 0 z)).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add
        ((norm_sub_le _ _).trans (add_le_add h6 h4)) h2)) hzero))
  rw [correctionMoment_two_four_six_phi hz, norm_real, Real.norm_eq_abs] at h
  exact h.trans (by norm_num)

#print axioms source_positive_moment_gaussian
#print axioms source_moments_one_to_six
#print axioms source_phi_one_amplitude
#print axioms source_phi_two_amplitude

end LiuWang.Proof.Campaign20260915.ZetaRealNormalization
