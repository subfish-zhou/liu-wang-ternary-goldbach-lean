import LiuWang.Proof.Campaign20260915.ZetaValidation.SecondOrderEvaluation
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Analysis.Calculus.Deriv.Polynomial

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def bernoulliCoefficientBound (k : ℕ) : ℚ :=
  (∑ j ∈ Finset.range (k + 1), |bernoulli j| * (k.choose j : ℚ)) / k.factorial

noncomputable section

open Complex Polynomial Finset MeasureTheory Set

def normalizedBernoulli (k : ℕ) (x : ℝ) : ℝ :=
  aeval x (Polynomial.bernoulli k) / k.factorial

def bernoulliKernel (k : ℕ) (s : ℂ) (u : ℝ) : ℂ :=
  (normalizedBernoulli k (Int.fract u) : ℂ) * (u : ℂ) ^ (-s - k)

theorem normalizedBernoulli_zero (k : ℕ) :
    normalizedBernoulli k 0 = (bernoulli k : ℝ) / k.factorial := by
  simp [normalizedBernoulli, aeval_def, Polynomial.coeff_bernoulli]

theorem normalizedBernoulli_one (k : ℕ) (hk : k ≠ 1) :
    normalizedBernoulli k 1 = normalizedBernoulli k 0 := by
  simp [normalizedBernoulli, aeval_def, Polynomial.coeff_bernoulli,
    bernoulli_eq_bernoulli'_of_ne_one hk]

theorem normalizedBernoulli_first (x : ℝ) :
    normalizedBernoulli 1 x = x - 1 / 2 := by
  simp [normalizedBernoulli, Polynomial.bernoulli_one, aeval_def]

theorem hasDerivAt_normalizedBernoulli (k : ℕ) (x : ℝ) :
    HasDerivAt (normalizedBernoulli (k + 1)) (normalizedBernoulli k x) x := by
  have h := ((Polynomial.bernoulli (k + 1)).hasDerivAt_aeval x).div_const
    (((k + 1).factorial : ℕ) : ℝ)
  rw [Polynomial.derivative_bernoulli_add_one] at h
  have he : ((aeval x) (((k : ℚ[X]) + 1) * Polynomial.bernoulli k) : ℝ) /
      (k + 1).factorial = normalizedBernoulli k x := by
    simp only [map_mul, map_add, map_natCast, map_one]
    rw [normalizedBernoulli, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
  rw [he] at h
  exact h

theorem continuous_normalizedBernoulli (k : ℕ) : Continuous (normalizedBernoulli k) := by
  unfold normalizedBernoulli
  exact (Polynomial.continuous_aeval _).div_const _

theorem normalizedBernoulli_expansion (k : ℕ) (x : ℝ) :
    normalizedBernoulli k x =
      (∑ j ∈ range (k + 1), (bernoulli j : ℝ) * (k.choose j : ℝ) * x ^ (k - j)) /
        k.factorial := by
  simp [normalizedBernoulli, Polynomial.bernoulli, aeval_def]

theorem abs_normalizedBernoulli_le (k : ℕ) {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    |normalizedBernoulli k x| ≤ (bernoulliCoefficientBound k : ℝ) := by
  rw [normalizedBernoulli_expansion, abs_div,
    abs_of_pos (show (0 : ℝ) < k.factorial by positivity)]
  unfold bernoulliCoefficientBound
  push_cast
  gcongr
  calc
    _ ≤ ∑ j ∈ range (k + 1),
        |(bernoulli j : ℝ) * (k.choose j : ℝ) * x ^ (k - j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (k.choose j) : (0 : ℝ) ≤ k.choose j),
        abs_of_nonneg (pow_nonneg hx.1 _)]
      have hp : x ^ (k - j) ≤ 1 := pow_le_one₀ hx.1 hx.2
      nlinarith [mul_nonneg (abs_nonneg (bernoulli j : ℝ)) (Nat.cast_nonneg (k.choose j))]

theorem bernoulliCoefficientBound_nonneg (k : ℕ) : 0 ≤ bernoulliCoefficientBound k := by
  unfold bernoulliCoefficientBound
  positivity

theorem bernoulliKernel_first (s : ℂ) (u : ℝ) :
    bernoulliKernel 1 s u = centeredAbelKernel s u := by
  simp [bernoulliKernel, normalizedBernoulli_first, centeredAbelKernel]

theorem norm_bernoulliKernel_le (k : ℕ) (s : ℂ) {u : ℝ} (hu : 0 < u) :
    ‖bernoulliKernel k s u‖ ≤
      (bernoulliCoefficientBound k : ℝ) * u ^ (-s.re - k) := by
  rw [bernoulliKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hu]
  simp only [sub_re, neg_re, natCast_re]
  exact mul_le_mul_of_nonneg_right
    (abs_normalizedBernoulli_le k ⟨Int.fract_nonneg u, (Int.fract_lt_one u).le⟩)
    (Real.rpow_nonneg hu.le _)

theorem bernoulliKernel_integrable (k : ℕ) {s : ℂ} (hs : 1 < s.re + k)
    {a : ℝ} (ha : 0 < a) : IntegrableOn (bernoulliKernel k s) (Ioi a) := by
  have hm : AEStronglyMeasurable (bernoulliKernel k s) (volume.restrict (Ioi a)) := by
    unfold bernoulliKernel
    exact (((continuous_normalizedBernoulli k).measurable.comp measurable_fract).complex_ofReal.mul
      (Complex.measurable_ofReal.pow_const (-s - k))).aestronglyMeasurable
  refine IntegrableOn.mono'
    ((integrableOn_Ioi_rpow_of_lt (by linarith : -s.re - k < -1) ha).const_mul
      (bernoulliCoefficientBound k : ℝ)) hm ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact norm_bernoulliKernel_le k s (ha.trans hu)

theorem norm_bernoulliTail_le (k : ℕ) {s : ℂ} (hs : 1 < s.re + k)
    {a : ℝ} (ha : 0 < a) :
    ‖∫ u in Ioi a, bernoulliKernel k s u‖ ≤
      (bernoulliCoefficientBound k : ℝ) * a ^ (1 - s.re - k) / (s.re + k - 1) := by
  calc
    _ ≤ ∫ u in Ioi a, (bernoulliCoefficientBound k : ℝ) * u ^ (-s.re - k) := by
      apply norm_integral_le_of_norm_le
        ((integrableOn_Ioi_rpow_of_lt (by linarith : -s.re - k < -1) ha).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact norm_bernoulliKernel_le k s (ha.trans hu)
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) ha]
      rw [show -s.re - (k : ℝ) + 1 = -(s.re + k - 1) by ring, neg_div_neg_eq,
        show -(s.re + (k : ℝ) - 1) = 1 - s.re - k by ring]
      ring

end

end LiuWang.Proof.Campaign20260915.ZetaValidation
