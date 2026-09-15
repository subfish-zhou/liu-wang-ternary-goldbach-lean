import LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.ExponentialAxis

/-! An analytic weight for nonprincipal f itself, with no zeta pole regularization. -/

set_option autoImplicit false
noncomputable section

open Finset MeasureTheory Set Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.NonprincipalDensityAdvance
open Complex.HadamardThreeLines

namespace LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis

def cosineDetector {q : ℕ} [NeZero q] (chi : Character q) (X y : ℝ) (s : ℂ) : ℂ :=
  NonprincipalDensityAdvance.f chi X s / Complex.cos (s / (2 * (y : ℂ)))

def cosineMean (q : ℕ) [NeZero q] (X sigma y : ℝ) : ℝ :=
  (∑ chi ∈ nonprincipalCharacters q, ∫ t : ℝ,
    ‖cosineDetector chi X y ((sigma : ℂ) + t * Complex.I)‖ ^ 2) / q.totient

theorem cosine_lower {z : ℂ} (hz : |z.re| ≤ 1 / 2) :
    (1 / 4 : ℝ) * Real.exp |z.im| ≤ ‖Complex.cos z‖ := by
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using
    GlobalZeroDensity.norm_cos_ge_exp z (hz.trans (by norm_num))

theorem cosine_argument_small {y : ℝ} (hy : 2 ≤ y) {s : ℂ} (hs : |s.re| ≤ 1) :
    |(s / (2 * (y : ℂ))).re| ≤ 1 / 2 := by
  rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.div_ofReal_re,
    abs_div, abs_of_pos (by positivity : 0 < 2 * y)]
  apply (div_le_iff₀ (by positivity : 0 < 2 * y)).mpr
  linarith

theorem cosine_denominator_ne_zero {y : ℝ} (hy : 2 ≤ y) {s : ℂ} (hs : |s.re| ≤ 1) :
    Complex.cos (s / (2 * (y : ℂ))) ≠ 0 :=
  norm_pos_iff.mp ((by positivity : (0 : ℝ) < (1 / 4) * Real.exp |(s / (2 * (y : ℂ))).im|).trans_le
    (cosine_lower (cosine_argument_small hy hs)))

theorem cosineDetector_decay {q : ℕ} [NeZero q] (chi : Character q) (X : ℝ)
    {y : ℝ} (hy : 2 ≤ y) {s : ℂ} (hs : |s.re| ≤ 1) :
    ‖cosineDetector chi X y s‖ ≤
      4 * ‖NonprincipalDensityAdvance.f chi X s‖ * Real.exp (-|s.im| / (2 * y)) := by
  have hc := cosine_lower (cosine_argument_small hy hs)
  have hi : |(s / (2 * (y : ℂ))).im| = |s.im| / (2 * y) := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.div_ofReal_im,
      abs_div, abs_of_pos (by positivity : 0 < 2 * y)]
  rw [hi] at hc
  have hinv := one_div_le_one_div_of_le (by positivity) hc
  have he : 1 / ((1 / 4 : ℝ) * Real.exp (|s.im| / (2 * y))) =
      4 * Real.exp (-|s.im| / (2 * y)) := by
    rw [neg_div, Real.exp_neg]
    field_simp
  rw [he] at hinv
  have h := mul_le_mul_of_nonneg_left hinv (norm_nonneg (NonprincipalDensityAdvance.f chi X s))
  unfold cosineDetector
  rw [norm_div]
  simpa only [div_eq_mul_inv, one_mul, mul_assoc, mul_comm, mul_left_comm] using h

theorem cosineDetector_weight {q : ℕ} [NeZero q] (chi : Character q) (X : ℝ)
    {y : ℝ} (hy : 2 ≤ y) {s : ℂ} (hs : |s.re| ≤ 1) :
    ‖cosineDetector chi X y s‖ ^ 2 ≤
      16 * ‖NonprincipalDensityAdvance.f chi X s‖ ^ 2 * Real.exp (-|s.im| / y) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (cosineDetector_decay chi X hy hs) 2
  rw [mul_pow, mul_pow, ← Real.exp_nat_mul] at h
  norm_num only [Nat.cast_ofNat] at h
  have he : 2 * (-|s.im| / (2 * y)) = -|s.im| / y := by ring
  simpa only [he, show (4 : ℝ) ^ 2 = 16 by norm_num] using h

theorem cosineDetector_diffAt {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (X : ℝ) {y : ℝ} (hy : 2 ≤ y) {s : ℂ} (hs : |s.re| ≤ 1) :
    DifferentiableAt ℂ (cosineDetector chi X y) s :=
  (differentiable_f hchi X s).div ((differentiableAt_id.div_const _).ccos)
    (cosine_denominator_ne_zero hy hs)

theorem cosineDetector_diffContOnCl {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (X : ℝ) {y : ℝ} (hy : 2 ≤ y) :
    DiffContOnCl ℂ (cosineDetector chi X y) (verticalStrip (1 / 2) 1) := by
  apply DifferentiableOn.diffContOnCl
  rw [verticalStrip, Complex.closure_preimage_re, closure_Ioo (by norm_num : (1 / 2 : ℝ) ≠ 1)]
  intro s hs
  apply (cosineDetector_diffAt hchi X hy _).differentiableWithinAt
  exact abs_le.mpr ⟨by linarith [hs.1], hs.2⟩

theorem continuous_cosineDetector_vertical {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (X : ℝ) {y sigma : ℝ} (hy : 2 ≤ y) (hs : |sigma| ≤ 1) :
    Continuous (fun t : ℝ => cosineDetector chi X y ((sigma : ℂ) + t * Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hv : Continuous (fun t : ℝ => (sigma : ℂ) + t * Complex.I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  exact (cosineDetector_diffAt hchi X hy (by simpa using hs)).continuousAt.comp hv.continuousAt

theorem cosine_integrable_of_exponential {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (X : ℝ) {y sigma : ℝ} (hy : 2 ≤ y) (hs : |sigma| ≤ 1)
    (hi : Integrable (fun t : ℝ =>
      ‖NonprincipalDensityAdvance.f chi X ((sigma : ℂ) + t * Complex.I)‖ ^ 2 *
        Real.exp (-|t| / y))) :
    Integrable (fun t : ℝ => ‖cosineDetector chi X y ((sigma : ℂ) + t * Complex.I)‖ ^ 2) := by
  apply (hi.const_mul 16).mono' ((continuous_cosineDetector_vertical hchi X hy hs).norm.pow 2).aestronglyMeasurable
  filter_upwards with t
  simp only [Pi.pow_apply]
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
    Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add, mul_assoc] using
    cosineDetector_weight chi X hy (s := (sigma : ℂ) + t * Complex.I) (by simpa using hs)

theorem cosineMean_le_exponential (q : ℕ) [NeZero q] (X : ℝ) {y sigma : ℝ}
    (hy : 2 ≤ y) (hs : |sigma| ≤ 1)
    (hi : ∀ chi ∈ nonprincipalCharacters q, Integrable (fun t : ℝ =>
      ‖NonprincipalDensityAdvance.f chi X ((sigma : ℂ) + t * Complex.I)‖ ^ 2 *
        Real.exp (-|t| / y))) :
    cosineMean q X sigma y ≤ 16 * exponentialMean q X sigma y := by
  have hb (chi : Character q) (hc : chi ∈ nonprincipalCharacters q) :
      (∫ t : ℝ, ‖cosineDetector chi X y ((sigma : ℂ) + t * Complex.I)‖ ^ 2) ≤
      16 * (∫ t : ℝ, ‖NonprincipalDensityAdvance.f chi X ((sigma : ℂ) + t * Complex.I)‖ ^ 2 *
        Real.exp (-|t| / y)) := by
    have h := integral_mono (cosine_integrable_of_exponential ((mem_nonprincipalCharacters chi).mp hc)
      X hy hs (hi chi hc)) ((hi chi hc).const_mul 16) (fun t => by
        simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
          Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add, mul_assoc] using
          cosineDetector_weight chi X hy (s := (sigma : ℂ) + t * Complex.I) (by simpa using hs))
    rwa [integral_const_mul] at h
  have h := div_le_div_of_nonneg_right (sum_le_sum (s := nonprincipalCharacters q) hb) (Nat.cast_nonneg q.totient)
  unfold cosineMean exponentialMean
  rw [← mul_sum] at h
  exact h.trans_eq (by ring)

theorem cosine_right_fixed_X (q : ℕ) [NeZero q] {y : ℝ} (hy : 2 ≤ y) :
    cosineMean q ((q : ℝ) * y) 1 y ≤
      4620288 * (1 + Real.log ((q : ℝ) * y)) ^ 5 / q := by
  have h := exponential_right_fixed_X q hy (sigma := 1) le_rfl
  exact (cosineMean_le_exponential q _ hy (by norm_num) h.1).trans
    ((mul_le_mul_of_nonneg_left h.2 (by norm_num : (0 : ℝ) ≤ 16)).trans_eq (by ring))

theorem cosine_critical_fixed_X (q : ℕ) [NeZero q] {y : ℝ} (hy : 2 ≤ y)
    {M : ℕ} (hM : 2 ≤ M) :
    cosineMean q ((q : ℝ) * y) (1 / 2) y ≤ 256 * criticalBudget q ((q : ℝ) * y) M y := by
  have h := exponential_critical_fixed_X q hy hM
  have hi : ∀ chi ∈ nonprincipalCharacters q, Integrable (fun t : ℝ =>
      ‖NonprincipalDensityAdvance.f chi ((q : ℝ) * y) (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 2 *
        Real.exp (-|t| / y)) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using h.1
  exact (cosineMean_le_exponential q _ hy (by norm_num) hi).trans
    ((mul_le_mul_of_nonneg_left h.2 (by norm_num : (0 : ℝ) ≤ 16)).trans_eq (by ring))

end LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis
