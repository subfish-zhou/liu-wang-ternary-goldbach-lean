import LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.StripGrowth

/-! Recover the original f on its true finite window, including actual L-zero detection. -/

set_option autoImplicit false
noncomputable section

open Finset MeasureTheory Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.NonprincipalDensityAdvance

namespace LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis

theorem f_eq_cosine_mul {q : ℕ} [NeZero q] (chi : Character q) (X : ℝ)
    {y : ℝ} (hy : 2 ≤ y) {s : ℂ} (hs : |s.re| ≤ 1) :
    NonprincipalDensityAdvance.f chi X s =
      cosineDetector chi X y s * Complex.cos (s / (2 * (y : ℂ))) := by
  rw [cosineDetector, div_mul_cancel₀ _ (cosine_denominator_ne_zero hy hs)]

theorem cosineDetector_zero_iff {q : ℕ} [NeZero q] (chi : Character q) (X : ℝ)
    {y : ℝ} (hy : 2 ≤ y) {s : ℂ} (hs : |s.re| ≤ 1) :
    cosineDetector chi X y s = 0 ↔ NonprincipalDensityAdvance.f chi X s = 0 := by
  rw [cosineDetector, div_eq_zero_iff]
  simp only [cosine_denominator_ne_zero hy hs, or_false]

theorem window_cosine_sq {y : ℝ} (hy : 2 ≤ y) {s : ℂ} (ht : |s.im| ≤ y) :
    ‖Complex.cos (s / (2 * (y : ℂ)))‖ ^ 2 ≤ 3 := by
  let z := s / (2 * (y : ℂ))
  have hcosh : Real.cosh z.im ≤ Real.exp |z.im| := by
    rw [← Real.cosh_abs, Real.cosh_eq]
    have h := Real.exp_le_exp.mpr (show -|z.im| ≤ |z.im| by linarith [abs_nonneg z.im])
    linarith
  have hc := pow_le_pow_left₀ (norm_nonneg _)
    ((GlobalZeroDensity.Strip.norm_cos_le_cosh z).trans hcosh) 2
  rw [← Real.exp_nat_mul] at hc
  have hi : |z.im| = |s.im| / (2 * y) := by
    dsimp [z]
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.div_ofReal_im,
      abs_div, abs_of_pos (by positivity : 0 < 2 * y)]
  have harg : 2 * |z.im| ≤ 1 := by
    rw [hi]
    have h : |s.im| / (2 * y) ≤ 1 / 2 :=
      (div_le_iff₀ (by positivity : 0 < 2 * y)).mpr (by linarith)
    linarith
  have h := Real.exp_le_exp.mpr harg
  have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
  exact hc.trans (h.trans he)

theorem f_window_le_cosine {q : ℕ} [NeZero q] (chi : Character q) (X : ℝ)
    {y : ℝ} (hy : 2 ≤ y) {s : ℂ} (hs : |s.re| ≤ 1) (ht : |s.im| ≤ y) :
    ‖NonprincipalDensityAdvance.f chi X s‖ ^ 2 ≤ 3 * ‖cosineDetector chi X y s‖ ^ 2 := by
  rw [f_eq_cosine_mul chi X hy hs, norm_mul, mul_pow]
  have h := mul_le_mul_of_nonneg_left (window_cosine_sq hy ht)
    (sq_nonneg ‖cosineDetector chi X y s‖)
  exact h.trans_eq (mul_comm _ _)

theorem actual_L_zero_detected {q : ℕ} [NeZero q] (chi : Character q) (X : ℝ)
    {y : ℝ} (hy : 2 ≤ y) {rho : ℂ} (hr : |rho.re| ≤ 1) (hi : |rho.im| ≤ y)
    (hz : chi.LFunction rho = 0) :
    (1 / 3 : ℝ) ≤ ‖cosineDetector chi X y rho‖ ^ 2 := by
  have h := f_window_le_cosine chi X hy hr hi
  simp only [NonprincipalDensityAdvance.f, hz, zero_mul, zero_sub, norm_neg,
    norm_one, one_pow] at h
  linarith

theorem Fmean_le_cosineMean (q : ℕ) [NeZero q] (X : ℝ) {y sigma : ℝ}
    (hy : 2 ≤ y) (hs : sigma ∈ Set.Icc (1 / 2) 1) :
    Fmean q X sigma y ≤ 3 * cosineMean q X sigma y := by
  have his (chi : Character q) (hchi : chi ∈ nonprincipalCharacters q) :
      (∫ t in -y..y, ‖NonprincipalDensityAdvance.f chi X ((sigma : ℂ) + t * Complex.I)‖ ^ 2) ≤
      3 * (∫ t : ℝ, ‖cosineDetector chi X y ((sigma : ℂ) + t * Complex.I)‖ ^ 2) := by
    have hn : chi ≠ 1 := (mem_nonprincipalCharacters chi).mp hchi
    have hg := cosine_strip_integrable hn X hy hs
    have hgi : IntervalIntegrable (fun t : ℝ =>
        ‖cosineDetector chi X y ((sigma : ℂ) + t * Complex.I)‖ ^ 2) volume (-y) y :=
      ((continuous_cosineDetector_vertical hn X hy
        (abs_le.mpr ⟨by linarith [hs.1], hs.2⟩)).norm.pow 2).intervalIntegrable (-y) y
    have h := intervalIntegral.integral_mono_on (by linarith : -y ≤ y)
      (f_vertical_integrable hn X sigma y) (hgi.const_mul 3) (fun t ht => by
        apply f_window_le_cosine chi X hy
        · simpa using abs_le.mpr ⟨(by linarith [hs.1] : -1 ≤ sigma), hs.2⟩
        · simpa using abs_le.mpr ht)
    rw [intervalIntegral.integral_const_mul] at h
    have hw : (∫ t in -y..y, ‖cosineDetector chi X y ((sigma : ℂ) + t * Complex.I)‖ ^ 2) ≤
        ∫ t : ℝ, ‖cosineDetector chi X y ((sigma : ℂ) + t * Complex.I)‖ ^ 2 := by
      rw [intervalIntegral.integral_of_le (by linarith : -y ≤ y)]
      exact setIntegral_le_integral hg (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    exact h.trans (mul_le_mul_of_nonneg_left hw (by norm_num))
  have h := div_le_div_of_nonneg_right (sum_le_sum (s := nonprincipalCharacters q) his) (Nat.cast_nonneg q.totient)
  rw [← mul_sum] at h
  exact h.trans_eq (by unfold cosineMean; ring)

end LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis
