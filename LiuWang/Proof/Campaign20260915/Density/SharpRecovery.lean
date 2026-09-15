import LiuWang.Proof.Campaign20260915.Density.FamilyInterpolation

set_option autoImplicit false
noncomputable section

open Finset Complex MeasureTheory Set
open LiuWang.Proof.Interfaces (Character)
open LiuWang.Proof.NonprincipalDensityAdvance (nonprincipalCharacters)
open LiuWang.Proof.NonprincipalDensityMeans
open LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis
open LiuWang.Proof.DirichletZeroCount.Applications
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.Density

theorem cosh_half_sq_source : Real.cosh (1 / 2) ^ 2 ≤ 1.272 := by
  have he : Real.exp 1 ≤ 2.719 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have hn : Real.exp (-1) ≤ 0.368 := by
    rw [Real.exp_neg, ← one_div]
    apply (div_le_iff₀ (Real.exp_pos 1)).mpr
    nlinarith [Real.exp_one_gt_d9]
  have htwo := Real.cosh_two_mul (1 / 2)
  rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.cosh_eq] at htwo
  nlinarith [Real.cosh_sq_sub_sinh_sq (1 / 2)]

theorem source_cosine_equation_33 {y : ℝ} (hy : 0 < y) {s : ℂ} (ht : |s.im| ≤ y) :
    ‖Complex.cos (s / (2 * (y : ℂ)))‖ ^ 2 ≤ 1.272 := by
  have hi : |(s / (2 * (y : ℂ))).im| ≤ 1 / 2 := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.div_ofReal_im,
      abs_div, abs_of_pos (by positivity : 0 < 2 * y)]
    apply (div_le_iff₀ (by positivity : 0 < 2 * y)).mpr
    linarith
  have hc := Real.cosh_le_cosh.mpr
    (show |(s / (2 * (y : ℂ))).im| ≤ |(1 / 2 : ℝ)| by simpa using hi)
  exact (pow_le_pow_left₀ (norm_nonneg _)
    ((GlobalZeroDensity.Strip.norm_cos_le_cosh _).trans hc) 2).trans cosh_half_sq_source

theorem f_window_le_cosine_sharp {q : ℕ} [NeZero q] (chi : Character q) (X : ℝ)
    {y : ℝ} (hy : 2 ≤ y) {s : ℂ} (hs : |s.re| ≤ 2) (ht : |s.im| ≤ y) :
    ‖NonprincipalDensityAdvance.f chi X s‖ ^ 2 ≤ 1.272 * ‖cosineDetector chi X y s‖ ^ 2 := by
  have he : NonprincipalDensityAdvance.f chi X s =
      cosineDetector chi X y s * Complex.cos (s / (2 * (y : ℂ))) := by
    rw [cosineDetector, div_mul_cancel₀ _ (cosine_denominator_extended hy hs)]
  conv_lhs => rw [he, norm_mul, mul_pow]
  exact (mul_le_mul_of_nonneg_left (source_cosine_equation_33 (by linarith) ht)
    (sq_nonneg ‖cosineDetector chi X y s‖)).trans_eq (mul_comm _ _)

theorem family_window_le_cosine_sharp (q : ℕ) [NeZero q] (X : ℝ) {y sigma : ℝ}
    (hy : 2 ≤ y) (hs : sigma ∈ Set.Icc (1 / 2) 2) :
    (∑ chi ∈ nonprincipalCharacters q, ∫ t in -y..y,
      ‖NonprincipalDensityAdvance.f chi X ((sigma : ℂ) + t * I)‖ ^ 2) ≤
      1.272 * (∑ chi ∈ nonprincipalCharacters q, ∫ t : ℝ,
        ‖cosineDetector chi X y ((sigma : ℂ) + t * I)‖ ^ 2) := by
  have his (chi : Character q) (hc : chi ∈ nonprincipalCharacters q) :
      (∫ t in -y..y, ‖NonprincipalDensityAdvance.f chi X ((sigma : ℂ) + t * I)‖ ^ 2) ≤
        1.272 * (∫ t : ℝ, ‖cosineDetector chi X y ((sigma : ℂ) + t * I)‖ ^ 2) := by
    have hn := (NonprincipalDensityAdvance.mem_nonprincipalCharacters chi).mp hc
    have hg := cosine_integrable_extended hn X hy hs
    have hsa : |sigma| ≤ 2 := abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
    have hgi : IntervalIntegrable (fun t : ℝ =>
        ‖cosineDetector chi X y ((sigma : ℂ) + t * I)‖ ^ 2) volume (-y) y :=
      ((cosine_vertical_continuous_extended hn X hy hsa).norm.pow 2).intervalIntegrable (-y) y
    have h := intervalIntegral.integral_mono_on (by linarith : -y ≤ y)
      (f_vertical_integrable hn X sigma y) (hgi.const_mul 1.272) (fun t ht => by
        apply f_window_le_cosine_sharp chi X hy
        · simpa using hsa
        · simpa using abs_le.mpr ht)
    rw [intervalIntegral.integral_const_mul] at h
    have hw : (∫ t in -y..y, ‖cosineDetector chi X y ((sigma : ℂ) + t * I)‖ ^ 2) ≤
        ∫ t : ℝ, ‖cosineDetector chi X y ((sigma : ℂ) + t * I)‖ ^ 2 := by
      rw [intervalIntegral.integral_of_le (by linarith : -y ≤ y)]
      exact setIntegral_le_integral hg (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    exact h.trans (mul_le_mul_of_nonneg_left hw (by norm_num))
  have h := sum_le_sum (s := nonprincipalCharacters q) his
  rwa [← mul_sum] at h

theorem Fmean_le_cosineMean_sharp (q : ℕ) [NeZero q] (X : ℝ) {y sigma : ℝ}
    (hy : 2 ≤ y) (hs : sigma ∈ Set.Icc (1 / 2) 2) :
    Fmean q X sigma y ≤ 1.272 * cosineMean q X sigma y := by
  have h := div_le_div_of_nonneg_right (family_window_le_cosine_sharp q X hy hs)
    (Nat.cast_nonneg q.totient)
  exact h.trans_eq (by unfold cosineMean; ring)

theorem source_family_window_interpolation (q : ℕ) [NeZero q] {y sigma : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (hs : sigma ∈ Icc (1 / 2) (1 + sourceDelta ((q : ℝ) * y))) :
    SourceRoute.Density.Restart.familyMean q ((q : ℝ) * y) sigma y ≤
      1.272 *
        ((∑ chi ∈ nonprincipalCharacters q, ∫ t : ℝ,
          ‖cosineDetector chi ((q : ℝ) * y) y ((1 / 2 : ℂ) + t * I)‖ ^ 2) ^
          (1 - (sigma - 1 / 2) / (1 / 2 + sourceDelta ((q : ℝ) * y))) *
        (∑ chi ∈ nonprincipalCharacters q, ∫ t : ℝ,
          ‖cosineDetector chi ((q : ℝ) * y) y
            (((1 + sourceDelta ((q : ℝ) * y) : ℝ) : ℂ) + t * I)‖ ^ 2) ^
          ((sigma - 1 / 2) / (1 / 2 + sourceDelta ((q : ℝ) * y)))) := by
  have hy' : 2 ≤ y := by
    linarith [(source_height_log_bounds (source_height_ge_log_six hy)).1]
  have hd := source_product_shift_bounds q hy
  have h := (family_window_le_cosine_sharp q ((q : ℝ) * y) hy'
    ⟨hs.1, by linarith [hs.2]⟩).trans
    (mul_le_mul_of_nonneg_left (source_family_interpolation q hy hs) (by norm_num))
  rw [SourceRoute.Density.Restart.familyMean]
  unfold SourceRoute.Density.Restart.familySquare
  rw [intervalIntegral.integral_finsetSum]
  · exact h
  · intro chi hc
    exact f_vertical_integrable
      ((NonprincipalDensityAdvance.mem_nonprincipalCharacters chi).mp hc) _ _ _

#print axioms source_cosine_equation_33
#print axioms Fmean_le_cosineMean_sharp
#print axioms source_family_window_interpolation

end LiuWang.Proof.Campaign20260915.Density
