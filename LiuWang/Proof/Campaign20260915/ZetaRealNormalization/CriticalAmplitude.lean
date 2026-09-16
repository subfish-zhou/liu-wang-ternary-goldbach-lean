import LiuWang.Proof.Campaign20260915.ZetaRealNormalization.NonintegerC2Budgets

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Set

namespace LiuWang.Proof.Campaign20260915.ZetaRealNormalization
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaJnCentral

private theorem sinc_half_lower {x : ℝ} (hx : |x| ≤ Real.pi / 2) :
    1 / 2 ≤ Real.sinc x := by
  have hp (y : ℝ) (hy : 0 < y) (hu : y ≤ Real.pi / 2) :
      1 / 2 ≤ Real.sinc y := by
    rw [Real.sinc_of_ne_zero hy.ne', le_div_iff₀ hy]
    have h := Real.mul_le_sin hy.le hu
    have hc : (1 / 2 : ℝ) ≤ 2 / Real.pi := by
      rw [le_div_iff₀ Real.pi_pos]
      linarith [Real.pi_lt_four]
    nlinarith
  rcases lt_trichotomy x 0 with hn | rfl | hp'
  · rw [← Real.sinc_neg]
    exact hp (-x) (by linarith) (by rwa [abs_of_neg hn] at hx)
  · norm_num
  · exact hp x hp' (by rwa [abs_of_pos hp'] at hx)

private theorem criticalPhi_amplitude_nonneg {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    rsPhi z ≤ 4 := by
  have hsmall : |Real.pi / 2 * (z - 1 / 2)| ≤ Real.pi / 2 := by
    rw [abs_le]
    constructor <;> nlinarith [Real.pi_pos]
  have hlarge : |Real.pi / 2 * (z + 1 / 2)| ≤ 3 * Real.pi / 4 := by
    rw [abs_le]
    constructor <;> nlinarith [Real.pi_pos]
  have hs := sinc_half_lower hsmall
  have hl := rs_sinc_lower hlarge
  have hd := mul_le_mul hl hs (by norm_num : (0 : ℝ) ≤ 1 / 2) (by linarith)
  have hd' := mul_le_mul_of_nonneg_left hd Real.pi_pos.le
  have hp := rsPhi_denominator_pos
    (show |z| < 3 / 2 by rw [abs_of_nonneg hz0]; linarith)
  unfold rsPhi
  rw [div_le_iff₀ hp]
  nlinarith [Real.sinc_le_one (Real.pi / 2 * (z ^ 2 - 1 / 4)), Real.pi_gt_three]

theorem criticalPhi_amplitude {z : ℝ} (hz : |z| ≤ 1) :
    |rsPhi z| ≤ 4 := by
  rw [abs_of_pos (rsPhi_uniform_bound hz).1]
  by_cases hz0 : 0 ≤ z
  · exact criticalPhi_amplitude_nonneg hz0 ((le_abs_self z).trans hz)
  · rw [← rsPhi_even]
    exact criticalPhi_amplitude_nonneg (by linarith) (by rwa [abs_of_neg (by linarith)] at hz)

theorem critical_first_gaussian_scalar :
    (3 / 4) * exactGaussianBudget (Real.pi / 3) 0 +
      (4 * Real.pi / 3) * exactGaussianBudget (Real.pi / 3) 2 ≤ 305 / 48 := by
  have hb : 0 < Real.pi / 3 := by positivity
  have hs2 : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hs3 : Real.sqrt 3 ≤ 7 / 4 := by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hratio : Real.sqrt 3 / Real.sqrt 2 ≤ 7 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hid :
      (3 / 4) * exactGaussianBudget (Real.pi / 3) 0 +
        (4 * Real.pi / 3) * exactGaussianBudget (Real.pi / 3) 2 =
          (57 + 11 * (Real.sqrt 3 / Real.sqrt 2)) / (4 * Real.pi) := by
    unfold exactGaussianBudget
    rw [gaussianAbsoluteMoment_one,
      show gaussianAbsoluteMoment (Real.pi / 3) 3 =
        2 / (2 * (Real.pi / 3)) * gaussianAbsoluteMoment (Real.pi / 3) 1 by
          simpa only [Nat.cast_one, Nat.reduceAdd, show (1 : ℝ) + 1 = 2 by norm_num] using
            gaussianAbsoluteMoment_step hb 1,
      gaussianAbsoluteMoment_one,
      show gaussianAbsoluteMoment (Real.pi / 3) 2 =
        1 / (2 * (Real.pi / 3)) * gaussianAbsoluteMoment (Real.pi / 3) 0 by
          simpa using gaussianAbsoluteMoment_step hb 0,
      gaussianAbsoluteMoment_zero hb, show Real.pi / (Real.pi / 3) = 3 by field_simp]
    field_simp
    ring
  rw [hid, div_le_iff₀ (by positivity)]
  nlinarith [Real.pi_gt_three]

theorem critical_first_Jn_all_positive {eta : ℝ} {m : ℕ}
    (he : 0 < eta) (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) :
    ‖∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta m 1 y‖ ≤
      10 / eta := by
  let W := fun y : ℝ => (3 / 4) * exactGaussianWeight (Real.pi / 3) 0 y +
    (4 * Real.pi / 3) * exactGaussianWeight (Real.pi / 3) 2 y
  have hb : 0 < Real.pi / 3 := by positivity
  have hi : Integrable W :=
    ((exactGaussianWeight_integrable hb 0).const_mul (3 / 4)).add
      ((exactGaussianWeight_integrable hb 2).const_mul (4 * Real.pi / 3))
  have hW (y : ℝ) : 0 ≤ W y := by
    dsimp [W, exactGaussianWeight]
    positivity
  have hpoint (y : ℝ) (hy : y ∈ Icc (-eta / 2) (eta / 2)) :
      ‖rsJnIntegrand (1 / 2) eta m 1 y‖ ≤ Real.exp (3 / 8) / eta * W y := by
    have h := jn_one_pointwise (1 / 2) he (abs_le.mpr (by
      simpa only [mem_Icc, neg_div] using hy)) hm0 hm1
    norm_num only [show |(1 / 2 : ℝ) - 1| = 1 / 2 by norm_num,
      show (3 / 4 : ℝ) * (1 / 2) = 3 / 8 by norm_num] at h
    apply h.trans_eq
    dsimp [W, firstOrderPolynomial, exactGaussianWeight]
    norm_num only [show |(1 / 2 : ℝ) - 1| = 1 / 2 by norm_num, pow_zero, sq_abs]
    ring
  have hI : ∫ y : ℝ, W y =
      (3 / 4) * exactGaussianBudget (Real.pi / 3) 0 +
        (4 * Real.pi / 3) * exactGaussianBudget (Real.pi / 3) 2 := by
    rw [show W = _ from rfl,
      integral_add ((exactGaussianWeight_integrable hb 0).const_mul _)
        ((exactGaussianWeight_integrable hb 2).const_mul _),
      integral_const_mul, integral_const_mul, exactGaussianWeight_integral hb,
      exactGaussianWeight_integral hb]
  have hE : Real.exp (3 / 8 : ℝ) ≤ 97 / 64 := by
    have h := Real.abs_exp_sub_one_sub_id_le (x := 3 / 8) (by norm_num)
    have h' := (abs_le.mp h).2
    linarith
  rw [intervalIntegral.integral_symm, norm_neg]
  calc
    _ ≤ ∫ y : ℝ in (-eta / 2)..(eta / 2), Real.exp (3 / 8) / eta * W y :=
      intervalIntegral.norm_integral_le_of_norm_le (by linarith)
        (Filter.Eventually.of_forall (fun y hy => hpoint y ⟨hy.1.le, hy.2⟩))
        (hi.const_mul _).intervalIntegrable
    _ ≤ ∫ y : ℝ, Real.exp (3 / 8) / eta * W y := by
      rw [intervalIntegral.integral_of_le (by linarith)]
      exact setIntegral_le_integral (hi.const_mul _)
        (Filter.Eventually.of_forall (fun y => mul_nonneg (by positivity) (hW y)))
    _ = Real.exp (3 / 8) / eta *
        ((3 / 4) * exactGaussianBudget (Real.pi / 3) 0 +
          (4 * Real.pi / 3) * exactGaussianBudget (Real.pi / 3) 2) := by
      rw [integral_const_mul, hI]
    _ ≤ (97 / 64) / eta * (305 / 48) :=
      mul_le_mul (div_le_div_of_nonneg_right hE he.le) critical_first_gaussian_scalar
        (by rw [← hI]; exact integral_nonneg hW) (by positivity)
    _ ≤ _ := by
      field_simp
      norm_num

#print axioms criticalPhi_amplitude
#print axioms critical_first_Jn_all_positive

end LiuWang.Proof.Campaign20260915.ZetaRealNormalization
