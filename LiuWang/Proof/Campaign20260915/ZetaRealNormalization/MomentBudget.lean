import LiuWang.Proof.Campaign20260915.ZetaRealNormalization.SourceSeven

set_option autoImplicit false
noncomputable section
open Complex

namespace LiuWang.Proof.Campaign20260915.ZetaRealNormalization
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

def momentDerivativeBudget (n : ℕ) (z : ℝ) : ℝ :=
  (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
    |iteratedDeriv j rsPhi z| * ‖gaussianJet (Real.pi * I / 2) (n - j)‖) /
      (2 * Real.pi) ^ n

theorem correctionMoment_derivative_bound (n : ℕ) {z : ℝ} (hz : |z| < 3 / 2) :
    ‖correctionMoment n z‖ ≤ momentDerivativeBudget n z := by
  have h := congrArg norm (correctionMoment_phi_derivatives n hz)
  simp only [norm_mul, norm_pow, norm_ofNat, norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, norm_I, mul_one] at h
  unfold momentDerivativeBudget
  apply (le_div_iff₀ (by positivity : 0 < (2 * Real.pi) ^ n)).mpr
  calc
    _ = ‖∑ j ∈ Finset.range (n + 1), (n.choose j : ℂ) *
        ((iteratedDeriv j rsPhi z : ℝ) : ℂ) * gaussianJet (Real.pi * I / 2) (n - j)‖ := by
      rw [mul_comm]
      exact h
    _ ≤ ∑ j ∈ Finset.range (n + 1), ‖(n.choose j : ℂ) *
        ((iteratedDeriv j rsPhi z : ℝ) : ℂ) * gaussianJet (Real.pi * I / 2) (n - j)‖ :=
      norm_sum_le _ _
    _ = _ := by
      simp only [norm_mul, norm_natCast, norm_real, Real.norm_eq_abs]

theorem momentDerivativeBudget_three (z : ℝ) :
    momentDerivativeBudget 3 z =
      (|iteratedDeriv 3 rsPhi z| + 3 * Real.pi * |iteratedDeriv 1 rsPhi z|) /
        (8 * Real.pi ^ 3) := by
  norm_num [momentDerivativeBudget, Finset.sum_range_succ, gaussianJet_zero,
    gaussianJet_one, gaussianJet_two, gaussianJet_three, norm_mul, norm_div,
    norm_pow, abs_of_pos Real.pi_pos]
  ring

theorem momentDerivativeBudget_four (z : ℝ) :
    momentDerivativeBudget 4 z =
      (|iteratedDeriv 4 rsPhi z| + 6 * Real.pi * |iteratedDeriv 2 rsPhi z| +
        3 * Real.pi ^ 2 * |rsPhi z|) / (16 * Real.pi ^ 4) := by
  norm_num [momentDerivativeBudget, Finset.sum_range_succ, gaussianJet_zero,
    gaussianJet_one, gaussianJet_two, gaussianJet_three, gaussianJet_four,
    norm_mul, norm_div, norm_pow, abs_of_pos Real.pi_pos, Nat.choose]
  ring

theorem momentDerivativeBudget_five (z : ℝ) :
    momentDerivativeBudget 5 z =
      (|iteratedDeriv 5 rsPhi z| + 10 * Real.pi * |iteratedDeriv 3 rsPhi z| +
        15 * Real.pi ^ 2 * |iteratedDeriv 1 rsPhi z|) / (32 * Real.pi ^ 5) := by
  norm_num [momentDerivativeBudget, Finset.sum_range_succ, gaussianJet_zero,
    gaussianJet_one, gaussianJet_two, gaussianJet_three, gaussianJet_four,
    gaussianJet_five, norm_mul, norm_div, norm_pow, abs_of_pos Real.pi_pos, Nat.choose]
  ring

theorem momentDerivativeBudget_six (z : ℝ) :
    momentDerivativeBudget 6 z =
      (|iteratedDeriv 6 rsPhi z| + 15 * Real.pi * |iteratedDeriv 4 rsPhi z| +
        45 * Real.pi ^ 2 * |iteratedDeriv 2 rsPhi z| + 15 * Real.pi ^ 3 * |rsPhi z|) /
        (64 * Real.pi ^ 6) := by
  norm_num [momentDerivativeBudget, Finset.sum_range_succ, gaussianJet_zero,
    gaussianJet_one, gaussianJet_two, gaussianJet_three, gaussianJet_four,
    gaussianJet_five, gaussianJet_six, norm_mul, norm_div, norm_pow, abs_of_pos Real.pi_pos,
    Nat.choose]
  ring

def sourceExtraDerivativeBudget (eta z : ℝ) : ℝ :=
  5 / (16 * eta ^ 3) * momentDerivativeBudget 3 z +
    35 / (128 * eta ^ 4) * momentDerivativeBudget 4 z +
    (9 * Real.pi / (10 * eta ^ 3) + 63 / (256 * eta ^ 5)) * momentDerivativeBudget 5 z +
    (223 * Real.pi / (240 * eta ^ 4) + 231 / (1024 * eta ^ 6)) * momentDerivativeBudget 6 z

theorem sourceExtraBudget_le_derivative {eta z : ℝ} (he : 0 < eta) (hz : |z| < 3 / 2) :
    sourceExtraBudget eta z ≤ sourceExtraDerivativeBudget eta z := by
  unfold sourceExtraBudget sourceExtraDerivativeBudget
  exact add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left (correctionMoment_derivative_bound 3 hz) (by positivity))
    (mul_le_mul_of_nonneg_left (correctionMoment_derivative_bound 4 hz) (by positivity)))
    (mul_le_mul_of_nonneg_left (correctionMoment_derivative_bound 5 hz) (by positivity)))
    (mul_le_mul_of_nonneg_left (correctionMoment_derivative_bound 6 hz) (by positivity))

theorem normalized_source_seven_derivative_budget {eta : ℝ} {m : ℕ}
    (h0 : 0 < eta - m) (h1 : eta - m < 1) :
    |sourceSevenNormalized eta m -
      sourceSignedAmplitude eta m * sourceRealCorrection eta (sourcePhiParameter eta m)| ≤
        eta ^ (-(1 / 2 : ℝ)) *
          (sourcePhaseBudget eta *
            (|sourceRealCorrection eta (sourcePhiParameter eta m)| +
              |sourceImaginaryCorrection eta (sourcePhiParameter eta m)|) +
            sourceExtraDerivativeBudget eta (sourcePhiParameter eta m)) := by
  have he : 0 < eta := by linarith [Nat.cast_nonneg (α := ℝ) m]
  exact (normalized_source_seven_budget h0 h1).trans
    (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (sourceExtraBudget_le_derivative he
        (sourcePhiParameter_domain h0.le h1.le))) (Real.rpow_nonneg he.le _))

#print axioms correctionMoment_derivative_bound
#print axioms normalized_source_seven_derivative_budget

end LiuWang.Proof.Campaign20260915.ZetaRealNormalization
