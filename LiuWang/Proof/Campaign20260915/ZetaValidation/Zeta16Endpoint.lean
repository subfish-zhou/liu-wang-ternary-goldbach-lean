import LiuWang.Proof.Campaign20260915.ZetaValidation.Zeta16Rational
import LiuWang.Proof.Campaign20260915.ZetaValidation.GammaPhase16
import LiuWang.Proof.Campaign20260915.ZetaValidation.SecondOrderEvaluation
import LiuWang.Proof.Campaign20260915.ZetaValidation.InitialSegment

set_option autoImplicit false
noncomputable section

open Complex Finset Set

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def zeta16Correction : ℂ := -(1281 / 2050) - (4096 / 1025) * I

theorem zeta16Correction_eq :
    zeta16Correction = (64 : ℂ) / (criticalPoint 16 - 1) - 1 / 2 := by
  apply Complex.ext <;> norm_num [zeta16Correction, criticalPoint, Complex.div_re,
    Complex.div_im, Complex.normSq_apply]

theorem norm_zeta16Correction_le : ‖zeta16Correction‖ ≤ 5 := by
  have h : ‖zeta16Correction‖ ^ 2 ≤ (25 : ℝ) := by
    rw [Complex.sq_norm]
    norm_num [zeta16Correction, Complex.normSq_apply]
  nlinarith [norm_nonneg zeta16Correction]

theorem abelApprox_sixteen_formula :
    abelApprox (criticalPoint 16) 64 =
      (∑ j ∈ range 64, (j + 1 : ℂ) ^ (-criticalPoint 16)) +
        zeta16Correction * (64 : ℂ) ^ (-criticalPoint 16) := by
  have hp : (64 : ℂ) ^ (1 - criticalPoint 16) =
      64 * (64 : ℂ) ^ (-criticalPoint 16) := by
    rw [sub_eq_add_neg, cpow_add _ _ (by norm_num), cpow_one]
  rw [abelApprox]
  norm_num only [Nat.cast_ofNat]
  rw [hp, zeta16Correction_eq]
  unfold zetaPartialSum
  ring

theorem zeta16Center_formula :
    zeta16Center.toComplex =
      (∑ j ∈ range 64, (power16Center (j + 1)).toComplex) +
        zeta16Correction * (power16Center 64).toComplex := by
  apply Complex.ext
  all_goals
    simp only [zeta16Center, QComplex.toComplex, zeta16Correction,
      re_sum, im_sum, add_re, add_im, sub_re, sub_im, mul_re, mul_im,
      ratCast_re, ratCast_im, I_re, I_im, neg_re, neg_im, div_re, div_im]
    push_cast
    norm_num
    ring

theorem abelApprox_sixteen_rational_error :
    ‖abelApprox (criticalPoint 16) 64 - zeta16Center.toComplex‖ ≤ 69 / 1000 := by
  rw [abelApprox_sixteen_formula, zeta16Center_formula]
  have hs : ‖∑ j ∈ range 64,
      ((j + 1 : ℂ) ^ (-criticalPoint 16) - (power16Center (j + 1)).toComplex)‖ ≤
      (64 : ℝ) / 1000 := by
    calc
      _ ≤ ∑ j ∈ range 64,
          ‖(j + 1 : ℂ) ^ (-criticalPoint 16) - (power16Center (j + 1)).toComplex‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _j ∈ range 64, (1 / 1000 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := Finset.mem_range.mp hj
        simpa only [Nat.cast_add, Nat.cast_one] using
          power16Center_error (n := j + 1) (by omega) (by omega)
      _ = _ := by norm_num
  have hc :
      ‖zeta16Correction *
        ((64 : ℂ) ^ (-criticalPoint 16) - (power16Center 64).toComplex)‖ ≤ 5 / 1000 := by
    rw [norm_mul]
    exact (mul_le_mul norm_zeta16Correction_le
      (power16Center_error (n := 64) (by norm_num) (by norm_num))
      (norm_nonneg _) (by norm_num)).trans (by norm_num)
  rw [show
    ((∑ j ∈ range 64, (j + 1 : ℂ) ^ (-criticalPoint 16)) +
      zeta16Correction * (64 : ℂ) ^ (-criticalPoint 16)) -
      ((∑ j ∈ range 64, (power16Center (j + 1)).toComplex) +
      zeta16Correction * (power16Center 64).toComplex) =
    (∑ j ∈ range 64, ((j + 1 : ℂ) ^ (-criticalPoint 16) -
      (power16Center (j + 1)).toComplex)) +
      zeta16Correction * ((64 : ℂ) ^ (-criticalPoint 16) -
        (power16Center 64).toComplex) by rw [Finset.sum_sub_distrib]; ring]
  exact (norm_add_le _ _).trans ((add_le_add hs hc).trans (by norm_num))

theorem zeta_sixteen_abel_error :
    ‖riemannZeta (criticalPoint 16) - abelApprox (criticalPoint 16) 64‖ ≤ 1 / 20 := by
  have hs : ‖criticalPoint 16‖ ≤ 17 := by
    have h : ‖criticalPoint 16‖ ^ 2 = (1025 / 4 : ℝ) := by
      rw [Complex.sq_norm]
      norm_num [criticalPoint, Complex.normSq_apply]
    nlinarith [norm_nonneg (criticalPoint 16)]
  have hs1 : ‖criticalPoint 16 + 1‖ ≤ 17 := by
    have h : ‖criticalPoint 16 + 1‖ ^ 2 = (1033 / 4 : ℝ) := by
      rw [Complex.sq_norm]
      norm_num [criticalPoint, Complex.normSq_apply]
    nlinarith [norm_nonneg (criticalPoint 16 + 1)]
  have hr : (64 : ℝ) ^ (-(1 / 2 : ℝ) - 1) = 1 / 512 := by
    rw [sub_eq_add_neg, Real.rpow_add (by norm_num), Real.rpow_neg (by norm_num),
      ← Real.sqrt_eq_rpow, Real.rpow_neg (by norm_num), Real.rpow_one]
    norm_num
  have he := norm_zeta_sub_abelApprox_second_le (s := criticalPoint 16)
    (by norm_num [criticalPoint]) (criticalPoint_ne_one 16) (N := 64) (by norm_num)
  change ‖riemannZeta (criticalPoint 16) - abelApprox (criticalPoint 16) 64‖ ≤
    ‖criticalPoint 16‖ * ‖criticalPoint 16 + 1‖ *
      (64 : ℝ) ^ (-(1 / 2 : ℝ) - 1) / (8 * (1 / 2 + 1)) at he
  rw [hr] at he
  have hp := mul_le_mul hs hs1 (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 17)
  nlinarith

theorem zeta_sixteen_rational_error :
    ‖riemannZeta (criticalPoint 16) - zeta16Center.toComplex‖ ≤ 1 / 8 := by
  have ht := norm_sub_le_norm_sub_add_norm_sub (riemannZeta (criticalPoint 16))
    (abelApprox (criticalPoint 16) 64) zeta16Center.toComplex
  linarith [zeta_sixteen_abel_error, abelApprox_sixteen_rational_error]

theorem zeta_sixteen_positive_components :
    0 < (riemannZeta (criticalPoint 16)).re ∧ 0 < (riemannZeta (criticalPoint 16)).im := by
  have hr := (abs_re_le_norm (riemannZeta (criticalPoint 16) -
    zeta16Center.toComplex)).trans zeta_sixteen_rational_error
  have hi := (abs_im_le_norm (riemannZeta (criticalPoint 16) -
    zeta16Center.toComplex)).trans zeta_sixteen_rational_error
  simp only [sub_re, sub_im, QComplex.toComplex, add_re, add_im, mul_re, mul_im,
    ratCast_re, ratCast_im, I_re, I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add] at hr hi
  have h := zeta16Center_rational_lower
  have hrQ : ((1 / 4 : ℚ) : ℝ) ≤ (zeta16Center.1 : ℝ) := Rat.cast_le.mpr h.1
  have hiQ : ((1 / 4 : ℚ) : ℝ) ≤ (zeta16Center.2 : ℝ) := Rat.cast_le.mpr h.2
  norm_num at hrQ hiQ
  constructor <;> linarith [(abs_le.mp hr).1, (abs_le.mp hi).1]

theorem endpoint_sixteen_strict_sign : 0 < criticalCompletedZeta 16 := by
  have hz := zeta_sixteen_positive_components
  have hg := gamma16_phase_quadrant
  have h := congrArg Complex.re (normalizedCriticalZeta_ofReal 16)
  simp only [ofReal_re, mul_re] at h
  have hp : 0 < normalizedCriticalZeta 16 := by
    rw [h]
    exact sub_pos.mpr ((mul_neg_of_pos_of_neg hz.2 hg.2).trans
      (mul_pos hz.1 hg.1))
  have hn := criticalGammaNorm_pos 16
  change 0 < criticalCompletedZeta 16 / criticalGammaNorm 16 at hp
  exact (div_pos_iff.mp hp).elim (fun h => h.1) (fun h => (hn.not_gt h.2).elim)

theorem exists_nontrivial_zero_below_sixteen :
    ∃ t ∈ Ioo (1 / 4 : ℝ) 16, riemannZeta (criticalPoint t) = 0 := by
  apply exists_critical_zero_of_sign_change (by norm_num)
  exact mul_neg_of_neg_of_pos endpoint_quarter_strict_sign endpoint_sixteen_strict_sign

#print axioms zeta_sixteen_rational_error
#print axioms endpoint_sixteen_strict_sign
#print axioms exists_nontrivial_zero_below_sixteen

end LiuWang.Proof.Campaign20260915.ZetaValidation
