import LiuWang.Proof.Campaign20260915.LowZeroMoment.FourteenRational
import LiuWang.Proof.Campaign20260915.LowZeroMoment.GammaFourteen
import LiuWang.Proof.Campaign20260915.ZetaValidation.Zeta16Endpoint

set_option autoImplicit false
noncomputable section

open Complex Finset Set
open scoped ComplexConjugate

namespace LiuWang.Proof.Campaign20260915.LowZeroMoment
open LiuWang.Proof.Campaign20260915.ZetaValidation

def zeta14Correction : ℂ := -(1041 / 1570) - (3584 / 785) * I

theorem zeta14Correction_eq :
    zeta14Correction = (64 : ℂ) / (criticalPoint 14 - 1) - 1 / 2 := by
  apply Complex.ext <;> norm_num [zeta14Correction, criticalPoint, Complex.div_re,
    Complex.div_im, Complex.normSq_apply]

theorem norm_zeta14Correction_le : ‖zeta14Correction‖ ≤ 5 := by
  have h : ‖zeta14Correction‖ ^ 2 ≤ (25 : ℝ) := by
    rw [Complex.sq_norm]
    norm_num [zeta14Correction, Complex.normSq_apply]
  nlinarith [norm_nonneg zeta14Correction]

theorem abelApprox_fourteen_formula :
    abelApprox (criticalPoint 14) 64 =
      (∑ j ∈ range 64, (j + 1 : ℂ) ^ (-criticalPoint 14)) +
        zeta14Correction * (64 : ℂ) ^ (-criticalPoint 14) := by
  have hp : (64 : ℂ) ^ (1 - criticalPoint 14) =
      64 * (64 : ℂ) ^ (-criticalPoint 14) := by
    rw [sub_eq_add_neg, cpow_add _ _ (by norm_num), cpow_one]
  rw [abelApprox]
  norm_num only [Nat.cast_ofNat]
  rw [hp, zeta14Correction_eq]
  unfold zetaPartialSum
  ring

theorem zeta14Center_formula :
    zeta14Center.toComplex =
      (∑ j ∈ range 64, (power14Center (j + 1)).toComplex) +
        zeta14Correction * (power14Center 64).toComplex := by
  apply Complex.ext
  all_goals
    simp only [zeta14Center, zeta14TailIm, QComplex.toComplex, zeta14Correction,
      re_sum, im_sum, add_re, add_im, sub_re, sub_im, mul_re, mul_im,
      ratCast_re, ratCast_im, I_re, I_im, neg_re, neg_im, div_re, div_im]
    push_cast
    norm_num
    ring

theorem abelApprox_fourteen_rational_error :
    ‖abelApprox (criticalPoint 14) 64 - zeta14Center.toComplex‖ ≤ 207 / 10000 := by
  rw [abelApprox_fourteen_formula, zeta14Center_formula]
  have hs : ‖∑ j ∈ range 64,
      ((j + 1 : ℂ) ^ (-criticalPoint 14) - (power14Center (j + 1)).toComplex)‖ ≤
      (192 : ℝ) / 10000 := by
    calc
      _ ≤ ∑ j ∈ range 64,
          ‖(j + 1 : ℂ) ^ (-criticalPoint 14) - (power14Center (j + 1)).toComplex‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _j ∈ range 64, (3 / 10000 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := Finset.mem_range.mp hj
        simpa only [Nat.cast_add, Nat.cast_one] using
          power14Center_error (n := j + 1) (by omega) (by omega)
      _ = _ := by norm_num
  have hc :
      ‖zeta14Correction *
        ((64 : ℂ) ^ (-criticalPoint 14) - (power14Center 64).toComplex)‖ ≤ 15 / 10000 := by
    rw [norm_mul]
    exact (mul_le_mul norm_zeta14Correction_le
      (power14Center_error (n := 64) (by norm_num) (by norm_num))
      (norm_nonneg _) (by norm_num)).trans (by norm_num)
  rw [show
    ((∑ j ∈ range 64, (j + 1 : ℂ) ^ (-criticalPoint 14)) +
      zeta14Correction * (64 : ℂ) ^ (-criticalPoint 14)) -
      ((∑ j ∈ range 64, (power14Center (j + 1)).toComplex) +
      zeta14Correction * (power14Center 64).toComplex) =
    (∑ j ∈ range 64, ((j + 1 : ℂ) ^ (-criticalPoint 14) -
      (power14Center (j + 1)).toComplex)) +
      zeta14Correction * ((64 : ℂ) ^ (-criticalPoint 14) -
        (power14Center 64).toComplex) by rw [Finset.sum_sub_distrib]; ring]
  exact (norm_add_le _ _).trans ((add_le_add hs hc).trans (by norm_num))

theorem zeta_fourteen_abel_error :
    ‖riemannZeta (criticalPoint 14) - abelApprox (criticalPoint 14) 64‖ ≤ 3 / 80 := by
  have hs : ‖criticalPoint 14‖ ≤ 15 := by
    have h : ‖criticalPoint 14‖ ^ 2 = (785 / 4 : ℝ) := by
      rw [Complex.sq_norm]
      norm_num [criticalPoint, Complex.normSq_apply]
    nlinarith [norm_nonneg (criticalPoint 14)]
  have hs1 : ‖criticalPoint 14 + 1‖ ≤ 15 := by
    have h : ‖criticalPoint 14 + 1‖ ^ 2 = (793 / 4 : ℝ) := by
      rw [Complex.sq_norm]
      norm_num [criticalPoint, Complex.normSq_apply]
    nlinarith [norm_nonneg (criticalPoint 14 + 1)]
  have hr : (64 : ℝ) ^ (-(1 / 2 : ℝ) - 1) = 1 / 512 := by
    rw [sub_eq_add_neg, Real.rpow_add (by norm_num), Real.rpow_neg (by norm_num),
      ← Real.sqrt_eq_rpow, Real.rpow_neg (by norm_num), Real.rpow_one]
    norm_num
  have he := norm_zeta_sub_abelApprox_second_le (s := criticalPoint 14)
    (by norm_num [criticalPoint]) (criticalPoint_ne_one 14) (N := 64) (by norm_num)
  change ‖riemannZeta (criticalPoint 14) - abelApprox (criticalPoint 14) 64‖ ≤
    ‖criticalPoint 14‖ * ‖criticalPoint 14 + 1‖ *
      (64 : ℝ) ^ (-(1 / 2 : ℝ) - 1) / (8 * (1 / 2 + 1)) at he
  rw [hr] at he
  have hp := mul_le_mul hs hs1 (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 15)
  nlinarith

theorem zeta_fourteen_rational_error :
    ‖riemannZeta (criticalPoint 14) - zeta14Center.toComplex‖ ≤ 3 / 50 := by
  have ht := norm_sub_le_norm_sub_add_norm_sub (riemannZeta (criticalPoint 14))
    (abelApprox (criticalPoint 14) 64) zeta14Center.toComplex
  linarith [zeta_fourteen_abel_error, abelApprox_fourteen_rational_error]

theorem zeta_fourteen_im_neg : (riemannZeta (criticalPoint 14)).im < 0 := by
  have hi := (abs_im_le_norm (riemannZeta (criticalPoint 14) -
    zeta14Center.toComplex)).trans zeta_fourteen_rational_error
  simp only [sub_im, QComplex.toComplex, add_im, mul_im,
    ratCast_re, ratCast_im, I_re, I_im, mul_zero, mul_one, add_zero, zero_add] at hi
  have hQ : (zeta14Center.2 : ℝ) ≤ ((-(9 / 100) : ℚ) : ℝ) :=
    Rat.cast_le.mpr zeta14Center_im_upper
  norm_num at hQ
  linarith [(abs_le.mp hi).2]

theorem endpoint_fourteen_strict_sign : criticalCompletedZeta 14 < 0 := by
  have hid : (criticalGammaPhase 14) * conj (criticalGammaPhase 14) = 1 := by
    rw [mul_conj, ← Complex.sq_norm, norm_criticalGammaPhase]
    norm_num
  have h := congrArg (fun z : ℂ => z * conj (criticalGammaPhase 14))
    (normalizedCriticalZeta_ofReal 14)
  rw [mul_assoc, hid, mul_one] at h
  have hi := congrArg Complex.im h
  simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, conj_im] at hi
  have hn : normalizedCriticalZeta 14 < 0 := by
    have hp : normalizedCriticalZeta 14 * (-(criticalGammaPhase 14).im) < 0 := by
      rw [hi]
      exact zeta_fourteen_im_neg
    exact (mul_neg_iff.mp hp).resolve_left (by
      intro hh
      linarith [gamma14_phase_im_neg, hh.2]) |>.1
  exact (normalizedCriticalZeta_neg_iff 14).mp hn

theorem exists_nontrivial_zero_fourteen_sixteen :
    ∃ t ∈ Ioo (14 : ℝ) 16, riemannZeta (criticalPoint t) = 0 := by
  apply exists_critical_zero_of_sign_change (by norm_num)
  exact mul_neg_of_neg_of_pos endpoint_fourteen_strict_sign endpoint_sixteen_strict_sign

#print axioms zeta_fourteen_rational_error
#print axioms endpoint_fourteen_strict_sign
#print axioms exists_nontrivial_zero_fourteen_sixteen

end LiuWang.Proof.Campaign20260915.LowZeroMoment
