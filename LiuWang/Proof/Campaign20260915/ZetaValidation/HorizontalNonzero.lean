import LiuWang.Proof.Campaign20260915.ZetaValidation.HorizontalWeights
import LiuWang.Proof.Campaign20260915.ZetaValidation.SecondOrderEvaluation
import LiuWang.Proof.DirichletZeroCount.Remainder.RightHalfPlane
import LiuWang.Proof.DirichletZeroCount.Argument.XiCount

set_option autoImplicit false
noncomputable section
open Complex
open scoped ComplexConjugate

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

theorem horizontal_abel_correction_nonneg {sigma : ℝ}
    (hshi : sigma ≤ 2) :
    0 ≤ (abelApprox (horizontalPoint sigma) 64 -
      zetaPartialSum (horizontalPoint sigma) 64).re := by
  let s := horizontalPoint sigma
  let c : ℂ := 64 / (s - 1) - 1 / 2
  have hd : 0 < (sigma - 1) ^ 2 + 256 := by positivity
  have hc_re : c.re ≤ 0 := by
    change (64 / (horizontalPoint sigma - 1) - 1 / 2 : ℂ).re ≤ 0
    norm_num [horizontalPoint, div_re, normSq_apply]
    rw [← sq]
    apply (div_le_iff₀ hd).mpr
    nlinarith [sq_nonneg (sigma - 1)]
  have hc_im : c.im ≤ 0 := by
    change (64 / (horizontalPoint sigma - 1) - 1 / 2 : ℂ).im ≤ 0
    norm_num [horizontalPoint, div_im, normSq_apply]
    rw [← sq]
    positivity
  have hz := horizontal_tail_phase
  have hc : 0 ≤ (c * (64 : ℂ) ^ (-criticalPoint 16)).re := by
    rw [mul_re]
    exact sub_nonneg.mpr ((mul_nonpos_of_nonpos_of_nonneg hc_im hz.2.le).trans
      (mul_nonneg_of_nonpos_of_nonpos hc_re hz.1.le))
  have he : abelApprox s 64 - zetaPartialSum s 64 =
      (((64 : ℝ) ^ (1 / 2 - sigma) : ℝ) : ℂ) *
        (c * (64 : ℂ) ^ (-criticalPoint 16)) := by
    have hp : (64 : ℂ) ^ (1 - s) = 64 * (64 : ℂ) ^ (-s) := by
      rw [show 1 - s = (1 : ℂ) + -s by ring, cpow_add _ _ (by norm_num), cpow_one]
    rw [abelApprox]
    norm_num only [Nat.cast_ofNat]
    rw [hp]
    have hw := horizontal_cpow sigma (n := 64) (by norm_num)
    change (64 : ℂ) ^ (-s) = _ at hw
    rw [hw]
    dsimp [c]
    ring
  change 0 ≤ (abelApprox s 64 - zetaPartialSum s 64).re
  rw [he, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) hc

theorem horizontal_second_order_error {sigma : ℝ}
    (hslo : 1 / 2 ≤ sigma) (hshi : sigma ≤ 2) :
    ‖riemannZeta (horizontalPoint sigma) - abelApprox (horizontalPoint sigma) 64‖ ≤ 1 / 16 := by
  have hs1 : horizontalPoint sigma ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    norm_num [horizontalPoint] at this
  have hn : ‖horizontalPoint sigma‖ ≤ 18 := by
    have h := norm_le_abs_re_add_abs_im (horizontalPoint sigma)
    norm_num [horizontalPoint, abs_of_nonneg (by linarith : 0 ≤ sigma)] at h
    change ‖(⟨sigma, 16⟩ : ℂ)‖ ≤ 18
    linarith
  have hn1 : ‖horizontalPoint sigma + 1‖ ≤ 19 := by
    have h := norm_add_le (horizontalPoint sigma) 1
    norm_num at h
    linarith
  have hp : (64 : ℝ) ^ (-sigma - 1) ≤ 1 / 512 := by
    calc
      _ ≤ (64 : ℝ) ^ (-(1 / 2 : ℝ) - 1) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = _ := by
        rw [Real.rpow_sub (by norm_num), Real.rpow_neg (by norm_num),
          ← Real.sqrt_eq_rpow]
        norm_num
  have he := norm_zeta_sub_abelApprox_second_le (s := horizontalPoint sigma)
    (by simpa [horizontalPoint] using (show 1 / 10 < sigma by linarith)) hs1
    (N := 64) (by norm_num)
  change _ ≤ ‖horizontalPoint sigma‖ * ‖horizontalPoint sigma + 1‖ *
    (64 : ℝ) ^ (-sigma - 1) / (8 * (sigma + 1)) at he
  have hmul := mul_le_mul hn hn1 (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 18)
  have hnum := mul_le_mul hmul hp (Real.rpow_nonneg (by norm_num) _)
    (by norm_num : (0 : ℝ) ≤ 18 * 19)
  apply he.trans
  apply (div_le_iff₀ (by positivity : 0 < 8 * (sigma + 1))).mpr
  nlinarith

theorem horizontal_zeta_re_pos {sigma : ℝ} (hs : 1 / 2 ≤ sigma) :
    0 < (riemannZeta (horizontalPoint sigma)).re := by
  by_cases hshi : sigma ≤ 2
  · have hp := horizontal_partial_sum_lower hs
    have hc := horizontal_abel_correction_nonneg hshi
    have he := horizontal_second_order_error hs hshi
    have hre := neg_norm_le_re
      (riemannZeta (horizontalPoint sigma) - abelApprox (horizontalPoint sigma) 64)
    simp only [sub_re] at hc hre
    linarith
  · have h := LiuWang.Proof.DirichletZeroCount.Remainder.LFunction_re_pos
      (1 : LiuWang.Proof.Interfaces.Character 1)
      (s := horizontalPoint sigma) (by simpa [horizontalPoint] using (not_le.mp hshi).le)
    simpa only [DirichletCharacter.LFunction_modOne_eq] using h

theorem zeta_ne_zero_horizontal_right {s : ℂ} (hs : 1 / 2 ≤ s.re)
    (ht : |s.im| = 16) : riemannZeta s ≠ 0 := by
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 16)).mp ht with ht | ht
  · have he : s = horizontalPoint s.re := by apply Complex.ext <;> simp [horizontalPoint, ht]
    rw [he]
    exact ne_zero_of_re_pos (horizontal_zeta_re_pos hs)
  · have he : conj s = horizontalPoint s.re := by apply Complex.ext <;> simp [horizontalPoint, ht]
    have h := ne_zero_of_re_pos (horizontal_zeta_re_pos hs)
    rw [← he, riemannZeta_conj] at h
    exact fun hz => h (by simp [hz])

theorem zeta_ne_zero_height_sixteen {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (ht : |s.im| = 16) : riemannZeta s ≠ 0 := by
  by_cases hs : 1 / 2 ≤ s.re
  · exact zeta_ne_zero_horizontal_right hs ht
  · intro hz
    have hs0 : s ≠ 0 := ne_zero_of_re_pos h0
    have hs1 : s ≠ 1 := by intro he; simp [he] at h1
    have hx := (LiuWang.Proof.PrincipalPsi.Quantitative.xi_zero_iff_zeta_zero
      (by linarith : -2 < s.re) hs1).mpr hz
    have hy : riemannXi (1 - s) = 0 := by rwa [riemannXi_one_sub]
    have hy1 : 1 - s ≠ 1 := by intro he; apply hs0; linear_combination -he
    have hyz := (LiuWang.Proof.PrincipalPsi.Quantitative.xi_zero_iff_zeta_zero
      (s := 1 - s) (by simp only [sub_re, one_re]; linarith) hy1).mp hy
    exact zeta_ne_zero_horizontal_right
      (s := 1 - s) (by simp only [sub_re, one_re]; linarith)
      (by simpa using ht) hyz

#print axioms horizontal_zeta_re_pos
#print axioms zeta_ne_zero_height_sixteen

end LiuWang.Proof.Campaign20260915.ZetaValidation
