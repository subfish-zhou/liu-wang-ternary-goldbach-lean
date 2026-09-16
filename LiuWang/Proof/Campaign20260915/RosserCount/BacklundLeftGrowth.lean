import LiuWang.Proof.Campaign20260915.RosserCount.BacklundGammaRatio
import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCircle
import LiuWang.Proof.PrincipalPsi.Quantitative.XiBridge

set_option autoImplicit false
noncomputable section

open Complex
open scoped ComplexConjugate
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.PrincipalPsi
open LiuWang.Proof.PrincipalPsi.Quantitative
open LiuWang.Proof.Campaign20260915.ZetaWinding

namespace LiuWang.Proof.Campaign20260915.RosserCount

theorem backlund_left_functional_bound {σ t : ℝ}
    (hσ : -(1 / 2 : ℝ) ≤ σ) (hσ' : σ ≤ 0) (ht : 0 < t) :
    ‖riemannZeta (horizontalAt t σ)‖ ≤
      (t / (2 * Real.pi)) ^ (1 / 2 - σ) * Real.exp (129 / (8 * t ^ 2)) *
        ‖riemannZeta (1 - horizontalAt t σ)‖ := by
  let s := horizontalAt t σ
  let a := 1 + σ / 2
  let b := 1 + (1 - σ) / 2
  have hsre : s.re = σ := by simp [s, horizontalAt]
  have hsim : s.im = t := by simp [s, horizontalAt]
  have hs1 : s ≠ 1 := by
    intro he
    have h := congrArg Complex.im he
    rw [hsim, one_im] at h
    linarith
  have hs0 : s ≠ 0 := by
    intro he
    have h := congrArg Complex.im he
    rw [hsim, zero_im] at h
    linarith
  have hmirror : 1 - s ≠ 1 := by
    intro he
    apply hs0
    linear_combination -he
  have ha : 0 < a := by dsimp [a]; linarith
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hb : b ≤ 9 / 4 := by dsimp [b]; linarith
  have hdelta : b - a = 1 / 2 - σ := by dsimp [a, b]; ring
  have hga : s / 2 + 1 = horizontalAt (t / 2) a := by
    apply Complex.ext
    · simp [s, a, horizontalAt]
      ring
    · simp [s, a, horizontalAt]
  have hgb : (1 - s) / 2 + 1 = conj (horizontalAt (t / 2) b) := by
    apply Complex.ext
    · rw [conj_re]
      simp [s, b, horizontalAt]
      ring
    · rw [conj_im]
      simp [s, b, horizontalAt]
      ring
  have hA :
      ‖xiFactor s‖ = Real.pi ^ (-σ / 2) * ‖Gamma (horizontalAt (t / 2) a)‖ := by
    rw [xiFactor, norm_mul, hga, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    simp [hsre]
  have hB :
      ‖xiFactor (1 - s)‖ =
        Real.pi ^ (-(1 - σ) / 2) * ‖Gamma (horizontalAt (t / 2) b)‖ := by
    rw [xiFactor, norm_mul, hgb, Gamma_conj, norm_conj,
      Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    simp [hsre]
  have hγ :
      ‖Gamma (horizontalAt (t / 2) b)‖ ≤
        ‖Gamma (horizontalAt (t / 2) a)‖ * (t / 2) ^ (1 / 2 - σ) *
          Real.exp (129 / (8 * t ^ 2)) := by
    have h := backlund_gamma_ratio_le ha hab hb (half_pos ht)
    rw [hdelta] at h
    refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity))
    have he : 129 / (32 * (t / 2) ^ 2) = 129 / (8 * t ^ 2) := by
      congr 1
      ring
    rw [he]
    exact mul_le_of_le_one_right (by positivity) (by linarith)
  have hπ :
      Real.pi ^ (-(1 - σ) / 2) * (t / 2) ^ (1 / 2 - σ) =
        Real.pi ^ (-σ / 2) * (t / (2 * Real.pi)) ^ (1 / 2 - σ) := by
    have he : Real.pi ^ (-(1 - σ) / 2) =
        Real.pi ^ (-σ / 2) / Real.pi ^ (1 / 2 - σ) := by
      rw [← Real.rpow_sub Real.pi_pos]
      congr 1
      ring
    rw [he, show t / (2 * Real.pi) = (t / 2) / Real.pi by ring,
      Real.div_rpow (half_pos ht).le Real.pi_pos.le]
    ring
  have hfactor :
      ‖xiFactor (1 - s)‖ ≤
        ‖xiFactor s‖ * (t / (2 * Real.pi)) ^ (1 / 2 - σ) *
          Real.exp (129 / (8 * t ^ 2)) := by
    rw [hA, hB]
    calc
      _ ≤ Real.pi ^ (-(1 - σ) / 2) *
          (‖Gamma (horizontalAt (t / 2) a)‖ * (t / 2) ^ (1 / 2 - σ) *
            Real.exp (129 / (8 * t ^ 2))) :=
        mul_le_mul_of_nonneg_left hγ (by positivity)
      _ = ‖Gamma (horizontalAt (t / 2) a)‖ *
          (Real.pi ^ (-(1 - σ) / 2) * (t / 2) ^ (1 / 2 - σ)) *
            Real.exp (129 / (8 * t ^ 2)) := by ring
      _ = _ := by rw [hπ]; ring
  have hnorm : ‖s‖ ≤ ‖s - 1‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [Complex.sq_norm, normSq_apply, sub_re, sub_im, one_re, one_im, sub_zero,
      hsre]
    nlinarith
  have hApos : 0 < ‖xiFactor s‖ :=
    norm_pos_iff.mpr (xiFactor_ne_zero (by rw [hsre]; linarith))
  have hSpos : 0 < ‖s - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hs1)
  have hid :
      ‖xiFactor s‖ * ‖s - 1‖ * ‖riemannZeta s‖ =
        ‖xiFactor (1 - s)‖ * ‖s‖ * ‖riemannZeta (1 - s)‖ := by
    have h := congrArg norm (riemannXi_one_sub s)
    rw [xi_eq_factor_regularized (s := s) (by rw [hsre]; linarith),
      xi_eq_factor_regularized (s := 1 - s) (by simp [hsre]; linarith),
      regularizedPrincipal_eq hs1, regularizedPrincipal_eq hmirror,
      DirichletCharacter.LFunction_modOne_eq,
      show 1 - s - 1 = -s by ring] at h
    simp only [norm_mul, norm_neg] at h
    nlinarith only [h]
  have hcancel : ‖xiFactor s‖ * ‖riemannZeta s‖ ≤
      ‖xiFactor (1 - s)‖ * ‖riemannZeta (1 - s)‖ := by
    apply (mul_le_mul_iff_right₀ hSpos).mp
    calc
      _ = ‖xiFactor (1 - s)‖ * ‖s‖ * ‖riemannZeta (1 - s)‖ := by
        linear_combination hid
      _ ≤ ‖xiFactor (1 - s)‖ * ‖s - 1‖ * ‖riemannZeta (1 - s)‖ := by gcongr
      _ = _ := by ring
  apply (mul_le_mul_iff_right₀ hApos).mp
  calc
    _ ≤ ‖xiFactor (1 - s)‖ * ‖riemannZeta (1 - s)‖ := by nlinarith only [hcancel]
    _ ≤ (‖xiFactor s‖ * (t / (2 * Real.pi)) ^ (1 / 2 - σ) *
        Real.exp (129 / (8 * t ^ 2))) * ‖riemannZeta (1 - s)‖ :=
      mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)
    _ = _ := by ring

private theorem backlund_absorb_gamma_factor {t : ℝ} (ht : 1000 ≤ t) :
    Real.exp (129 / (8 * t ^ 2)) * (Real.log t - 0.048) < Real.log t := by
  have ht0 : 0 < t := by linarith
  let c := 129 / (8 * t ^ 2)
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hc1 : c < 1 := by
    dsimp [c]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hl : 0 ≤ Real.log t - 0.048 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3) (by linarith : (3 : ℝ) ≤ t)
    linarith [Real.log_three_gt_d9]
  have hcl : c * Real.log t < 0.048 := by
    have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos ht0) hc0
    have hu : c * t < 0.048 := by
      dsimp [c]
      have he : 129 / (8 * t ^ 2) * t = 129 / (8 * t) := by field_simp
      rw [he, div_lt_iff₀ (by positivity)]
      linarith
    nlinarith
  calc
    _ ≤ (1 / (1 - c)) * (Real.log t - 0.048) :=
      mul_le_mul_of_nonneg_right (Real.exp_bound_div_one_sub_of_interval hc0 hc1) hl
    _ < _ := by
      rw [one_div_mul_eq_div, div_lt_iff₀ (by linarith : 0 < 1 - c)]
      linarith

theorem backlund_zeta_left_growth_positive {σ t : ℝ}
    (hσ : -(1 / 2 : ℝ) ≤ σ) (hσ' : σ ≤ 0) (ht : 1000 ≤ t) :
    ‖riemannZeta (horizontalAt t σ)‖ <
      (t / (2 * Real.pi)) ^ (1 / 2 - σ) * Real.log t := by
  have ht0 : 0 < t := by linarith
  have hr := backlund_zeta_right_growth (s := 1 - horizontalAt t σ)
    (by simp [horizontalAt]; linarith) (by simp [horizontalAt]; linarith)
    (by simpa [horizontalAt, abs_of_pos ht0] using ht)
  simp only [sub_im, one_im, horizontalAt, add_im, ofReal_im, mul_im, ofReal_re,
    I_im, I_re, mul_one, mul_zero, add_zero, zero_add, zero_sub, abs_neg,
    abs_of_pos ht0] at hr
  have hpow : 0 < (t / (2 * Real.pi)) ^ (1 / 2 - σ) := by positivity
  calc
    _ ≤ _ := backlund_left_functional_bound hσ hσ' ht0
    _ < (t / (2 * Real.pi)) ^ (1 / 2 - σ) *
        (Real.exp (129 / (8 * t ^ 2)) * (Real.log t - 0.048)) := by
      have h := mul_lt_mul_of_pos_left hr
        (mul_pos hpow (Real.exp_pos (129 / (8 * t ^ 2))))
      simpa only [mul_assoc, horizontalAt] using! h
    _ < _ := mul_lt_mul_of_pos_left (backlund_absorb_gamma_factor ht) hpow

#print axioms backlund_left_functional_bound
#print axioms backlund_zeta_left_growth_positive

end LiuWang.Proof.Campaign20260915.RosserCount
