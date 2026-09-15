import LiuWang.Proof.Campaign20260915.ZetaValidation.NormalizedEvaluation

set_option autoImplicit false
noncomputable section

open Complex Set

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

theorem initial_segment_zeta_re {t : ℝ} (ht : |t| ≤ 1 / 4) :
    (riemannZeta (criticalPoint t)).re ≤ -(1 / 2 : ℝ) := by
  have ht2 : t ^ 2 ≤ (1 / 16 : ℝ) := by
    have h := abs_le.mp ht
    nlinarith [sq_le_sq' h.1 h.2]
  have hn : ‖criticalPoint t‖ ≤ (3 / 5 : ℝ) := by
    have hs : ‖criticalPoint t‖ ^ 2 = 1 / 4 + t ^ 2 := by
      simp [Complex.sq_norm, Complex.normSq_apply, criticalPoint]
      ring
    nlinarith [norm_nonneg (criticalPoint t)]
  have hd : 0 < (1 / 4 : ℝ) + t ^ 2 := by positivity
  have hb : (abelApprox (criticalPoint t) 1).re ≤ -(11 / 10 : ℝ) := by
    have he : (abelApprox (criticalPoint t) 1).re =
        1 / 2 - (1 / 2) / (1 / 4 + t ^ 2) := by
      norm_num [abelApprox, zetaPartialSum, Complex.div_re, Complex.normSq_apply,
        criticalPoint]
      ring
    rw [he]
    have hr : (8 / 5 : ℝ) ≤ (1 / 2) / (1 / 4 + t ^ 2) := by
      apply (le_div_iff₀ hd).2
      nlinarith
    linarith
  have he := norm_zeta_sub_abelApprox_le (s := criticalPoint t)
    (by norm_num [criticalPoint]) (criticalPoint_ne_one t) (N := 1) (by norm_num)
  have hre := re_le_norm (riemannZeta (criticalPoint t) - abelApprox (criticalPoint t) 1)
  norm_num [criticalPoint] at he
  change ‖riemannZeta (criticalPoint t) - abelApprox (criticalPoint t) 1‖ ≤
    ‖criticalPoint t‖ at he
  rw [sub_re] at hre
  linarith

theorem initial_segment_zeta_ne_zero {t : ℝ} (ht : |t| ≤ 1 / 4) :
    riemannZeta (criticalPoint t) ≠ 0 := by
  intro hz
  have h := initial_segment_zeta_re ht
  rw [hz, zero_re] at h
  norm_num at h

theorem initial_segment_strict_sign {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 4) :
    criticalCompletedZeta t < 0 := by
  by_contra hn
  have hn0 : 0 ≤ criticalCompletedZeta t := le_of_not_gt hn
  obtain ⟨u, hu, hz⟩ := intermediate_value_Icc ht0
    continuous_criticalCompletedZeta.continuousOn ⟨endpoint_zero_strict_sign.le, hn0⟩
  have huz := (criticalCompletedZeta_eq_zero_iff u).mp hz
  exact initial_segment_zeta_ne_zero (by rw [abs_of_nonneg hu.1]; exact hu.2.trans ht) huz

theorem endpoint_quarter_strict_sign : criticalCompletedZeta (1 / 4) < 0 :=
  initial_segment_strict_sign (by norm_num) le_rfl

theorem first_order_radius_requires_quadratic_cutoff {t : ℝ} {N : ℕ}
    (hN : 1 ≤ N)
    (h : ‖criticalPoint t‖ * (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 / 2) :
    4 * t ^ 2 ≤ (N : ℝ) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNp
  rw [Real.rpow_neg hNp.le, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv] at h
  have hn := (div_le_iff₀ hs).mp h
  have hi : |t| ≤ ‖criticalPoint t‖ := abs_im_le_norm (criticalPoint t)
  have he := Real.sq_sqrt hNp.le
  have hl : 2 * |t| ≤ Real.sqrt (N : ℝ) := by linarith
  have hsq := mul_self_le_mul_self (by positivity : 0 ≤ 2 * |t|) hl
  nlinarith [sq_abs t]

theorem original_height_first_order_cost {N : ℕ} (hN : 1 ≤ N)
    (h : ‖criticalPoint 1894437‖ * (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 / 2) :
    4 * 1894437 ^ 2 ≤ N := by
  exact_mod_cast first_order_radius_requires_quadratic_cutoff hN h

#print axioms endpoint_quarter_strict_sign
#print axioms original_height_first_order_cost

end LiuWang.Proof.Campaign20260915.ZetaValidation
