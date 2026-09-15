import LiuWang.Proof.Campaign20260915.ZetaValidation.HighOrderUniform

set_option autoImplicit false
noncomputable section

open Complex

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

theorem original_height_order64_remainder {s : ℂ}
    (hslo : 1 / 2 ≤ s.re) (hshi : s.re ≤ 2) (ht : |s.im| ≤ 1894438) (hs1 : s ≠ 1) :
    ‖riemannZeta s - eulerMaclaurinApprox s 4194304 63‖ ≤ 1 / 10000000000000000 := by
  have hn : ‖s‖ ≤ 1894440 := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_nonneg (by linarith : 0 ≤ s.re)] at h
    linarith
  have hscale : ‖s‖ + (63 : ℝ) ≤ (4194304 : ℕ) / (2 : ℝ) := by
    norm_num
    linarith
  have he := eulerMaclaurin_geometric_error 63 (by linarith : 1 / 10 < s.re) hs1
    (N := 4194304) (by norm_num) hscale
  have hp : (4194304 : ℝ) ^ (1 - s.re) ≤ 2048 := by
    calc
      _ ≤ (4194304 : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = _ := by rw [← Real.sqrt_eq_rpow]; norm_num
  have hd : (2 : ℝ) ^ (63 + 2) * (s.re + 63) ≥ 2 ^ 65 * (1 / 2 + 63) := by
    gcongr
  have hdpos : 0 < (2 : ℝ) ^ (63 + 2) * (s.re + 63) := by positivity
  norm_num only [Nat.cast_ofNat] at he
  norm_num at hd hdpos
  apply he.trans
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 36893488147419103232) hdpos)).mpr
  linarith

theorem original_height_critical_order64_remainder {t : ℝ} (ht : |t| < 1894438) :
    ‖riemannZeta (criticalPoint t) -
      eulerMaclaurinApprox (criticalPoint t) 4194304 63‖ ≤ 1 / 10000000000000000 :=
  original_height_order64_remainder (by norm_num [criticalPoint]) (by norm_num [criticalPoint])
    (by simpa only [criticalPoint] using ht.le) (criticalPoint_ne_one t)

theorem original_height_normalized_order64_remainder {t : ℝ} (ht : |t| < 1894438) :
    |normalizedCriticalZeta t -
      (eulerMaclaurinApprox (criticalPoint t) 4194304 63 * criticalGammaPhase t).re| ≤
        1 / 10000000000000000 := by
  have he : normalizedCriticalZeta t -
      (eulerMaclaurinApprox (criticalPoint t) 4194304 63 * criticalGammaPhase t).re =
      ((riemannZeta (criticalPoint t) -
        eulerMaclaurinApprox (criticalPoint t) 4194304 63) * criticalGammaPhase t).re := by
    rw [sub_mul, sub_re, ← normalizedCriticalZeta_ofReal, ofReal_re]
  rw [he]
  have h := abs_re_le_norm
    ((riemannZeta (criticalPoint t) - eulerMaclaurinApprox (criticalPoint t) 4194304 63) *
      criticalGammaPhase t)
  rw [norm_mul, norm_criticalGammaPhase, mul_one] at h
  exact h.trans (original_height_critical_order64_remainder ht)

#print axioms original_height_order64_remainder
#print axioms original_height_normalized_order64_remainder

end LiuWang.Proof.Campaign20260915.ZetaValidation
