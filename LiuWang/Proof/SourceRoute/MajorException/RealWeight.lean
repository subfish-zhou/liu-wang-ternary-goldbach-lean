import LiuWang.Proof.OscillatoryBounds.Consumer
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.SourceRoute.MajorException

theorem log_thousand_bounds :
    (6 : ℝ) ≤ Real.log 1000 ∧ Real.log 1000 ≤ 6.9081 := by
  constructor
  · have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2^9)
      (by norm_num : (2 : ℝ)^9 ≤ 1000)
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith [Real.log_two_gt_d9]
  · have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 125/128)
    have he : Real.log (1000 : ℝ) = 10 * Real.log 2 + Real.log (125/128) := by
      rw [show (1000 : ℝ) = 2^10 * (125/128) by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
      norm_num
    rw [he]
    linarith [Real.log_two_lt_d9]

theorem source_real_mass_factor {beta : ℝ}
    (hb : 0.9957 ≤ beta) (hb1 : beta ≤ 1) :
    (1 - (0.001 : ℝ)^beta) / beta ≤ 1.0033 := by
  have hl : Real.log (0.001 : ℝ) = -Real.log 1000 := by
    rw [show (0.001 : ℝ) = (1000 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have he : (0.001 : ℝ)^beta =
      0.001 * Real.exp (Real.log 1000 * (1 - beta)) := by
    rw [Real.rpow_def_of_pos (by norm_num), hl,
      show -Real.log 1000 * beta =
        Real.log (0.001 : ℝ) + Real.log 1000 * (1 - beta) by rw [hl]; ring,
      Real.exp_add, Real.exp_log (by norm_num)]
  have ht := Real.add_one_le_exp (Real.log 1000 * (1 - beta))
  have hm := mul_le_mul_of_nonneg_right log_thousand_bounds.1
    (sub_nonneg.mpr hb1)
  apply (div_le_iff₀ (by linarith : 0 < beta)).mpr
  rw [he]
  nlinarith

theorem source_real_endpoint_factor {beta : ℝ}
    (hb : 0.9957 ≤ beta) (hb1 : beta ≤ 1) :
    (0.001 : ℝ)^(beta - 1) ≤ 1.0302 := by
  have hl : Real.log (0.001 : ℝ) = -Real.log 1000 := by
    rw [show (0.001 : ℝ) = (1000 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hm := mul_le_mul log_thousand_bounds.2
    (show 1 - beta ≤ 0.0043 by linarith)
    (sub_nonneg.mpr hb1) (by norm_num : (0 : ℝ) ≤ 6.9081)
  have hlog := Real.le_log_one_add_of_nonneg (x := (0.0302 : ℝ)) (by norm_num)
  norm_num at hlog
  rw [Real.rpow_def_of_pos (by norm_num)]
  apply (Real.exp_le_exp.mpr (show Real.log (0.001 : ℝ) * (beta - 1) ≤
    Real.log 1.0302 by rw [hl]; nlinarith)).trans_eq
  exact Real.exp_log (by norm_num)

theorem Jrho_source_mass {N : ℕ} (hN : 0 < N) {beta : ℝ}
    (hb : 0.9957 ≤ beta) (hb1 : beta ≤ 1) (eta : ℝ) :
    ‖Jrho N (beta : ℂ) eta‖ ≤ 1.0033 * (N : ℝ)^beta := by
  exact (OscillatoryBounds.Jrho_weight hN
    (show 0 < (beta : ℂ).re by simp; linarith) eta).trans
      (mul_le_mul_of_nonneg_right (source_real_mass_factor hb hb1)
        (Real.rpow_nonneg (Nat.cast_nonneg N) beta))

theorem Jrho_source_reciprocal {N : ℕ} (hN : 0 < N) {beta : ℝ}
    (hb : 0.9957 ≤ beta) (hb1 : beta ≤ 1) {eta : ℝ} (he : eta ≠ 0) :
    ‖Jrho N (beta : ℂ) eta‖ ≤
      1.0302 * (N : ℝ)^(beta - 1) / (Real.pi * |eta|) := by
  have h := OscillatoryBounds.Jrho_real_reciprocal hN
    (show (beta : ℂ).re ≤ 1 from hb1) (by simp : (beta : ℂ).im = 0) he
  simp only [Complex.ofReal_re] at h
  rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg N)] at h
  exact h.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (source_real_endpoint_factor hb hb1)
      (Real.rpow_nonneg (Nat.cast_nonneg N) (beta - 1))) (by positivity))

end LiuWang.Proof.SourceRoute.MajorException
