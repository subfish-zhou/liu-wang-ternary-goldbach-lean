import LiuWang.Proof.GlobalZeroDensity.WeightedMean

/-! A paid right-boundary logarithmic integral for the zero detector. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace LiuWang.Proof.GlobalZeroDensity

theorem abs_log_norm_H_le {y : ℝ} {s : ℂ} (hf : F y s ≤ 1 / 2) :
    |Real.log ‖H y s‖| ≤ 2 * F y s := by
  have hF : 0 ≤ F y s := sq_nonneg _
  have hlower : 1 - F y s ≤ ‖H y s‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (f y s ^ 2)
    rw [norm_one, norm_pow] at h
    exact h
  have hpos : 0 < ‖H y s‖ := by linarith
  have hinv : ‖H y s‖⁻¹ ≤ 1 + 2 * F y s := by
    rw [← one_div]
    apply (div_le_iff₀ hpos).mpr
    have hm := mul_le_mul_of_nonneg_right hlower (by linarith : 0 ≤ 1 + 2 * F y s)
    nlinarith
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  have hu := log_norm_H_le_F y s
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem F_two_le_quarter {y : ℝ} (hy : 5 ≤ y) {s : ℂ} (hs : s.re = 2) :
    F y s ≤ 1 / 4 := by
  have h := norm_f_two_le hs (by linarith : 1 < y)
  have hb : 2 / (y - 1) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by linarith : 0 < y - 1)).mpr
    linarith
  have hnorm := h.trans hb
  have hn := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  norm_num only at hn
  exact hn

theorem abs_log_integral_two_le {y : ℝ} (hy : 5 ≤ y) {u : ℝ} (hu : 0 ≤ u) :
    (∫ t in -u..u, |Real.log ‖H y ((2 : ℂ) + t * Complex.I)‖|) ≤
      16 * u / (y - 1) ^ 2 := by
  have hi := (intervalIntegrable_log_H_two (by linarith : 3 < y) u).abs
  have hF := (intervalIntegrable_F y u (σ := 2) (by norm_num)).const_mul 2
  have hpoint : ∀ t ∈ Set.Icc (-u) u,
      |Real.log ‖H y ((2 : ℂ) + t * Complex.I)‖| ≤
        2 * F y ((2 : ℂ) + t * Complex.I) := by
    intro t _
    exact abs_log_norm_H_le ((F_two_le_quarter hy (by simp)).trans (by norm_num))
  have h := intervalIntegral.integral_mono_on (by linarith : -u ≤ u) hi hF hpoint
  rw [intervalIntegral.integral_const_mul] at h
  have hm := M_two_le y (by linarith : 1 < y) hu
  simp only [M, Complex.ofReal_ofNat] at hm h
  calc
    _ ≤ 2 * (8 * u / (y - 1) ^ 2) :=
      h.trans (mul_le_mul_of_nonneg_left hm (by norm_num))
    _ = _ := by ring

end LiuWang.Proof.GlobalZeroDensity
