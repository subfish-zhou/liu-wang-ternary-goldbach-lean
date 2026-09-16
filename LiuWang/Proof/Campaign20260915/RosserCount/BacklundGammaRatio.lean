import LiuWang.Proof.Campaign20260915.ZetaWinding.LehmanGammaBudget

set_option autoImplicit false
noncomputable section

open Complex
open LiuWang.Proof.Campaign20260915.ZetaWinding

namespace LiuWang.Proof.Campaign20260915.RosserCount

private theorem gamma_right_log_derivative (y : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun u => Real.log ‖Gamma (horizontalAt y u)‖)
      (digamma (horizontalAt y x)).re x := by
  have hz : 0 < (horizontalAt y x).re := by simpa [horizontalAt] using hx
  have hd : HasDerivAt (fun u => horizontalAt y u) (1 : ℂ) x := by
    simpa [horizontalAt] using ofRealCLM.hasDerivAt.add_const ((y : ℂ) * I)
  have hg := (differentiableAt_Gamma _ (fun n => by
    intro he
    have h := hz
    rw [he] at h
    simp at h
    linarith [Nat.cast_nonneg (α := ℝ) n])).hasDerivAt.scomp x hd
  have h := log_norm_hasDerivAt hg (Gamma_ne_zero_of_re_pos hz)
  simpa [digamma_def, logDeriv_apply, smul_eq_mul] using h

theorem backlund_log_gamma_ratio_error {a b y : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 9 / 4) (hy : 0 < y) :
    |Real.log ‖Gamma (horizontalAt y b)‖ - Real.log ‖Gamma (horizontalAt y a)‖ -
        (b - a) * Real.log y| ≤ 129 / (32 * y ^ 2) * (b - a) := by
  let f : ℝ → ℝ := fun u => Real.log ‖Gamma (horizontalAt y u)‖ - u * Real.log y
  let g : ℝ → ℝ := fun u => (digamma (horizontalAt y u)).re - Real.log y
  have hd (u : ℝ) (hu : u ∈ Set.Icc a b) : HasDerivAt f (g u) u := by
    simpa [f, g] using! (gamma_right_log_derivative y (ha.trans_le hu.1)).sub
      ((hasDerivAt_id u).mul_const (Real.log y))
  have hg (u : ℝ) (hu : u ∈ Set.Ico a b) : ‖g u‖ ≤ 129 / (32 * y ^ 2) := by
    simpa [g, horizontalAt, Real.norm_eq_abs] using
      (digamma_re_log_im_error (z := horizontalAt y u)
        (by simpa [horizontalAt] using ha.trans_le hu.1)
        (by simpa [horizontalAt] using hu.2.le.trans hb)
        (by simpa [horizontalAt] using hy))
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun u hu => (hd u hu).hasDerivWithinAt) hg b ⟨hab, le_rfl⟩
  have he : f b - f a =
      Real.log ‖Gamma (horizontalAt y b)‖ - Real.log ‖Gamma (horizontalAt y a)‖ -
        (b - a) * Real.log y := by
    dsimp [f]
    ring
  rwa [Real.norm_eq_abs, he] at h

theorem backlund_gamma_ratio_le {a b y : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 9 / 4) (hy : 0 < y) :
    ‖Gamma (horizontalAt y b)‖ ≤
      ‖Gamma (horizontalAt y a)‖ * y ^ (b - a) *
        Real.exp (129 / (32 * y ^ 2) * (b - a)) := by
  have hga : 0 < ‖Gamma (horizontalAt y a)‖ :=
    norm_pos_iff.mpr (Gamma_ne_zero_of_re_pos (by simpa [horizontalAt] using ha))
  have hgb : 0 < ‖Gamma (horizontalAt y b)‖ :=
    norm_pos_iff.mpr (Gamma_ne_zero_of_re_pos
      (by simpa [horizontalAt] using ha.trans_le hab))
  have h := (abs_le.mp (backlund_log_gamma_ratio_error ha hab hb hy)).2
  calc
    _ = Real.exp (Real.log ‖Gamma (horizontalAt y b)‖) := (Real.exp_log hgb).symm
    _ ≤ Real.exp (Real.log ‖Gamma (horizontalAt y a)‖ +
        (b - a) * Real.log y + 129 / (32 * y ^ 2) * (b - a)) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = _ := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log hga, Real.rpow_def_of_pos hy]
      rw [mul_comm (b - a) (Real.log y)]

#print axioms backlund_log_gamma_ratio_error
#print axioms backlund_gamma_ratio_le

end LiuWang.Proof.Campaign20260915.RosserCount
