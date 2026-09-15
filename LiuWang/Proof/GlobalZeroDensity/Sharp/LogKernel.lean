import LiuWang.Proof.GlobalZeroDensity.Sharp.MollifierMean

/-! An explicit comparison of the logarithmic off-diagonal kernel with harmonic gaps. -/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.GlobalZeroDensity.Sharp

theorem logarithmic_kernel_le {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    1 / (Real.sqrt x * Real.sqrt y * (Real.log y - Real.log x)) ≤
      1 / (y - x) + 1 / (2 * Real.sqrt x * Real.sqrt y) := by
  have hy : 0 < y := hx.trans hxy
  have ha := Real.sqrt_pos.mpr hx
  have hb := Real.sqrt_pos.mpr hy
  have hab := Real.sqrt_lt_sqrt hx.le hxy
  have ha2 := Real.sq_sqrt hx.le
  have hb2 := Real.sq_sqrt hy.le
  have hla := Real.log_pow (Real.sqrt x) 2
  have hlb := Real.log_pow (Real.sqrt y) 2
  rw [ha2] at hla
  rw [hb2] at hlb
  norm_num at hla hlb
  have hlog := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div (ne_of_gt ha) (ne_of_gt hb)] at hlog
  have hquot : 1 - (Real.log y - Real.log x) / 2 ≤ Real.sqrt x / Real.sqrt y := by
    linarith
  have hprod := (le_div_iff₀ hb).mp hquot
  have hL : 0 < Real.log y - Real.log x := sub_pos.mpr (Real.log_lt_log hx hxy)
  have hden : 2 * Real.sqrt x * (Real.sqrt y - Real.sqrt x) ≤
      Real.sqrt x * Real.sqrt y * (Real.log y - Real.log x) := by
    nlinarith [mul_nonneg ha.le (show 0 ≤
      Real.sqrt y * (Real.log y - Real.log x) - 2 * (Real.sqrt y - Real.sqrt x) by
        nlinarith)]
  have hsmall : 0 < 2 * Real.sqrt x * (Real.sqrt y - Real.sqrt x) := by positivity
  calc
    _ ≤ 1 / (2 * Real.sqrt x * (Real.sqrt y - Real.sqrt x)) :=
      one_div_le_one_div_of_le hsmall hden
    _ = 1 / (y - x) + 1 / (2 * Real.sqrt x * (Real.sqrt y + Real.sqrt x)) := by
      have hfac : y - x = (Real.sqrt y - Real.sqrt x) *
          (Real.sqrt y + Real.sqrt x) := by nlinarith
      rw [hfac]
      field_simp [ne_of_gt ha, ne_of_gt (sub_pos.mpr hab), ne_of_gt (add_pos hb ha)]
      ring
    _ ≤ _ := by
      apply add_le_add le_rfl
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith

theorem logarithmic_kernel_abs_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hne : x ≠ y) :
    1 / (Real.sqrt x * Real.sqrt y * |Real.log x - Real.log y|) ≤
      1 / |x - y| + 1 / (2 * Real.sqrt x * Real.sqrt y) := by
  rcases lt_or_gt_of_ne hne with h | h
  · rw [abs_of_neg (sub_neg.mpr (Real.log_lt_log hx h)),
      abs_of_neg (sub_neg.mpr h), neg_sub, neg_sub]
    exact logarithmic_kernel_le hx h
  · rw [abs_of_pos (sub_pos.mpr (Real.log_lt_log hy h)), abs_of_pos (sub_pos.mpr h)]
    convert logarithmic_kernel_le hy h using 1 <;> ring

end LiuWang.Proof.GlobalZeroDensity.Sharp
