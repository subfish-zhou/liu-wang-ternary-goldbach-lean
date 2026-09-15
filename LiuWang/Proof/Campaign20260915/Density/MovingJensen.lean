import LiuWang.Proof.SourceRoute.Density.Restart.ProductHorizontal

set_option autoImplicit false
noncomputable section

open Complex Set Metric
open LiuWang.Proof.SourceRoute.Density.Restart
open LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation

namespace LiuWang.Proof.Campaign20260915.Density

theorem product_horizontal_argument_moving (q : ℕ) [NeZero q] {X a U h x r : ℝ}
    (hX : 100000 ≤ X) (hqX : (q : ℝ) ≤ X) (hU : 0 ≤ U)
    (hb : ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I),
      familyProduct q X s ≠ 0)
    (hh : h = -U ∨ h = U) (hx : x ∈ Icc a 2) (hr : 2 - x ≤ r) :
    |(horizontalLog (familyProduct q X) 2 U h x).im| ≤
      ((productReflectedZeros q X h r).card + 1 : ℝ) * Real.pi := by
  have ha : a ≤ 2 := hx.1.trans hx.2
  have hd := entire_horizontalLog_data (familyProduct_differentiable q X) hb hh
  have hA : ContinuousOn (fun t : ℝ => (horizontalLog (familyProduct q X) 2 U h t).im)
      (Icc a 2) := by
    simpa only [uIcc_of_le ha, Function.comp_def] using
      Complex.continuous_im.comp_continuousOn hd.1
  have hS : ∀ t ∈ Icc x 2, Real.cos (horizontalLog (familyProduct q X) 2 U h t).im = 0 →
      (t : ℂ) ∈ productReflectedZeros q X h r := by
    intro t ht hc
    have hta : t ∈ Icc a 2 := ⟨hx.1.trans ht.1, ht.2⟩
    have he := congrArg Complex.re (hd.2 t (by simpa only [uIcc_of_le ha] using hta))
    rw [Complex.exp_re, hc, mul_zero] at he
    have hz := (productReflection_real_zero_iff q X h t).mpr he.symm
    have htD : (t : ℂ) ∈ closedBall (2 : ℂ) r := by
      rw [mem_closedBall_iff_norm]
      have heq : (t : ℂ) - 2 = ((t - 2 : ℝ) : ℂ) := by push_cast; rfl
      rw [heq, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith [ht.2] : t - 2 ≤ 0)]
      linarith [ht.1]
    exact mem_productReflectedZeros q hX hqX htD hz
  apply anchored_argument_bound hx.2 (hA.mono (Icc_subset_Icc hx.1 le_rfl))
    (productReflectedZeros q X h r) hS
  simp only [horizontalLog, lineLog_anchor]
  apply (product_rightLog_anchor q hX hqX hU _).le
  rcases hh with rfl | rfl <;> constructor <;> linarith

theorem moving_radii_log_lower {x d : ℝ} (hd : 0 < d)
    (hx : x < 2) (hR : 2 - x + d / 2 ≤ 3 / 2) :
    d / 3 ≤ Real.log ((2 - x + d / 2) / (2 - x)) := by
  have hr : 0 < 2 - x := by linarith
  have hRp : 0 < 2 - x + d / 2 := by linarith
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hRp hr)
  have he : 1 - ((2 - x + d / 2) / (2 - x))⁻¹ =
      (d / 2) / (2 - x + d / 2) := by field_simp; ring
  rw [he] at h
  apply le_trans _ h
  apply (le_div_iff₀ hRp).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hR hd.le]

theorem product_moving_radii_count (q : ℕ) [NeZero q] {X T U x d : ℝ}
    (hX : 100000 ≤ X) (hqX : (q : ℝ) ≤ X) (hd : 0 < d) (hx : x < 2)
    (hwin : |U - T| + (2 - x + d / 2) ≤ 3 / 2) :
    ((productReflectedZeros q X U (2 - x)).card : ℝ) ≤
      3 / d * (Real.log (2 / (199499 / 100000 : ℝ)) +
        familyMaximum q X T (x - d / 2) (4 - x + d / 2)) := by
  have hr : 0 < 2 - x := by linarith
  have hR : 2 - x + d / 2 ≤ 3 / 2 := by linarith [abs_nonneg (U - T)]
  have hj := product_jensen_common_maximum q hX hqX hr
    (show 2 - x < 2 - x + d / 2 by linarith) hwin
  have he : 2 - (2 - x + d / 2) = x - d / 2 := by ring
  have he' : 2 + (2 - x + d / 2) = 4 - x + d / 2 := by ring
  rw [he, he'] at hj
  have hN : 0 ≤ Real.log (2 / (199499 / 100000 : ℝ)) +
      familyMaximum q X T (x - d / 2) (4 - x + d / 2) :=
    add_nonneg (Real.log_nonneg (by norm_num))
      (familyMaximum_nonneg q X T (by linarith))
  exact hj.trans ((div_le_div_of_nonneg_left hN (by positivity)
    (moving_radii_log_lower hd hx hR)).trans_eq (by field_simp))

end LiuWang.Proof.Campaign20260915.Density
