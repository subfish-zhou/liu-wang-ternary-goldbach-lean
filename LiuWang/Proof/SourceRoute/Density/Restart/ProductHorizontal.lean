import LiuWang.Proof.SourceRoute.Density.Restart.ProductContour
import LiuWang.Proof.SourceRoute.Density.Restart.ProductJensen
import LiuWang.Proof.SourceRoute.Density.Restart.AnchoredArgument

/-! Both horizontal sides of the actual product, with the source argument normalization. -/

set_option autoImplicit false

noncomputable section

open Complex Set Metric MeasureTheory
open scoped Interval
open LiuWang.Proof.NonprincipalDensityAdvance
open LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation

namespace LiuWang.Proof.SourceRoute.Density.Restart

theorem entire_horizontalLog_data {F : ℂ → ℂ} (hf : Differentiable ℂ F) {a U h : ℝ}
    (hb : ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), F s ≠ 0)
    (hh : h = -U ∨ h = U) :
    ContinuousOn (horizontalLog F 2 U h) [[a, 2]] ∧
      ∀ x ∈ [[a, 2]], Complex.exp (horizontalLog F 2 U h x) = F ((x : ℂ) + h * I) := by
  have hb' : ∀ s ∈ RectangleBorder ((a : ℂ) + ((-U : ℝ) : ℂ) * I)
      (((2 : ℝ) : ℂ) + U * I), F s ≠ 0 := by
    simpa only [ofReal_neg, ofReal_ofNat, neg_mul, sub_eq_add_neg] using hb
  obtain ⟨hbot, htop, _, hright⟩ :=
    rectangle_nonzero_lines (a := a) (b := 2) (c := -U) (d := U) hb'
  have hh' : h ∈ [[-U, U]] := by
    rcases hh with rfl | rfl
    · exact left_mem_uIcc
    · exact right_mem_uIcc
  have hn : ∀ x ∈ [[a, 2]], F ((x : ℂ) + h * I) ≠ 0 := by
    rcases hh with rfl | rfl
    · exact hbot
    · exact htop
  have hpath : ∀ x ∈ [[a, 2]], lineValue F (h * I) 1 x ≠ 0 := by
    simpa [lineValue, add_comm] using hn
  exact ⟨lineLog_continuousOn hf hpath, fun x hx =>
    horizontalLog_exp hf hright hh' hn hx⟩

theorem product_rightLog_anchor (q : ℕ) [NeZero q] {X U : ℝ}
    (hX : 100000 ≤ X) (hqX : (q : ℝ) ≤ X) (hU : 0 ≤ U)
    {t : ℝ} (ht : t ∈ Icc (-U) U) :
    |(rightLog (familyProduct q X) 2 U t).im| < Real.pi / 2 := by
  have hn : ∀ t ∈ [[-U, U]], familyProduct q X (((2 : ℝ) : ℂ) + t * I) ≠ 0 :=
    fun t _ => familyProduct_two_ne_zero q (by linarith) (by simp)
  have hA : ContinuousOn (fun t : ℝ => (rightLog (familyProduct q X) 2 U t).im)
      (Icc (-U) U) := by
    simpa only [rightLog, ofReal_ofNat, uIcc_of_le (show -U ≤ U by linarith),
      Function.comp_def] using
      Complex.continuous_im.comp_continuousOn
        (lineLog_continuousOn (familyProduct_differentiable q X) hn
          (l := Complex.log (familyProduct q X (((2 : ℝ) : ℂ) + U * I))))
  have hcos : ∀ t ∈ Icc (-U) U, Real.cos (rightLog (familyProduct q X) 2 U t).im ≠ 0 := by
    intro t ht hz
    have he := congrArg Complex.re (rightLog_exp (familyProduct_differentiable q X) hn
      (by simpa [uIcc_of_le (show -U ≤ U by linarith)] using ht))
    rw [Complex.exp_re, hz, mul_zero] at he
    have hr := familyProduct_right_re q hX hqX (s := (2 : ℂ) + t * I) (by simp)
    norm_num only [ofReal_ofNat] at he
    linarith
  apply argument_stays_right hA hcos _ ht
  simp only [rightLog, lineLog_anchor, Complex.log_im]
  apply Complex.abs_arg_lt_pi_div_two_iff.mpr
  left
  have hr := familyProduct_right_re q hX hqX (s := (2 : ℂ) + U * I) (by simp)
  norm_num only [ofReal_ofNat]
  linarith

theorem product_horizontal_argument (q : ℕ) [NeZero q] {X a U h x r : ℝ}
    (hX : 100000 ≤ X) (hqX : (q : ℝ) ≤ X) (hU : 0 ≤ U)
    (hb : ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I),
      familyProduct q X s ≠ 0)
    (hh : h = -U ∨ h = U) (hx : x ∈ Icc a 2) (hr : 2 - a ≤ r) :
    |(horizontalLog (familyProduct q X) 2 U h x).im| ≤
      ((productReflectedZeros q X h r).card + 1 : ℝ) * Real.pi := by
  have ha : a ≤ 2 := hx.1.trans hx.2
  have hd := entire_horizontalLog_data (familyProduct_differentiable q X) hb hh
  have hA : ContinuousOn (fun t : ℝ => (horizontalLog (familyProduct q X) 2 U h t).im)
      (Icc a 2) := by
    simpa only [uIcc_of_le ha, Function.comp_def] using
      Complex.continuous_im.comp_continuousOn hd.1
  have hS : ∀ t ∈ Icc a 2, Real.cos (horizontalLog (familyProduct q X) 2 U h t).im = 0 →
      (t : ℂ) ∈ productReflectedZeros q X h r := by
    intro t ht hc
    have he := congrArg Complex.re (hd.2 t (by simpa only [uIcc_of_le ha] using ht))
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
    (productReflectedZeros q X h r) (fun t ht => hS t (Icc_subset_Icc hx.1 le_rfl ht))
  simp only [horizontalLog, lineLog_anchor]
  apply (product_rightLog_anchor q hX hqX hU _).le
  rcases hh with rfl | rfl <;> constructor <;> linarith

theorem product_horizontal_integral (q : ℕ) [NeZero q] {X a U h r : ℝ}
    (hX : 100000 ≤ X) (hqX : (q : ℝ) ≤ X) (ha : a ≤ 2) (hU : 0 ≤ U)
    (hb : ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I),
      familyProduct q X s ≠ 0)
    (hh : h = -U ∨ h = U) (hr : 2 - a ≤ r) :
    |∫ x in a..2, (horizontalLog (familyProduct q X) 2 U h x).im| ≤
      (2 - a) * (((productReflectedZeros q X h r).card + 1 : ℝ) * Real.pi) := by
  have hv := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := 2)
    (f := fun x : ℝ => (horizontalLog (familyProduct q X) 2 U h x).im)
    (C := (((productReflectedZeros q X h r).card + 1 : ℝ) * Real.pi))
    (fun x hx => by
      have hx' : x ∈ Icc a 2 := by simpa [uIcc_of_le ha] using uIoc_subset_uIcc hx
      simpa only [Real.norm_eq_abs] using product_horizontal_argument q hX hqX hU hb hh hx' hr)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ha), mul_comm] using hv

theorem product_horizontal_card_bound (q : ℕ) [NeZero q] {X a U r : ℝ}
    (hX : 100000 ≤ X) (hqX : (q : ℝ) ≤ X) (ha : a ≤ 2) (hU : 0 ≤ U)
    (hb : ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I),
      familyProduct q X s ≠ 0)
    (hr : 2 - a ≤ r) :
    productHorizontal q X a U ≤
      2 * (2 - a) * Real.pi * ((productReflectedZeros q X U r).card + 1 : ℝ) := by
  have hp := product_horizontal_integral q hX hqX ha hU hb (Or.inr rfl) hr
  have hm := product_horizontal_integral q hX hqX ha hU hb (Or.inl rfl) hr
  rw [productReflectedZeros_neg] at hm
  unfold productHorizontal
  nlinarith [(abs_le.mp hp).2, (abs_le.mp hm).1]

theorem product_horizontal_source_bound (q : ℕ) [NeZero q] {X T U a xi d : ℝ}
    (hX : 100000 ≤ X) (hqX : (q : ℝ) ≤ X) (ha : a ≤ 2) (hU : 0 ≤ U)
    (hd : 0 < d) (hxi : 1 / 2 + 2 * d ≤ xi) (hxi1 : xi < 1)
    (hleft : xi - d ≤ a) (hwin : |U - T| + (2 - xi + 3 * d / 2) ≤ 3 / 2)
    (hb : ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I),
      familyProduct q X s ≠ 0) :
    productHorizontal q X a U ≤ 2 * (2 - a) * Real.pi *
      (3 / d * (Real.log (2 / (199499 / 100000 : ℝ)) +
        familyMaximum q X T (xi - 3 * d / 2) (4 - xi + 3 * d / 2)) + 1) := by
  apply (product_horizontal_card_bound q hX hqX ha hU hb
    (show 2 - a ≤ 2 - xi + d by linarith)).trans
  exact mul_le_mul_of_nonneg_left
    (add_le_add (product_source_radii_count q hX hqX hd hxi hxi1 hwin) (le_refl 1))
    (by positivity)

end LiuWang.Proof.SourceRoute.Density.Restart
