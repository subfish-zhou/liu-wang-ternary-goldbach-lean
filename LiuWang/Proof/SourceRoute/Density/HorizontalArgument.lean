import LiuWang.Proof.SourceRoute.Density.FamilyLittlewood
import LiuWang.Proof.SourceRoute.Density.ReflectedDetector
import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation.ArgumentVariation

/-! Both actual horizontal branches, with their common right-edge anchor paid. -/

set_option autoImplicit false

noncomputable section

open Complex Set Metric MeasureTheory
open scoped Interval
open LiuWang.Proof.Interfaces (Character)
open LiuWang.Proof.NonprincipalDensityAdvance
open LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation

namespace LiuWang.Proof.SourceRoute.Density

theorem horizontalLog_data {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (X : ℝ) {a U h : ℝ}
    (hb : ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), H chi X s ≠ 0)
    (hh : h = -U ∨ h = U) :
    ContinuousOn (horizontalLog (H chi X) 2 U h) [[a, 2]] ∧
      ∀ x ∈ [[a, 2]], Complex.exp (horizontalLog (H chi X) 2 U h x) =
        H chi X ((x : ℂ) + h * I) := by
  have hb' : ∀ s ∈ RectangleBorder ((a : ℂ) + ((-U : ℝ) : ℂ) * I)
      (((2 : ℝ) : ℂ) + U * I), H chi X s ≠ 0 := by
    simpa only [ofReal_neg, ofReal_ofNat, neg_mul, sub_eq_add_neg] using hb
  obtain ⟨hbot, htop, _, hright⟩ :=
    rectangle_nonzero_lines (f := H chi X) (a := a) (b := 2) (c := -U) (d := U) hb'
  have hh' : h ∈ [[-U, U]] := by
    rcases hh with rfl | rfl
    · exact left_mem_uIcc
    · exact right_mem_uIcc
  have hn : ∀ x ∈ [[a, 2]], H chi X ((x : ℂ) + h * I) ≠ 0 := by
    rcases hh with rfl | rfl
    · exact hbot
    · exact htop
  have hpath : ∀ x ∈ [[a, 2]], lineValue (H chi X) (h * I) 1 x ≠ 0 := by
    simpa [lineValue, add_comm] using hn
  constructor
  · change ContinuousOn (lineLog (H chi X) (h * I) 1 2 (rightLog (H chi X) 2 U h)) [[a, 2]]
    exact lineLog_continuousOn (f := H chi X) (p := h * I) (v := 1) (a := a) (b := 2)
      (differentiable_H hchi X) hpath
  · intro x hx
    exact horizontalLog_exp (f := H chi X) (a := a) (b := 2) (c := -U) (d := U)
      (h := h) (x := x) (differentiable_H hchi X) hright hh' hn hx

theorem horizontal_argument_variation {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {X a U h x : ℝ} (hX : 5 ≤ X) (ha : a ≤ 2)
    (hb : ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), H chi X s ≠ 0)
    (hh : h = -U ∨ h = U) (hx : x ∈ Icc a 2) :
    |(horizontalLog (H chi X) 2 U h x).im -
        (horizontalLog (H chi X) 2 U h 2).im| ≤
      ((reflectedZeros chi X h (2 - a)).card + 1 : ℝ) * Real.pi := by
  have hd := horizontalLog_data hchi X hb hh
  have hA : ContinuousOn (fun t : ℝ => (horizontalLog (H chi X) 2 U h t).im)
      (Icc a 2) := by
    simpa only [uIcc_of_le ha, Function.comp_def] using
      Complex.continuous_im.comp_continuousOn hd.1
  have hS : ∀ t ∈ Icc a 2, Real.cos (horizontalLog (H chi X) 2 U h t).im = 0 →
      (t : ℂ) ∈ reflectedZeros chi X h (2 - a) := by
    intro t ht hc
    have he := congrArg Complex.re (hd.2 t (by simpa [uIcc_of_le ha] using ht))
    rw [Complex.exp_re, hc, mul_zero] at he
    have hz := (reflectedDetector_real_zero_iff chi X h t).mpr he.symm
    have htD : (t : ℂ) ∈ closedBall (2 : ℂ) (2 - a) := by
      rw [mem_closedBall_iff_norm]
      have heq : (t : ℂ) - 2 = ((t - 2 : ℝ) : ℂ) := by push_cast; rfl
      rw [heq, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith [ht.2] : t - 2 ≤ 0)]
      linarith [ht.1]
    exact mem_reflectedZeros_of_zero hchi hX htD hz
  have hv := argument_variation_le hx.2
    (hA.mono (Icc_subset_Icc hx.1 le_rfl)) (reflectedZeros chi X h (2 - a))
    (fun t ht => hS t (Icc_subset_Icc hx.1 le_rfl ht))
  simpa only [abs_sub_comm] using hv

theorem horizontal_centered_integral {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {X a U h : ℝ} (hX : 5 ≤ X) (ha : a ≤ 2)
    (hb : ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), H chi X s ≠ 0)
    (hh : h = -U ∨ h = U) :
    |(∫ x in a..2, (horizontalLog (H chi X) 2 U h x).im) -
        (2 - a) * (horizontalLog (H chi X) 2 U h 2).im| ≤
      (2 - a) * (((reflectedZeros chi X h (2 - a)).card + 1 : ℝ) * Real.pi) := by
  have hi : IntervalIntegrable (fun x : ℝ => (horizontalLog (H chi X) 2 U h x).im)
      volume a 2 :=
    (Complex.continuous_im.comp_continuousOn (horizontalLog_data hchi X hb hh).1).intervalIntegrable
  have he :
      (∫ x in a..2, (horizontalLog (H chi X) 2 U h x).im) -
          (2 - a) * (horizontalLog (H chi X) 2 U h 2).im =
        ∫ x in a..2, (horizontalLog (H chi X) 2 U h x).im -
          (horizontalLog (H chi X) 2 U h 2).im := by
    rw [intervalIntegral.integral_sub hi intervalIntegrable_const,
      intervalIntegral.integral_const]
    rfl
  rw [he]
  have hv := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := 2)
    (f := fun x : ℝ => (horizontalLog (H chi X) 2 U h x).im -
      (horizontalLog (H chi X) 2 U h 2).im)
    (C := (((reflectedZeros chi X h (2 - a)).card + 1 : ℝ) * Real.pi))
    (fun x hx => by
      have hx' : x ∈ Icc a 2 := by simpa [uIcc_of_le ha] using uIoc_subset_uIcc hx
      simpa only [Real.norm_eq_abs] using horizontal_argument_variation hchi hX ha hb hh hx')
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ha), mul_comm] using hv

theorem rightLog_variation {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {X U : ℝ} (hX : 5 ≤ X) (hU : 0 ≤ U) :
    |(rightLog (H chi X) 2 U U).im - (rightLog (H chi X) 2 U (-U)).im| ≤ Real.pi := by
  have hn : ∀ t ∈ [[-U, U]], H chi X (((2 : ℝ) : ℂ) + t * I) ≠ 0 :=
    fun t _ => H_ne_zero_on_two chi (by simp) (by linarith)
  have hA : ContinuousOn (fun t : ℝ => (rightLog (H chi X) 2 U t).im) (Icc (-U) U) := by
    simpa only [rightLog, ofReal_ofNat, uIcc_of_le (show -U ≤ U by linarith),
      Function.comp_def] using
      Complex.continuous_im.comp_continuousOn
        (lineLog_continuousOn (differentiable_H hchi X) hn
          (l := Complex.log (H chi X (((2 : ℝ) : ℂ) + U * I))))
  have hcos : ∀ t ∈ Icc (-U) U, Real.cos (rightLog (H chi X) 2 U t).im = 0 →
      (t : ℂ) ∈ (∅ : Finset ℂ) := by
    intro t ht hz
    have he := congrArg Complex.re (rightLog_exp (differentiable_H hchi X) hn
      (by simpa [uIcc_of_le (show -U ≤ U by linarith)] using ht))
    rw [Complex.exp_re, hz, mul_zero] at he
    have hr := H_re_two_lower chi (by linarith : 1 < X) t
    have hq : 4 / (X - 1) ^ 2 ≤ 1 / 4 := by
      apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < X - 1))).mpr
      nlinarith
    norm_num only [ofReal_ofNat] at he
    exfalso
    linarith
  simpa using argument_variation_le (by linarith : -U ≤ U) hA ∅ hcos

theorem horizontal_card_bound {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {X a U : ℝ} (hX : 5 ≤ X) (ha : a ≤ 2) (hU : 0 ≤ U)
    (hb : ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), H chi X s ≠ 0) :
    (∫ x in a..2, (horizontalLog (H chi X) 2 U U x).im) -
        (∫ x in a..2, (horizontalLog (H chi X) 2 U (-U) x).im) ≤
      (2 - a) * Real.pi *
        ((reflectedZeros chi X U (2 - a)).card +
          (reflectedZeros chi X (-U) (2 - a)).card + 3 : ℝ) := by
  have hp := horizontal_centered_integral hchi hX ha hb (Or.inr rfl)
  have hm := horizontal_centered_integral hchi hX ha hb (Or.inl rfl)
  simp only [horizontalLog, lineLog_anchor] at hp hm
  have hr := rightLog_variation hchi hX hU
  have hmul := mul_le_mul_of_nonneg_left (abs_le.mp hr).2 (sub_nonneg.mpr ha)
  simp only [horizontalLog]
  nlinarith [(abs_le.mp hp).2, (abs_le.mp hm).1]

theorem family_horizontal_card_bound (q : ℕ) [NeZero q] {X a U : ℝ}
    (hX : 5 ≤ X) (ha : a ≤ 2) (hU : 0 ≤ U)
    (hb : ∀ chi ∈ nonprincipalCharacters q,
      ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), H chi X s ≠ 0) :
    horizontalDifference q X a U ≤
      (2 - a) * Real.pi *
        ((∑ chi ∈ nonprincipalCharacters q,
          ((reflectedZeros chi X U (2 - a)).card +
            (reflectedZeros chi X (-U) (2 - a)).card + 3 : ℝ)) / q.totient) := by
  have h := Finset.sum_le_sum (s := nonprincipalCharacters q) (fun chi hchi =>
    horizontal_card_bound ((mem_nonprincipalCharacters chi).mp hchi) hX ha hU (hb chi hchi))
  rw [← Finset.mul_sum] at h
  exact (div_le_div_of_nonneg_right h (Nat.cast_nonneg _)).trans_eq (by ring)

end LiuWang.Proof.SourceRoute.Density
