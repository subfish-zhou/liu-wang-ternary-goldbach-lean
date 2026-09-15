import LiuWang.Proof.DirichletZeroCount.Remainder.HorizontalSum
import LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate.LogDerivative

/-! # Explicit ordinary L horizontal phase fees at every regular height -/

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory
open scoped Classical
open LiuWang.Proof.Interfaces (Character CompletedZeroIndex completedZeroValue completedZeroValue_re_mem_Ioo)
open LiuWang.Proof.LocalAnalyticBounds
open LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.DirichletZeroCount.Remainder

def horizontalFee (q : ℕ) (H : ℝ) : ℝ :=
  57 / 2 + 12 * Real.log (|H| + 2) +
    (5 * Real.pi / 2 + 4) * (Real.log q / 2 + Real.log (|H| + 2) / 2 + 2)

theorem horizontal_logDeriv_continuousOn {F : ℂ → ℂ} {H : ℝ}
    (ha : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, AnalyticAt ℂ F ((x : ℂ) + (H : ℂ) * I))
    (hn : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, F ((x : ℂ) + (H : ℂ) * I) ≠ 0) :
    ContinuousOn (fun x : ℝ => logDeriv F ((x : ℂ) + (H : ℂ) * I)) (Set.Icc (1 / 2 : ℝ) 2) := by
  intro x hx
  have hc := ((ha x hx).deriv.div (ha x hx) (hn x hx)).continuousAt.comp
    (f := fun t : ℝ => (t : ℂ) + (H : ℂ) * I) (by fun_prop)
  simpa only [logDeriv_apply, Function.comp_def, Pi.div_apply] using! hc.continuousWithinAt

theorem horizontal_L_im_abs_le {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) {H : ℝ} (hH : 2 ≤ |H|)
    (havoid : ∀ p : CompletedZeroIndex chi, H - (completedZeroValue p).im ≠ 0) :
    |(HIntegral (logDeriv chi.LFunction) (1 / 2) 2 H).im| ≤ horizontalFee q H := by
  have hH0 : H ≠ 0 := by intro he; norm_num [he] at hH
  obtain ⟨B, hB, hsep⟩ := exists_separation_of_regular hchi hprim havoid
  have hn (x : ℝ) (hx : x ∈ Set.Icc (1 / 2 : ℝ) 2) :
      chi.LFunction ((x : ℂ) + (H : ℂ) * I) ≠ 0 :=
    LFunction_ne_zero_on_separated_strip hchi hprim hB hH0 hsep (by simp)
      (by simp; linarith [hx.1])
  have hpos (x : ℝ) (hx : x ∈ Set.Icc (1 / 2 : ℝ) 2) :
      0 < ((x : ℂ) + (H : ℂ) * I).re := by simp; linarith [hx.1]
  have hLc := horizontal_logDeriv_continuousOn
    (fun _ _ => (DirichletCharacter.differentiable_LFunction hchi).analyticAt _) hn
  have hGc := horizontal_logDeriv_continuousOn
    (fun x hx => Argument.gammaFactor_analyticAt chi (hpos x hx))
    (fun x hx => DirichletCharacter.gammaFactor_ne_zero_of_re_pos chi (hpos x hx))
  let R (x : ℝ) : ℂ :=
    logDeriv chi.LFunction (referencePoint H) -
      logDeriv chi.gammaFactor ((x : ℂ) + (H : ℂ) * I) +
      logDeriv chi.gammaFactor (referencePoint H)
  have hRc : ContinuousOn R (Set.Icc (1 / 2 : ℝ) 2) :=
    (continuousOn_const.sub hGc).add continuousOn_const
  have hab : (1 / 2 : ℝ) ≤ 2 := by norm_num
  have hLi : IntervalIntegrable (fun x : ℝ => logDeriv chi.LFunction ((x : ℂ) + (H : ℂ) * I))
      volume (1 / 2) 2 := hLc.intervalIntegrable_of_Icc hab
  have hRi : IntervalIntegrable R volume (1 / 2) 2 := hRc.intervalIntegrable_of_Icc hab
  have hLim : IntervalIntegrable (fun x : ℝ => (logDeriv chi.LFunction ((x : ℂ) + (H : ℂ) * I)).im)
      volume (1 / 2) 2 := (continuous_im.comp_continuousOn hLc).intervalIntegrable_of_Icc hab
  have hRim : IntervalIntegrable (fun x : ℝ => (R x).im) volume (1 / 2) 2 :=
    (continuous_im.comp_continuousOn hRc).intervalIntegrable_of_Icc hab
  have he (x : ℝ) (hx : x ∈ Set.Icc (1 / 2 : ℝ) 2) :
      (logDeriv chi.LFunction ((x : ℂ) + (H : ℂ) * I)).im =
        (R x).im + ∑' p : CompletedZeroIndex chi, compensatedImag chi H p x := by
    have hp := logDeriv_LFunction_eq_reference_add_zero_difference hchi hprim (hn x hx)
      (DirichletCharacter.gammaFactor_ne_zero_of_re_pos chi (hpos x hx))
      (DirichletCharacter.differentiableAt_gammaFactor_of_re_pos chi (hpos x hx)) H
    have hsaway : ∀ p : CompletedZeroIndex chi, (x : ℂ) + (H : ℂ) * I ≠ completedZeroValue p := by
      intro p hp
      apply havoid p
      have hh := congrArg Complex.im hp
      simpa using sub_eq_zero.mpr hh
    have hwaway : ∀ p : CompletedZeroIndex chi, referencePoint H ≠ completedZeroValue p := by
      intro p hp
      have hr := (completedZeroValue_re_mem_Ioo hchi hprim p).2
      simp [← hp, referencePoint] at hr
    have hsum := summable_completedZero_reciprocalDifference hchi hprim hsaway hwaway
    norm_num only [ofReal_ofNat] at hp
    change logDeriv chi.LFunction ((x : ℂ) + (H : ℂ) * I) = R x +
      ∑' p : CompletedZeroIndex chi,
        (1 / ((x : ℂ) + (H : ℂ) * I - completedZeroValue p) -
          1 / (referencePoint H - completedZeroValue p)) at hp
    rw [hp, add_im, Complex.im_tsum hsum]
    rfl
  have hsumI : IntervalIntegrable (fun x : ℝ =>
      ∑' p : CompletedZeroIndex chi, compensatedImag chi H p x) volume (1 / 2) 2 := by
    apply (hLim.sub hRim).congr
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    dsimp only
    linarith [he x ⟨hx.1.le, hx.2⟩]
  have hsplit :
      (HIntegral (logDeriv chi.LFunction) (1 / 2) 2 H).im =
        (∫ x in (1 / 2 : ℝ)..2, (R x).im) +
        (∫ x in (1 / 2 : ℝ)..2, ∑' p : CompletedZeroIndex chi, compensatedImag chi H p x) := by
    have hLimeq : (∫ x in (1 / 2 : ℝ)..2, logDeriv chi.LFunction ((x : ℂ) + (H : ℂ) * I)).im =
        ∫ x in (1 / 2 : ℝ)..2, (logDeriv chi.LFunction ((x : ℂ) + (H : ℂ) * I)).im := by
      exact (intervalIntegral.intervalIntegral_im hLi).symm
    rw [HIntegral, hLimeq, ← intervalIntegral.integral_add hRim hsumI]
    apply intervalIntegral.integral_congr
    intro x hx
    exact he x (by simpa only [Set.uIcc_of_le hab] using hx)
  have hRbound (x : ℝ) (hx : x ∈ Set.Icc (1 / 2 : ℝ) 2) :
      ‖R x‖ ≤ 19 + 8 * Real.log (|H| + 2) := by
    have hl : ‖logDeriv chi.LFunction (referencePoint H)‖ ≤ 1 := by
      have hh := norm_neg_logDeriv_LFunction_le_zeta_re chi
        (s := referencePoint H) (by norm_num [referencePoint])
      have hz := norm_zeta_real_logDeriv_le_one
        (s := 2) (le_refl (2 : ℝ))
      have hz' : ‖-deriv riemannZeta ((referencePoint H).re : ℂ) /
          riemannZeta ((referencePoint H).re : ℂ)‖ ≤ 1 := by
        simpa [referencePoint] using hz
      simpa [logDeriv_apply, norm_div, norm_neg] using hh.trans hz'
    have hs := norm_logDeriv_gammaFactor_horizontal_explicit chi
      (s := (x : ℂ) + (H : ℂ) * I) (by simp; linarith [hx.1])
      (by simpa using hx.2) (by simpa using hH)
    have hw := norm_logDeriv_gammaFactor_horizontal_explicit chi
      (s := referencePoint H) (by norm_num [referencePoint]) (by norm_num [referencePoint])
      (by simpa [referencePoint] using hH)
    simp only [add_im, mul_im, ofReal_im, ofReal_re, I_re, I_im, mul_one, mul_zero, add_zero,
      zero_add] at hs
    have hh : ‖R x‖ ≤ ‖logDeriv chi.LFunction (referencePoint H)‖ +
        ‖logDeriv chi.gammaFactor ((x : ℂ) + (H : ℂ) * I)‖ +
        ‖logDeriv chi.gammaFactor (referencePoint H)‖ :=
      (norm_add_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
    rw [show (referencePoint H).im = H by simp [referencePoint]] at hw
    linarith
  have hRint : |∫ x in (1 / 2 : ℝ)..2, (R x).im| ≤ 57 / 2 + 12 * Real.log (|H| + 2) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x : ℝ => (R x).im) (a := (1 / 2 : ℝ)) (b := 2)
      (C := 19 + 8 * Real.log (|H| + 2)) (fun x hx => by
        rw [Set.uIoc_of_le hab] at hx
        rw [Real.norm_eq_abs]
        exact (abs_im_le_norm _).trans (hRbound x ⟨hx.1.le, hx.2⟩))
    rw [Real.norm_eq_abs] at hh
    norm_num only [show 2 - (1 / 2 : ℝ) = 3 / 2 by norm_num,
      abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at hh
    linarith
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add hRint (compensated_sum_integral_abs_le hchi hprim havoid))

theorem horizontal_L_im_abs_le_regular {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) {H : ℝ} (hH : 2 ≤ |H|)
    (hreg : ∀ s : ℂ, 0 < s.re → s.re < 1 → s.im = H → chi.LFunction s ≠ 0) :
    |(HIntegral (logDeriv chi.LFunction) (1 / 2) 2 H).im| ≤ horizontalFee q H := by
  apply horizontal_L_im_abs_le hchi hprim hH
  intro p hp
  have hnon := hreg (completedZeroValue p) (completedZeroValue_re_mem_Ioo hchi hprim p).1
    (completedZeroValue_re_mem_Ioo hchi hprim p).2 (sub_eq_zero.mp hp).symm
  exact ne_symmetricCompletedZeroValue_of_LFunction_ne_zero hchi hnon p rfl

end LiuWang.Proof.DirichletZeroCount.Remainder
