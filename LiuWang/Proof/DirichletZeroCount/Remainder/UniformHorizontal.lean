import LiuWang.Proof.DirichletZeroCount.Remainder.GammaHorizontal

/-! # Sharpened ordinary L horizontal fees with no logarithmic Gamma loss -/

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory
open scoped Classical
open LiuWang.Proof.Interfaces (Character CompletedZeroIndex completedZeroValue completedZeroValue_re_mem_Ioo)
open LiuWang.Proof.LocalAnalyticBounds
open LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.DirichletZeroCount.Remainder

def uniformHorizontalFee (q : ℕ) (H : ℝ) : ℝ :=
  3 + 3 * Real.pi / 8 +
    (5 * Real.pi / 2 + 4) * (Real.log q / 2 + Real.log (|H| + 2) / 2 + 2)

theorem L_reference_norm_le_one {q : ℕ} [NeZero q] (chi : Character q) (H : ℝ) :
    ‖logDeriv chi.LFunction (referencePoint H)‖ ≤ 1 := by
  have hh := norm_neg_logDeriv_LFunction_le_zeta_re chi
    (s := referencePoint H) (by norm_num [referencePoint])
  have hz := norm_zeta_real_logDeriv_le_one (s := 2) le_rfl
  simp only [referencePoint, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
    mul_zero, zero_mul, sub_self, add_zero] at hh
  simpa [logDeriv_apply, referencePoint, norm_div, norm_neg] using hh.trans hz

theorem horizontal_L_im_abs_le_uniform {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) {H : ℝ} (hH : H ≠ 0)
    (havoid : ∀ p : CompletedZeroIndex chi, H - (completedZeroValue p).im ≠ 0) :
    |(HIntegral (logDeriv chi.LFunction) (1 / 2) 2 H).im| ≤ uniformHorizontalFee q H := by
  obtain ⟨B, hB, hsep⟩ := exists_separation_of_regular hchi hprim havoid
  have hn (x : ℝ) (hx : x ∈ Set.Icc (1 / 2 : ℝ) 2) :
      chi.LFunction ((x : ℂ) + (H : ℂ) * I) ≠ 0 :=
    LFunction_ne_zero_on_separated_strip hchi hprim hB hH hsep (by simp)
      (by simp; linarith [hx.1])
  have hpos (x : ℝ) (hx : x ∈ Set.Icc (1 / 2 : ℝ) 2) :
      0 < ((x : ℂ) + (H : ℂ) * I).re := by simp; linarith [hx.1]
  have hLc := horizontal_logDeriv_continuousOn
    (fun _ _ => (DirichletCharacter.differentiable_LFunction hchi).analyticAt _) hn
  have hGc := horizontal_logDeriv_continuousOn
    (fun x hx => Argument.gammaFactor_analyticAt chi (hpos x hx))
    (fun x hx => DirichletCharacter.gammaFactor_ne_zero_of_re_pos chi (hpos x hx))
  let R (x : ℝ) : ℝ :=
    (logDeriv chi.LFunction (referencePoint H)).im -
      (logDeriv chi.gammaFactor ((x : ℂ) + (H : ℂ) * I)).im +
      (logDeriv chi.gammaFactor (referencePoint H)).im
  have hab : (1 / 2 : ℝ) ≤ 2 := by norm_num
  have hLi : IntervalIntegrable (fun x : ℝ => logDeriv chi.LFunction ((x : ℂ) + (H : ℂ) * I))
      volume (1 / 2) 2 := hLc.intervalIntegrable_of_Icc hab
  have hLim : IntervalIntegrable (fun x : ℝ => (logDeriv chi.LFunction ((x : ℂ) + (H : ℂ) * I)).im)
      volume (1 / 2) 2 := (continuous_im.comp_continuousOn hLc).intervalIntegrable_of_Icc hab
  have hRi : IntervalIntegrable R volume (1 / 2) 2 :=
    ((continuousOn_const.sub (continuous_im.comp_continuousOn hGc)).add continuousOn_const
      ).intervalIntegrable_of_Icc hab
  have he (x : ℝ) (hx : x ∈ Set.Icc (1 / 2 : ℝ) 2) :
      (logDeriv chi.LFunction ((x : ℂ) + (H : ℂ) * I)).im =
        R x + ∑' p : CompletedZeroIndex chi, compensatedImag chi H p x := by
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
    simp only [referencePoint] at hsum
    rw [hp, add_im, Complex.im_tsum hsum]
    rfl
  have hsumI : IntervalIntegrable (fun x : ℝ =>
      ∑' p : CompletedZeroIndex chi, compensatedImag chi H p x) volume (1 / 2) 2 := by
    apply (hLim.sub hRi).congr
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    dsimp only
    linarith [he x ⟨hx.1.le, hx.2⟩]
  have hsplit :
      (HIntegral (logDeriv chi.LFunction) (1 / 2) 2 H).im =
        (∫ x in (1 / 2 : ℝ)..2, R x) +
        (∫ x in (1 / 2 : ℝ)..2, ∑' p : CompletedZeroIndex chi, compensatedImag chi H p x) := by
    have him : (∫ x in (1 / 2 : ℝ)..2, logDeriv chi.LFunction ((x : ℂ) + (H : ℂ) * I)).im =
        ∫ x in (1 / 2 : ℝ)..2, (logDeriv chi.LFunction ((x : ℂ) + (H : ℂ) * I)).im :=
      (intervalIntegral.intervalIntegral_im hLi).symm
    rw [HIntegral, him, ← intervalIntegral.integral_add hRi hsumI]
    apply intervalIntegral.integral_congr
    intro x hx
    exact he x (by simpa only [Set.uIcc_of_le hab] using hx)
  have hRbound (x : ℝ) (hx : x ∈ Set.Icc (1 / 2 : ℝ) 2) : |R x| ≤ 2 + Real.pi / 4 := by
    have hl := (abs_im_le_norm _).trans (L_reference_norm_le_one chi H)
    have hg := gammaFactor_im_difference_le chi (s := (x : ℂ) + (H : ℂ) * I)
      (w := referencePoint H) (by simpa using hx.1) (by norm_num [referencePoint])
      (by simp [referencePoint])
    have hr : R x = (logDeriv chi.LFunction (referencePoint H)).im -
        ((logDeriv chi.gammaFactor ((x : ℂ) + (H : ℂ) * I)).im -
          (logDeriv chi.gammaFactor (referencePoint H)).im) := by dsimp [R]; ring
    rw [hr]
    exact (abs_sub _ _).trans ((add_le_add hl hg).trans (by ring_nf; rfl))
  have hRint : |∫ x in (1 / 2 : ℝ)..2, R x| ≤ 3 + 3 * Real.pi / 8 := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := R) (a := (1 / 2 : ℝ)) (b := 2) (C := 2 + Real.pi / 4) (fun x hx => by
        rw [Set.uIoc_of_le hab] at hx
        exact (Real.norm_eq_abs _).trans_le (hRbound x ⟨hx.1.le, hx.2⟩))
    rw [Real.norm_eq_abs] at hh
    norm_num only [show 2 - (1 / 2 : ℝ) = 3 / 2 by norm_num,
      abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at hh
    linarith
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add hRint (compensated_sum_integral_abs_le hchi hprim havoid))

theorem horizontal_L_im_abs_le_uniform_regular {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) {H : ℝ} (hH : H ≠ 0)
    (hreg : ∀ s : ℂ, 0 < s.re → s.re < 1 → s.im = H → chi.LFunction s ≠ 0) :
    |(HIntegral (logDeriv chi.LFunction) (1 / 2) 2 H).im| ≤ uniformHorizontalFee q H := by
  apply horizontal_L_im_abs_le_uniform hchi hprim hH
  intro p hp
  have hnon := hreg (completedZeroValue p) (completedZeroValue_re_mem_Ioo hchi hprim p).1
    (completedZeroValue_re_mem_Ioo hchi hprim p).2 (sub_eq_zero.mp hp).symm
  exact ne_symmetricCompletedZeroValue_of_LFunction_ne_zero hchi hnon p rfl

end LiuWang.Proof.DirichletZeroCount.Remainder
