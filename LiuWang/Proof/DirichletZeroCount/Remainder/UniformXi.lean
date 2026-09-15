import LiuWang.Proof.DirichletZeroCount.Remainder.XiClosedCount
import LiuWang.Proof.DirichletZeroCount.Remainder.UniformClosedCount

/-! # Sharpened principal counts using the sign of the actual Gamma phase -/

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Filter
open scoped Topology Classical
open LiuWang.Proof.LocalAnalyticBounds
open LiuWang.Proof.ChebyshevBound.HighHeight
open LiuWang.Proof.PrincipalPsi.Quantitative
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.Interfaces (Character)

namespace LiuWang.Proof.DirichletZeroCount.Remainder

theorem xi_horizontal_eq_compensated {H : ℝ}
    (ha : ∀ p : RiemannXiDivisorZeroIndex, H - (riemannXiDivisorZeroValue p).im ≠ 0) :
    (HIntegral (logDeriv riemannXi) (1 / 2) 2 H).im =
      (3 / 2) * (logDeriv riemannXi (referencePoint H)).im +
        ∫ x in (1 / 2 : ℝ)..2, ∑' p, indexedImag riemannXiDivisorZeroValue H p x := by
  have hsaway (x : ℝ) : ∀ p : RiemannXiDivisorZeroIndex,
      (x : ℂ) + (H : ℂ) * I ≠ riemannXiDivisorZeroValue p := by
    intro p he
    apply ha p
    have hh := congrArg Complex.im he
    simpa using sub_eq_zero.mpr hh
  have hwaway : ∀ p : RiemannXiDivisorZeroIndex, referencePoint H ≠ riemannXiDivisorZeroValue p := by
    simpa only [referencePoint, ← ofReal_ofNat] using hsaway 2
  have he (x : ℝ) : (logDeriv riemannXi ((x : ℂ) + (H : ℂ) * I)).im =
      (logDeriv riemannXi (referencePoint H)).im +
        ∑' p : RiemannXiDivisorZeroIndex, indexedImag riemannXiDivisorZeroValue H p x := by
    have ht : Summable (xiTerm ((x : ℂ) + (H : ℂ) * I)) :=
      summable_riemannXi_logDerivTerms_divisorZeroIndex₀ (hsaway x)
    have hw := xiTerm_summable (s := referencePoint H) (by norm_num [referencePoint])
    have hd : (∑' p, (1 / ((x : ℂ) + (H : ℂ) * I - riemannXiDivisorZeroValue p) -
        1 / (referencePoint H - riemannXiDivisorZeroValue p))) =
        (∑' p, xiTerm ((x : ℂ) + (H : ℂ) * I) p) - ∑' p, xiTerm (referencePoint H) p := by
      rw [← ht.tsum_sub hw]
      apply tsum_congr
      intro p
      dsimp [xiTerm]
      ring
    have hder : logDeriv riemannXi ((x : ℂ) + (H : ℂ) * I) =
        logDeriv riemannXi (referencePoint H) +
        ∑' p, (1 / ((x : ℂ) + (H : ℂ) * I - riemannXiDivisorZeroValue p) -
          1 / (referencePoint H - riemannXiDivisorZeroValue p)) := by
      rw [hd, xi_hadamard_logDeriv (hsaway x), xi_hadamard_logDeriv hwaway]
      ring
    rw [hder, add_im, Complex.im_tsum (xi_reciprocal_difference_summable (hsaway x) H)]
    rfl
  have hnon (x : ℝ) : riemannXi ((x : ℂ) + (H : ℂ) * I) ≠ 0 := by
    intro hz
    have h0 : (x : ℂ) + (H : ℂ) * I ≠ 0 := by
      intro he
      simp [he, riemannXi_zero] at hz
    obtain ⟨p, hp⟩ := BombieriVinogradov.exists_divisorZeroIndex₀_val_eq_of_apply_eq_zero
      differentiable_riemannXi riemannXi_nontrivial h0 hz
    exact hsaway x p hp.symm
  have hc := horizontal_logDeriv_continuousOn
    (fun _ _ => differentiable_riemannXi.analyticAt _) (fun x _ => hnon x)
  have hi : IntervalIntegrable (fun x : ℝ => logDeriv riemannXi ((x : ℂ) + (H : ℂ) * I))
      volume (1 / 2) 2 := hc.intervalIntegrable_of_Icc (by norm_num)
  have him : (HIntegral (logDeriv riemannXi) (1 / 2) 2 H).im =
      ∫ x in (1 / 2 : ℝ)..2, (logDeriv riemannXi ((x : ℂ) + (H : ℂ) * I)).im :=
    (intervalIntegral.intervalIntegral_im hi).symm
  have his : IntervalIntegrable (fun x : ℝ => ∑' p, indexedImag riemannXiDivisorZeroValue H p x)
      volume (1 / 2) 2 := by
    have h := (continuous_im.comp_continuousOn hc).intervalIntegrable_of_Icc (μ := volume) (by norm_num)
    apply (h.sub (intervalIntegrable_const (c := (logDeriv riemannXi (referencePoint H)).im))).congr
    intro x _
    dsimp only [Function.comp_def]
    linarith [he x]
  rw [him]
  simp_rw [he]
  rw [intervalIntegral.integral_add intervalIntegrable_const his, intervalIntegral.integral_const]
  norm_num

theorem xi_reference_im_lower {H : ℝ} (hH : 0 ≤ H) :
    -(3 / 2 : ℝ) ≤ (logDeriv riemannXi (referencePoint H)).im := by
  have hz : ‖logDeriv riemannZeta (referencePoint H)‖ ≤ 1 := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using L_reference_norm_le_one (1 : Character 1) H
  have hp : -(1 / 2 : ℝ) ≤ (1 / (referencePoint H - 1)).im := by
    have he : (1 / (referencePoint H - 1)).im = -H / (1 + H ^ 2) := by
      simp [referencePoint, one_div, inv_im, normSq_apply, pow_two]
      norm_num
    rw [he]
    apply (le_div_iff₀ (by positivity : 0 < 1 + H ^ 2)).mpr
    nlinarith [sq_nonneg (H - 1)]
  have hg := digamma_im_nonneg (z := referencePoint H / 2 + 1)
    (by norm_num [referencePoint]) (by simpa [referencePoint] using div_nonneg hH (by norm_num : (0 : ℝ) ≤ 2))
  have he := logDeriv_xi_eq_zeta (s := referencePoint H) (by norm_num [referencePoint])
    (by intro h; have hr := congrArg Complex.re h; norm_num [referencePoint] at hr)
    (riemannZeta_ne_zero_of_one_lt_re (by norm_num [referencePoint]))
  rw [he]
  simp only [add_im, sub_im, div_ofNat_im, ofReal_im, zero_div, sub_zero]
  have hh : ((1 / 2 : ℂ) * digamma (referencePoint H / 2 + 1)).im =
      (digamma (referencePoint H / 2 + 1)).im / 2 := by simp; ring
  rw [hh]
  linarith [(abs_le.mp ((abs_im_le_norm _).trans hz)).1]

def uniformXiFee (H : ℝ) : ℝ :=
  9 / 4 + (5 * Real.pi / 2 + 4) * (Real.log (|H| + 2) / 2 + 7 / 3)

theorem xi_horizontal_im_lower {H : ℝ} (hH : 0 ≤ H)
    (ha : ∀ p : RiemannXiDivisorZeroIndex, H - (riemannXiDivisorZeroValue p).im ≠ 0) :
    -uniformXiFee H ≤ (HIntegral (logDeriv riemannXi) (1 / 2) 2 H).im := by
  rw [xi_horizontal_eq_compensated ha]
  have hh := (abs_le.mp (xi_compensated_integral_abs_le ha)).1
  have hr := xi_reference_im_lower hH
  unfold uniformXiFee
  linarith

def uniformXiCountBound (y : ℝ) : ℝ :=
  (3 * Real.pi + sourceGammaMain 4 y - y * Real.log Real.pi + 2 * uniformXiFee y) / Real.pi

theorem uniformXiCountBound_continuous : Continuous uniformXiCountBound := by
  have hl : Continuous (fun H : ℝ => Real.log (|H| + 2)) :=
    (show Continuous (fun H : ℝ => |H| + 2) by fun_prop).log
      (fun H => ne_of_gt (by positivity : 0 < |H| + 2))
  have hg := sourceGammaMain_continuous (a := 4) (by norm_num)
  unfold uniformXiCountBound uniformXiFee
  fun_prop

theorem principal_count_regular_le_uniform (q : ℕ) [NeZero q] {H : ℝ} (hH : 0 ≤ H)
    (hreg : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = H → (1 : Character q).LFunction s ≠ 0) :
    (count (1 : Character q) 0 H : ℝ) ≤ uniformXiCountBound H := by
  have ha : ∀ p : RiemannXiDivisorZeroIndex, H - (riemannXiDivisorZeroValue p).im ≠ 0 := by
    intro p he
    have hr := riemannXiDivisorZeroValue_re_mem_Ioo p
    have hz := (Argument.xi_zero_iff_principal q hr.1 hr.2).mp (riemannXiDivisorZeroValue_eq_zero p)
    exact hreg _ hr.1 hr.2 (by rw [← sub_eq_zero.mp he, abs_of_nonneg hH]) hz
  apply (principal_count_le_xi_horizontal q hH hreg).trans
  unfold uniformXiCountBound
  apply div_le_div_of_nonneg_right _ Real.pi_pos.le
  linarith [xi_horizontal_im_lower hH ha]

theorem principal_count_closed_le_uniform (q : ℕ) [NeZero q] {y : ℝ} (hy : 0 ≤ y) :
    (count (1 : Character q) 0 y : ℝ) ≤ uniformXiCountBound y := by
  by_contra hn
  have hl : uniformXiCountBound y < (count (1 : Character q) 0 y : ℝ) := lt_of_not_ge hn
  have hmem := uniformXiCountBound_continuous.continuousAt.preimage_mem_nhds (Iio_mem_nhds hl)
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hmem
  obtain ⟨H, hyH, hHr, hc, _, hreg⟩ := Applications.exists_common_count_plateau q (y := y) hr
  have hclose : H ∈ Metric.ball y r := by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hyH)]
    linarith
  have hb := principal_count_regular_le_uniform q (hy.trans hyH.le) (hreg 1)
  rw [hc 1 0 H hyH.le le_rfl] at hb
  exact (not_lt_of_ge hb) (hsub hclose)

theorem principal_count_alpha_le_uniform (q : ℕ) [NeZero q] {alpha y : ℝ}
    (ha : 0 ≤ alpha) (hy : 0 ≤ y) :
    (count (1 : Character q) alpha y : ℝ) ≤ uniformXiCountBound y :=
  (Nat.cast_le.mpr (count_antitone_alpha (1 : Character q) y ha)).trans
    (principal_count_closed_le_uniform q hy)

theorem uniformXiCountBound_le_previous (y : ℝ) : uniformXiCountBound y ≤ xiPhaseCountBound y := by
  have hl : 0 ≤ Real.log (|y| + 2) := Real.log_nonneg (by linarith [abs_nonneg y])
  unfold uniformXiCountBound xiPhaseCountBound uniformXiFee xiHorizontalFee
  apply div_le_div_of_nonneg_right _ Real.pi_pos.le
  linarith

end LiuWang.Proof.DirichletZeroCount.Remainder
