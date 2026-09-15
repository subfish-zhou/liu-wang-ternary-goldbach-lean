import LiuWang.Proof.DirichletZeroCount.Remainder.IndexedHorizontal
import LiuWang.Proof.DirichletZeroCount.Remainder.XiVertical

/-! # The actual xi horizontal edge, with an explicit logarithmic fee -/

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory
open scoped Classical
open LiuWang.Proof.LocalAnalyticBounds
open LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate
open LiuWang.Proof.ChebyshevBound.HighHeight
open LiuWang.Proof.PrincipalPsi.Quantitative
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.Interfaces (Character)

namespace LiuWang.Proof.DirichletZeroCount.Remainder

theorem xi_kernel_nonneg (H : ℝ) (p : RiemannXiDivisorZeroIndex) :
    0 ≤ (1 / (referencePoint H - riemannXiDivisorZeroValue p)).re := by
  rw [one_div, inv_re]
  apply div_nonneg _ (normSq_nonneg _)
  have hr := (riemannXiDivisorZeroValue_re_mem_Ioo p).2
  simpa [referencePoint] using (show 0 ≤ 2 - (riemannXiDivisorZeroValue p).re by linarith)

theorem xi_kernel_le_term (H : ℝ) (p : RiemannXiDivisorZeroIndex) :
    (1 / (referencePoint H - riemannXiDivisorZeroValue p)).re ≤ (xiTerm (referencePoint H) p).re := by
  have hp : 0 ≤ (1 / riemannXiDivisorZeroValue p).re := by
    rw [one_div, inv_re]
    exact div_nonneg (riemannXiDivisorZeroValue_re_mem_Ioo p).1.le (normSq_nonneg _)
  exact le_add_of_nonneg_right hp

theorem xi_kernel_summable (H : ℝ) :
    Summable (fun p : RiemannXiDivisorZeroIndex => (1 / (referencePoint H - riemannXiDivisorZeroValue p)).re) :=
  Summable.of_nonneg_of_le (xi_kernel_nonneg H) (xi_kernel_le_term H)
    (Complex.reCLM.summable (xiTerm_summable (s := referencePoint H) (by norm_num [referencePoint])))

theorem xi_kernel_sum_le (H : ℝ) :
    (∑' p : RiemannXiDivisorZeroIndex, (1 / (referencePoint H - riemannXiDivisorZeroValue p)).re) ≤
      Real.log (|H| + 2) / 2 + 7 / 3 := by
  have ht := xiTerm_summable (s := referencePoint H) (by norm_num [referencePoint])
  have hh := (xi_kernel_summable H).tsum_le_tsum (xi_kernel_le_term H) (Complex.reCLM.summable ht)
  rw [← Complex.re_tsum ht] at hh
  exact hh.trans (xi_reference_mass_improved H)

theorem xi_compensated_integral_abs_le {H : ℝ}
    (ha : ∀ p : RiemannXiDivisorZeroIndex, H - (riemannXiDivisorZeroValue p).im ≠ 0) :
    |∫ x in (1 / 2 : ℝ)..2, ∑' p : RiemannXiDivisorZeroIndex, indexedImag riemannXiDivisorZeroValue H p x| ≤
      (5 * Real.pi / 2 + 4) * (Real.log (|H| + 2) / 2 + 7 / 3) := by
  have hf : {p : RiemannXiDivisorZeroIndex | |H - (riemannXiDivisorZeroValue p).im| ≤ 1}.Finite := by
    simpa only [xiWindowSet, abs_sub_comm] using xiWindowSet_finite H 1
  exact (indexed_integral_abs_le riemannXiDivisorZeroValue_re_mem_Ioo hf (xi_kernel_summable H) ha).trans
    (mul_le_mul_of_nonneg_left (xi_kernel_sum_le H) (by positivity))

theorem xi_reference_im_abs_le (H : ℝ) :
    |(logDeriv riemannXi (referencePoint H)).im| ≤ 17 / 2 + 4 * Real.log (|H| + 2) := by
  have hz := norm_neg_logDeriv_LFunction_le_zeta_re (1 : Character 1)
    (s := referencePoint H) (by norm_num [referencePoint])
  rw [DirichletCharacter.LFunction_modOne_eq] at hz
  have hz' : ‖logDeriv riemannZeta (referencePoint H)‖ ≤ 1 := by
    have hh := norm_zeta_real_logDeriv_le_one (s := 2) le_rfl
    have h := hz.trans (by simpa [referencePoint] using hh)
    simpa [logDeriv_apply, norm_div, norm_neg] using h
  have hn : 1 ≤ ‖referencePoint H - 1‖ := by
    exact le_trans (by norm_num [referencePoint]) (re_le_norm _)
  have hp : ‖1 / (referencePoint H - 1)‖ ≤ 1 := by
    simpa only [one_div, norm_inv] using inv_le_one_of_one_le₀ hn
  have hg := norm_digamma_le_explicit (z := referencePoint H / 2 + 1)
    (by norm_num [referencePoint]) (by norm_num [referencePoint])
  have hl := Real.log_le_log (by positivity : 0 < |(referencePoint H / 2 + 1).im| + 2)
    (show |(referencePoint H / 2 + 1).im| + 2 ≤ |H| + 2 by
      simp [referencePoint, abs_div])
  have he := logDeriv_xi_eq_zeta (s := referencePoint H) (by norm_num [referencePoint])
    (by intro h; have hr := congrArg Complex.re h; norm_num [referencePoint] at hr)
    (riemannZeta_ne_zero_of_one_lt_re (by norm_num [referencePoint]))
  rw [he]
  simp only [add_im, sub_im, div_ofNat_im, ofReal_im, zero_div, sub_zero]
  have ht : |((1 / 2 : ℂ) * digamma (referencePoint H / 2 + 1)).im| ≤
      4 * Real.log (|H| + 2) + 13 / 2 := by
    have hh := abs_im_le_norm ((1 / 2 : ℂ) * digamma (referencePoint H / 2 + 1))
    rw [norm_mul] at hh
    norm_num only [norm_div, norm_one, norm_ofNat] at hh
    linarith
  exact (abs_add_le _ _).trans ((add_le_add_left (abs_add_le _ _) _).trans (by
    linarith [(abs_im_le_norm _).trans hz', (abs_im_le_norm _).trans hp]))

def xiHorizontalFee (H : ℝ) : ℝ :=
  51 / 4 + 6 * Real.log (|H| + 2) +
    (5 * Real.pi / 2 + 4) * (Real.log (|H| + 2) / 2 + 7 / 3)

theorem xi_horizontal_im_abs_le {H : ℝ}
    (ha : ∀ p : RiemannXiDivisorZeroIndex, H - (riemannXiDivisorZeroValue p).im ≠ 0) :
    |(HIntegral (logDeriv riemannXi) (1 / 2) 2 H).im| ≤ xiHorizontalFee H := by
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
  have hsum := xi_compensated_integral_abs_le ha
  have href : |(2 - (1 / 2 : ℝ)) • (logDeriv riemannXi (referencePoint H)).im| ≤
      51 / 4 + 6 * Real.log (|H| + 2) := by
    rw [smul_eq_mul, abs_mul]
    norm_num only [show 2 - (1 / 2 : ℝ) = 3 / 2 by norm_num, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    linarith [xi_reference_im_abs_le H]
  exact (abs_add_le _ _).trans (add_le_add href hsum)

theorem xi_horizontal_im_abs_le_regular (q : ℕ) [NeZero q] {H : ℝ} (hH : 0 ≤ H)
    (hreg : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = H → (1 : Character q).LFunction s ≠ 0) :
    |(HIntegral (logDeriv riemannXi) (1 / 2) 2 H).im| ≤ xiHorizontalFee H := by
  apply xi_horizontal_im_abs_le
  intro p he
  have hr := riemannXiDivisorZeroValue_re_mem_Ioo p
  have hz := (Argument.xi_zero_iff_principal q hr.1 hr.2).mp (riemannXiDivisorZeroValue_eq_zero p)
  exact hreg _ hr.1 hr.2 (by rw [← sub_eq_zero.mp he, abs_of_nonneg hH]) hz

end LiuWang.Proof.DirichletZeroCount.Remainder
