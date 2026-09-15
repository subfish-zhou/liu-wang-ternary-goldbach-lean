import LiuWang.Proof.DirichletZeroCount.Smoothed

/-! # Sharpened principal and complete-character count producers -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.LocalAnalyticBounds
open LiuWang.Proof.PrincipalPsi.Quantitative
open LiuWang.Proof.ChebyshevBound.HighHeight
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.DirichletZeroCount

theorem xi_reference_mass_improved (t : ℝ) :
    (∑' p, xiTerm (referencePoint t) p).re ≤ Real.log (|t| + 2) / 2 + 7 / 3 := by
  have he := Robin1984.neg_riemannZeta_logDeriv_eq_xiDivisor_tsum
    (s := referencePoint t) (by norm_num [referencePoint])
  have hn := norm_neg_logDeriv_LFunction_le_zeta_re
    (1 : Character 1) (s := referencePoint t) (by norm_num [referencePoint])
  rw [DirichletCharacter.LFunction_modOne_eq] at hn
  have hnorm : ‖-deriv riemannZeta (referencePoint t) / riemannZeta (referencePoint t)‖ ≤ 1 :=
    hn.trans (by simpa [referencePoint] using norm_zeta_real_logDeriv_le_one (s := 2) le_rfl)
  have hreal : -1 ≤ (-deriv riemannZeta (referencePoint t) / riemannZeta (referencePoint t)).re :=
    (abs_le.mp ((Complex.abs_re_le_norm _).trans hnorm)).1
  have hp : (1 / (referencePoint t - 1)).re ≤ 1 := by
    have hnorm1 : 1 ≤ ‖referencePoint t - 1‖ :=
      le_trans (by norm_num [referencePoint]) (Complex.re_le_norm _)
    apply (Complex.re_le_norm _).trans
    simpa only [one_div, norm_inv] using inv_le_one_of_one_le₀ hnorm1
  have ha := archimedean_re_le (s := referencePoint t)
    (by norm_num [referencePoint]) (by norm_num [referencePoint])
  have heR := congrArg Complex.re he
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re] at heR
  norm_num only [Complex.mul_re, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_div, zero_mul, sub_zero] at heR
  simp only [one_div_mul_eq_div] at heR
  rw [show (referencePoint t).im = t by simp [referencePoint]] at ha
  change _ = -(logDeriv Complex.riemannXi 0).re - (∑' p, xiTerm (referencePoint t) p).re +
    _ - _ + _ at heR
  linarith

theorem xi_count_smoothed {y a : ℝ} (hy : 0 ≤ y) (ha : 0 < a) :
    ((xiWindow 0 y).card : ℝ) ≤
      (y + a) * (Real.log (y + a + 2) / 2 + 7 / 3) / Real.arctan (a / 2) := by
  apply finite_count_smoothed _ riemannXiDivisorZeroValue hy ha
  · exact fun p _ => riemannXiDivisorZeroValue_re_mem_Ioo p
  · exact fun p hp => by simpa using mem_xiWindow.mp hp
  · intro t ht
    have hs1 : 1 ≤ (referencePoint t).re := by norm_num [referencePoint]
    have hs := Complex.reCLM.summable (xiTerm_summable hs1)
    have hlog := Real.log_le_log (by positivity : 0 < |t| + 2)
      (show |t| + 2 ≤ y + a + 2 by linarith [abs_le.mpr ht])
    calc
      _ ≤ ∑ p ∈ xiWindow 0 y, (xiTerm (referencePoint t) p).re := by
        apply Finset.sum_le_sum
        intro p _
        rw [heightKernel_eq]
        have hr := (riemannXiDivisorZeroValue_re_mem_Ioo p).1
        have hp0 : 0 ≤ (1 / riemannXiDivisorZeroValue p).re := by
          rw [one_div, Complex.inv_re]
          exact div_nonneg hr.le (Complex.normSq_nonneg _)
        simpa only [xiTerm, Complex.add_re] using
          le_add_of_nonneg_right (a := (1 / (referencePoint t - riemannXiDivisorZeroValue p)).re) hp0
      _ ≤ (∑' p, xiTerm (referencePoint t) p).re := by
        rw [Complex.re_tsum (xiTerm_summable hs1)]
        exact hs.sum_le_tsum _ (fun p _ => xiTerm_re_nonneg hs1 p)
      _ ≤ _ := (xi_reference_mass_improved t).trans (by linarith)

theorem count_principal_smoothed (q : ℕ) [NeZero q] (alpha : ℝ)
    {y a : ℝ} (hy : 0 ≤ y) (ha : 0 < a) :
    (count (1 : Character q) alpha y : ℝ) ≤
      (y + a) * (Real.log (y + a + 2) / 2 + 7 / 3) / Real.arctan (a / 2) := by
  rw [count_principal_eq_zeta, count_principal]
  have hc : ((principalIndices 1 alpha y).card : ℝ) ≤
      ((PrincipalPsi.closedZeroIndices 1 y).card : ℝ) :=
    Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
  rw [card_principal_closed_eq_xi] at hc
  exact hc.trans (xi_count_smoothed hy ha)

def sharpenedBound {q : ℕ} [NeZero q] (chi : Character q) (y a : ℝ) : ℝ :=
  min (characterBound chi y)
    (if chi = 1 then
      (y + a) * (Real.log (y + a + 2) / 2 + 7 / 3) / Real.arctan (a / 2)
    else (y + a) * (Real.log chi.conductor / 2 + Real.log (y + a + 2) / 2 + 2) /
      Real.arctan (a / 2))

theorem count_le_sharpenedBound {q : ℕ} [NeZero q] (chi : Character q) (alpha : ℝ)
    {y a : ℝ} (hy : 0 ≤ y) (ha : 0 < a) :
    (count chi alpha y : ℝ) ≤ sharpenedBound chi y a := by
  apply le_min (count_le_characterBound chi alpha hy)
  split_ifs with h
  · subst chi
    exact count_principal_smoothed q alpha hy ha
  · exact count_conductor_smoothed h alpha hy ha

theorem sharpenedBound_nonneg {q : ℕ} [NeZero q] (chi : Character q)
    {y a : ℝ} (hy : 0 ≤ y) (ha : 0 < a) : 0 ≤ sharpenedBound chi y a :=
  (Nat.cast_nonneg (count chi 0 y)).trans (count_le_sharpenedBound chi 0 hy ha)

theorem familyCount_le_sharpened (q : ℕ) [NeZero q] (alpha : ℝ)
    {y a : ℝ} (hy : 0 ≤ y) (ha : 0 < a) :
    (familyCount q alpha y : ℝ) ≤ ∑ chi : Character q, sharpenedBound chi y a := by
  unfold familyCount
  rw [Nat.cast_sum]
  exact Finset.sum_le_sum (fun chi _ => count_le_sharpenedBound chi alpha hy ha)

theorem sharpened_family_le_mother (q : ℕ) [NeZero q] (y a : ℝ) :
    (∑ chi : Character q, sharpenedBound chi y a) ≤ familyBound q y := by
  rw [← sum_characterBound]
  exact Finset.sum_le_sum (fun _ _ => min_le_left _ _)

end LiuWang.Proof.DirichletZeroCount
