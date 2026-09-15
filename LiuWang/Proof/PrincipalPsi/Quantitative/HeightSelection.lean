import LiuWang.Proof.PrincipalPsi.Quantitative.XiBridge
import LiuWang.Proof.LocalAnalyticBounds.HeightHelpers.SharpIntervalAvoidance
import LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate.CompensatedSum

/-! # 真实 xi 正核的局部计数、全窗计数和独立上下选高 -/

set_option autoImplicit false
noncomputable section

open Complex
open scoped BigOperators
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ChebyshevBound.HighHeight
open LiuWang.Proof.LocalAnalyticBounds

namespace LiuWang.Proof.PrincipalPsi.Quantitative

def xiWindowSet (H r : ℝ) : Set RiemannXiDivisorZeroIndex :=
  {p | |(riemannXiDivisorZeroValue p).im - H| ≤ r}

theorem xiWindowSet_finite (H r : ℝ) : (xiWindowSet H r).Finite := by
  apply (Complex.Hadamard.divisorZeroIndex₀_norm_le_finite
    (f := riemannXi) (U := Set.univ) (B := |H| + |r| + 2) (by simp)).subset
  intro p hp
  obtain ⟨hr0, hr1⟩ := riemannXiDivisorZeroValue_re_mem_Ioo p
  have htri := abs_sub_le (riemannXiDivisorZeroValue p).im H 0
  change |(riemannXiDivisorZeroValue p).im - H| ≤ r at hp
  have hi : |(riemannXiDivisorZeroValue p).im| ≤ |H| + |r| := by
    simp only [sub_zero] at htri
    linarith [le_abs_self r]
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (by
    rw [abs_of_pos hr0]
    linarith)

def xiWindow (H r : ℝ) : Finset RiemannXiDivisorZeroIndex :=
  (xiWindowSet_finite H r).toFinset

@[simp] theorem mem_xiWindow {H r : ℝ} {p : RiemannXiDivisorZeroIndex} :
    p ∈ xiWindow H r ↔ |(riemannXiDivisorZeroValue p).im - H| ≤ r := by
  simp [xiWindow, xiWindowSet]

def referenceMass (H : ℝ) : ℝ := Real.log (|H| + 2) / 2 + 22 / 3

def heightSeparationBudget (H : ℝ) : ℝ := 5 * referenceMass H + 1

theorem referenceMass_nonneg (H : ℝ) : 0 ≤ referenceMass H := by
  have h := Real.log_nonneg (show 1 ≤ |H| + 2 by linarith [abs_nonneg H])
  unfold referenceMass
  linarith

theorem xi_reference_kernel_sum_le (H : ℝ) :
    (∑' p, xiTerm (referencePoint H) p).re ≤ referenceMass H := by
  have he := Robin1984.neg_riemannZeta_logDeriv_eq_xiDivisor_tsum
    (s := referencePoint H) (by norm_num [referencePoint])
  have hl : ‖-deriv riemannZeta (referencePoint H) / riemannZeta (referencePoint H)‖ ≤ 6 := by
    have h := norm_neg_logDeriv_LFunction_le_zeta_re
      (1 : DirichletCharacter ℂ 1) (s := referencePoint H) (by norm_num [referencePoint])
    rw [DirichletCharacter.LFunction_modOne_eq] at h
    exact h.trans (by simpa [referencePoint] using norm_neg_logDeriv_zeta_two_le_six)
  have hp : (1 / (referencePoint H - 1)).re ≤ 1 := by
    have hn : 1 ≤ ‖referencePoint H - 1‖ := by
      exact le_trans (by norm_num [referencePoint]) (Complex.re_le_norm _)
    apply (Complex.re_le_norm _).trans
    simpa only [one_div, norm_inv] using inv_le_one_of_one_le₀ hn
  have hreal : -6 ≤ (-deriv riemannZeta (referencePoint H) / riemannZeta (referencePoint H)).re := by
    have h := Complex.abs_re_le_norm
      (-deriv riemannZeta (referencePoint H) / riemannZeta (referencePoint H))
    exact (abs_le.mp (h.trans hl)).1
  have ha := archimedean_re_le (s := referencePoint H)
    (by norm_num [referencePoint]) (by norm_num [referencePoint])
  have heR := congrArg Complex.re he
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re] at heR
  norm_num only [Complex.mul_re, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_div, zero_mul, sub_zero] at heR
  simp only [one_div_mul_eq_div] at heR
  rw [show (referencePoint H).im = H by simp [referencePoint]] at ha
  change (∑' p, xiTerm (referencePoint H) p).re ≤ _
  unfold referenceMass
  change _ = -(logDeriv riemannXi 0).re - (∑' p, xiTerm (referencePoint H) p).re +
    _ - _ + _ at heR
  linarith

theorem local_kernel_lower {H : ℝ} {p : RiemannXiDivisorZeroIndex}
    (hp : p ∈ xiWindow H 1) :
    (1 / 5 : ℝ) ≤ (xiTerm (referencePoint H) p).re := by
  obtain ⟨hb0, hb1⟩ := riemannXiDivisorZeroValue_re_mem_Ioo p
  have ht := mem_xiWindow.mp hp
  have ht2 : (H - (riemannXiDivisorZeroValue p).im) ^ 2 ≤ 1 := by
    have hh := (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr ht
    rw [sq_abs, one_pow] at hh
    nlinarith
  have hden : 0 < (2 - (riemannXiDivisorZeroValue p).re) ^ 2 +
      (H - (riemannXiDivisorZeroValue p).im) ^ 2 := by nlinarith [sq_nonneg (H - (riemannXiDivisorZeroValue p).im)]
  have hk : (1 / 5 : ℝ) ≤ (1 / (referencePoint H - riemannXiDivisorZeroValue p)).re := by
    simp only [one_div, Complex.inv_re, Complex.normSq_apply, referencePoint,
      Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
    norm_num
    simp only [← pow_two]
    apply (le_div_iff₀ hden).mpr
    nlinarith [sq_nonneg (1 - (riemannXiDivisorZeroValue p).re)]
  have hn : 0 ≤ (1 / riemannXiDivisorZeroValue p).re := by
    rw [one_div, Complex.inv_re]
    exact div_nonneg hb0.le (Complex.normSq_nonneg _)
  exact hk.trans (by simpa only [xiTerm, Complex.add_re] using
    le_add_of_nonneg_right hn)

theorem xiWindow_local_card_le (H : ℝ) :
    ((xiWindow H 1).card : ℝ) ≤ 5 * referenceMass H := by
  have hs := Complex.reCLM.summable (xiTerm_summable
    (s := referencePoint H) (by norm_num [referencePoint]))
  have hsum : ((xiWindow H 1).card : ℝ) / 5 ≤
      (∑' p, xiTerm (referencePoint H) p).re := by
    rw [Complex.re_tsum (xiTerm_summable (by norm_num [referencePoint]))]
    calc
      _ = ∑ _p ∈ xiWindow H 1, (1 / 5 : ℝ) := by simp; ring
      _ ≤ ∑ p ∈ xiWindow H 1, (xiTerm (referencePoint H) p).re :=
        Finset.sum_le_sum (fun _ hp => local_kernel_lower hp)
      _ ≤ _ := hs.sum_le_tsum _ (fun p _ => xiTerm_re_nonneg
        (by norm_num [referencePoint]) p)
  linarith [xi_reference_kernel_sum_le H]

theorem xiWindow_total_card_le {T : ℝ} (hT : 0 ≤ T) :
    ((xiWindow 0 T).card : ℝ) ≤ (2 / 3) * T ^ 2 := by
  have hsum : ((xiWindow 0 T).card : ℝ) ≤
      T ^ 2 * ∑' p : RiemannXiDivisorZeroIndex, 1 / (riemannXiDivisorZeroValue p).im ^ 2 := by
    rw [← tsum_mul_left]
    calc
      _ = ∑ _p ∈ xiWindow 0 T, (1 : ℝ) := by simp
      _ ≤ ∑ p ∈ xiWindow 0 T, T ^ 2 * (1 / (riemannXiDivisorZeroValue p).im ^ 2) := by
        apply Finset.sum_le_sum
        intro p hp
        have hh := xi_zero_height_gt_one p
        have him : |(riemannXiDivisorZeroValue p).im| ≤ T := by simpa using mem_xiWindow.mp hp
        have hsq : (riemannXiDivisorZeroValue p).im ^ 2 ≤ T ^ 2 := by
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hT).mpr him
        have hpos : 0 < (riemannXiDivisorZeroValue p).im ^ 2 := by
          nlinarith [sq_abs (riemannXiDivisorZeroValue p).im]
        rw [mul_one_div, le_div_iff₀ hpos, one_mul]
        exact hsq
      _ ≤ _ := (xi_height_inverse_square_summable.mul_left (T ^ 2)).sum_le_tsum _
        (fun _ _ => by positivity)
  exact hsum.trans ((mul_le_mul_of_nonneg_left xi_height_inverse_square_sum_le
    (sq_nonneg T)).trans_eq (by ring))

theorem exists_xi_separated_height (T : ℝ) :
    ∃ H : ℝ, |H - T| ≤ 1 ∧
      ∀ p : RiemannXiDivisorZeroIndex,
        (heightSeparationBudget T)⁻¹ ≤ |(riemannXiDivisorZeroValue p).im - H| := by
  classical
  let S := (xiWindow T 1).image (fun p => (riemannXiDivisorZeroValue p).im)
  have hc : (S.card : ℝ) ≤ 5 * referenceMass T :=
    (Nat.cast_le.mpr Finset.card_image_le).trans (xiWindow_local_card_le T)
  have hr : (heightSeparationBudget T)⁻¹ ≤ 1 / ((S.card : ℝ) + 1) := by
    rw [← one_div]
    exact one_div_le_one_div_of_le (by positivity) (by unfold heightSeparationBudget; linarith)
  obtain ⟨H, hH, hsep⟩ := exists_sharp_interval_away_from_finset S T
  refine ⟨H, by linarith [show 0 ≤ 1 / ((S.card : ℝ) + 1) by positivity], fun p => ?_⟩
  by_cases hp : p ∈ xiWindow T 1
  · exact hr.trans (hsep _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩))
  · have hout : 1 < |(riemannXiDivisorZeroValue p).im - T| :=
      lt_of_not_ge (fun h => hp (mem_xiWindow.mpr h))
    have htri := abs_sub_le (riemannXiDivisorZeroValue p).im H T
    linarith

theorem heightSeparationBudget_pos (T : ℝ) : 0 < heightSeparationBudget T := by
  unfold heightSeparationBudget
  linarith [referenceMass_nonneg T]

theorem exists_xi_rectangle_heights (T : ℝ) :
    ∃ Hp Hm : ℝ, |Hp - T| ≤ 1 ∧ |Hm + T| ≤ 1 ∧
      ∀ p : RiemannXiDivisorZeroIndex,
        (heightSeparationBudget T)⁻¹ ≤ |(riemannXiDivisorZeroValue p).im - Hp| ∧
        (heightSeparationBudget T)⁻¹ ≤ |(riemannXiDivisorZeroValue p).im - Hm| := by
  obtain ⟨Hp, hp, hsp⟩ := exists_xi_separated_height T
  obtain ⟨Hm, hm, hsm⟩ := exists_xi_separated_height (-T)
  exact ⟨Hp, Hm, hp, by simpa using hm, fun p =>
    ⟨hsp p, by simpa [heightSeparationBudget, referenceMass] using hsm p⟩⟩

end LiuWang.Proof.PrincipalPsi.Quantitative
