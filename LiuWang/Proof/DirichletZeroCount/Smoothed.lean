import LiuWang.Proof.DirichletZeroCount.SourceLow
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Global count sharpening by integration of the actual positive kernel

Finite sums, not an interchange of an unproved integral and an infinite sum,
are integrated. No horizontal logarithmic derivative crosses a zero: all
reference points have real part two. The padding `a > 0` is freely selectable.
This is still not the source's logarithmic-error Riemann--von Mangoldt bound.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.LocalAnalyticBounds
open LiuWang.Proof.PrincipalPsi.Quantitative
open LiuWang.Proof.ChebyshevBound.HighHeight
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.DirichletZeroCount

def heightKernel (rho : ℂ) (t : ℝ) : ℝ :=
  (2 - rho.re) / ((2 - rho.re) ^ 2 + (t - rho.im) ^ 2)

theorem heightKernel_eq (rho : ℂ) (t : ℝ) :
    heightKernel rho t = (1 / (referencePoint t - rho)).re := by
  simp [heightKernel, referencePoint, Complex.inv_re, Complex.normSq_apply, pow_two]

theorem heightKernel_continuous {rho : ℂ} (hr : rho.re < 1) :
    Continuous (heightKernel rho) := by
  have hd (t : ℝ) : (2 - rho.re) ^ 2 + (t - rho.im) ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (t - rho.im)]
  unfold heightKernel
  fun_prop (disch := exact hd _)

theorem integral_heightKernel (rho : ℂ) (H : ℝ) :
    (∫ t in -H..H, heightKernel rho t) =
      Real.arctan ((H - rho.im) / (2 - rho.re)) +
        Real.arctan ((H + rho.im) / (2 - rho.re)) := by
  unfold heightKernel
  rw [intervalIntegral.integral_comp_sub_right
    (fun t : ℝ => (2 - rho.re) / ((2 - rho.re) ^ 2 + t ^ 2)) rho.im,
    integral_div_sq_add_sq]
  rw [show (-H - rho.im) / (2 - rho.re) = -((H + rho.im) / (2 - rho.re)) by ring,
    Real.arctan_neg]
  ring

theorem integral_heightKernel_lower {rho : ℂ} {y a : ℝ}
    (ha : 0 < a) (hr : rho.re ∈ Set.Ioo 0 1) (ht : |rho.im| ≤ y) :
    2 * Real.arctan (a / 2) ≤ ∫ t in -(y + a)..y + a, heightKernel rho t := by
  have hu : 0 < 2 - rho.re := by linarith [hr.2]
  have hparts := abs_le.mp ht
  have h1 : a / 2 ≤ (y + a - rho.im) / (2 - rho.re) := by
    apply (le_div_iff₀ hu).mpr
    nlinarith [hr.1]
  have h2 : a / 2 ≤ (y + a + rho.im) / (2 - rho.re) := by
    apply (le_div_iff₀ hu).mpr
    nlinarith [hr.1]
  rw [integral_heightKernel]
  have h1' := Real.arctan_le_arctan_iff.mpr h1
  have h2' := Real.arctan_le_arctan_iff.mpr h2
  linarith

theorem finite_count_smoothed {ι : Type*} (S : Finset ι) (v : ι → ℂ)
    {y a B : ℝ} (hy : 0 ≤ y) (ha : 0 < a)
    (hr : ∀ p ∈ S, (v p).re ∈ Set.Ioo 0 1)
    (ht : ∀ p ∈ S, |(v p).im| ≤ y)
    (hm : ∀ t ∈ Set.Icc (-(y + a)) (y + a), ∑ p ∈ S, heightKernel (v p) t ≤ B) :
    (S.card : ℝ) ≤ (y + a) * B / Real.arctan (a / 2) := by
  have hc (p) (hp : p ∈ S) := heightKernel_continuous (hr p hp).2
  have hi (p) (hp : p ∈ S) : IntervalIntegrable (heightKernel (v p)) volume (-(y + a)) (y + a) :=
    (hc p hp).intervalIntegrable (a := -(y + a)) (b := y + a)
  have hsum : (S.card : ℝ) * (2 * Real.arctan (a / 2)) ≤
      ∫ t in -(y + a)..y + a, ∑ p ∈ S, heightKernel (v p) t := by
    rw [intervalIntegral.integral_finsetSum hi]
    calc
      _ = ∑ _p ∈ S, 2 * Real.arctan (a / 2) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun p hp => integral_heightKernel_lower ha (hr p hp) (ht p hp))
  have hupper : (∫ t in -(y + a)..y + a, ∑ p ∈ S, heightKernel (v p) t) ≤
      2 * (y + a) * B := by
    have hiSum : IntervalIntegrable (fun t => ∑ p ∈ S, heightKernel (v p) t)
        volume (-(y + a)) (y + a) := by
      convert! IntervalIntegrable.sum S hi using 1
      ext t
      simp only [Finset.sum_apply]
    have h := intervalIntegral.integral_mono_on (g := fun _ => B)
      (by linarith : -(y + a) ≤ y + a) hiSum intervalIntegrable_const hm
    simp only [intervalIntegral.integral_const, smul_eq_mul] at h
    exact h.trans_eq (by ring)
  have hatan : 0 < Real.arctan (a / 2) := Real.arctan_pos.mpr (by positivity)
  apply (le_div_iff₀ hatan).mpr
  linarith

theorem reference_mass_improved {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) (t : ℝ) :
    (∑' p : CompletedZeroIndex chi, heightKernel (completedZeroValue p) t) ≤
      Real.log q / 2 + Real.log (|t| + 2) / 2 + 2 := by
  simp only [heightKernel_eq]
  obtain ⟨B, hB, _⟩ := existsUnique_symmetricCompletedLFunction_hadamardConstant hchi hprim
  obtain ⟨Bi, hBi, _⟩ := existsUnique_symmetricCompletedLFunction_hadamardConstant
    (BombieriVinogradov.DirichletCharacter.inv_ne_one_of_ne_one hchi)
    (BombieriVinogradov.DirichletCharacter.IsPrimitive.inv hprim)
  have he := neg_re_logDeriv_LFunction_eq_modulus_gamma_sub_zeroKernel
    hchi hprim hB hBi (s := referencePoint t) (by norm_num [referencePoint])
  have hn := norm_neg_logDeriv_LFunction_le_zeta_re chi
    (s := referencePoint t) (by norm_num [referencePoint])
  have hz := norm_zeta_real_logDeriv_le_one (s := 2) le_rfl
  have hl : (logDeriv chi.LFunction (referencePoint t)).re ≤ 1 := by
    apply (Complex.re_le_norm _).trans
    apply le_trans _ hz
    simpa [logDeriv_apply, referencePoint, norm_div, norm_neg] using hn
  have hg := logDeriv_gammaFactor_re_le_on_two chi
    (s := referencePoint t) (by simp [referencePoint])
  rw [show (referencePoint t).im = t by simp [referencePoint]] at hg
  change -(logDeriv chi.LFunction (referencePoint t)).re =
    Real.log q / 2 + (logDeriv chi.gammaFactor (referencePoint t)).re -
      ∑' p : CompletedZeroIndex chi, (1 / (referencePoint t - completedZeroValue p)).re at he
  linarith

theorem count_primitive_smoothed {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) (alpha : ℝ)
    {y a : ℝ} (hy : 0 ≤ y) (ha : 0 < a) :
    (count chi alpha y : ℝ) ≤ (y + a) *
      (Real.log q / 2 + Real.log (y + a + 2) / 2 + 2) / Real.arctan (a / 2) := by
  rw [count_nonprincipal hchi]
  apply finite_count_smoothed _ completedZeroValue hy ha
  · intro p hp
    have hr := (mem_nonprincipalIndices.mp hp).1
    exact ⟨hr.1, hr.2.1⟩
  · exact fun p hp => (mem_nonprincipalIndices.mp hp).1.2.2
  · intro t ht
    have hs := summable_symmetricCompletedLFunction_zeroKernel_re hchi hprim
      (s := referencePoint t) (by norm_num [referencePoint])
    have hnonneg := symmetricCompletedLFunction_zeroKernel_re_nonneg hchi hprim
      (s := referencePoint t) (by norm_num [referencePoint])
    have hlog := Real.log_le_log (by positivity : 0 < |t| + 2)
      (show |t| + 2 ≤ y + a + 2 by linarith [(abs_le.mpr ht)])
    calc
      _ ≤ ∑' p : CompletedZeroIndex chi, heightKernel (completedZeroValue p) t := by
        simpa only [heightKernel_eq, completedZeroValue, symmetricCompletedZeroValue] using hs.sum_le_tsum
          (nonprincipalIndices chi alpha y) (fun p _ => hnonneg p)
      _ ≤ _ := (reference_mass_improved hchi hprim t).trans (by linarith)

theorem count_conductor_smoothed {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (alpha : ℝ) {y a : ℝ} (hy : 0 ≤ y) (ha : 0 < a) :
    (count chi alpha y : ℝ) ≤ (y + a) *
      (Real.log chi.conductor / 2 + Real.log (y + a + 2) / 2 + 2) /
        Real.arctan (a / 2) := by
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  rw [count_eq_primitive chi hchi]
  exact count_primitive_smoothed
    (BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hchi)
    chi.primitiveCharacter_isPrimitive alpha hy ha

end LiuWang.Proof.DirichletZeroCount
