import LiuWang.Proof.Campaign20260915.OriginalRegion.SelectedKernels
import LiuWang.Proof.Campaign20260915.OriginalRegion.SignedGamma

/-! Full-character signed envelopes using only previously proved Gamma estimates. -/

set_option autoImplicit false
noncomputable section

open Complex
open scoped Classical
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1
open LiuWang.Proof.MultiZeroRepulsion

namespace LiuWang.Proof.Campaign20260915.OriginalRegion

def signedEnvelope {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (sigma t : ℝ) : ℝ :=
  if chi = 1 then
    poleDifference sigma t - kappa * Real.log Real.pi +
      (if |t| < 1 then 0.0615 else kappa * Real.log |t| + 0.3316) -
      principalEulerDifference q sigma t
  else
    kappa * (Real.log ((chi.conductor : ℝ) / Real.pi) +
      Real.log (max 1 |t|)) + 5 / 16 - 5 * stechkinK / 48 -
      levelEulerDifference chi sigma t

theorem signed_nonprincipal_envelope {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1)
    {sigma : ℝ} (hs : sigma ∈ Set.Ioo (1 : ℝ) 1.15) (t : ℝ) :
    signedCost chi sigma t ≤ signedEnvelope chi sigma t := by
  have hg := gammaDifference_le chi.primitiveCharacter hs.1 (by linarith [hs.2]) t
  rw [gammaDifference_eq chi.primitiveCharacter hs.1 t, ← kappa_eq] at hg
  simp only [signedCost, signedEnvelope, if_neg hc]
  nlinarith

theorem signed_principal_envelope_strict {q : ℕ} [NeZero q]
    {sigma : ℝ} (hs : sigma ∈ Set.Ioo (1 : ℝ) 1.15) (t : ℝ) :
    signedCost (1 : DirichletCharacter ℂ q) sigma t <
      signedEnvelope (1 : DirichletCharacter ℂ q) sigma t := by
  simp only [signedEnvelope, ite_true]
  by_cases ht : |t| < 1
  · rw [if_pos ht]
    exact signed_principal_low hs ht
  · rw [if_neg ht]
    have hh := signed_principal_high (q := q) hs (le_of_not_gt ht)
    linarith

theorem signedCost_le_envelope {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {sigma : ℝ}
    (hs : sigma ∈ Set.Ioo (1 : ℝ) 1.15) (t : ℝ) :
    signedCost chi sigma t ≤ signedEnvelope chi sigma t := by
  by_cases hc : chi = 1
  · subst chi
    exact (signed_principal_envelope_strict hs t).le
  · exact signed_nonprincipal_envelope chi hc hs t

theorem signed_quartic_envelope_strict {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {rho : ℂ}
    (hr : 1 / 2 < rho.re ∧ rho.re < 1) (hz : chi.LFunction rho = 0)
    {sigma : ℝ} (hs : sigma ∈ Set.Ioo (1 : ℝ) 1.15) :
    24480 * reflectedKernel sigma rho.im rho <
      14379 * signedEnvelope (1 : DirichletCharacter ℂ q) sigma 0 +
      24480 * signedEnvelope chi sigma rho.im +
      14900 * signedEnvelope (chi ^ 2) sigma (2 * rho.im) +
      6000 * signedEnvelope (chi ^ 3) sigma (3 * rho.im) +
      1250 * signedEnvelope (chi ^ 4) sigma (4 * rho.im) := by
  have hh := signed_quartic_selected_bound chi hr hz hs.1
  have h0 := signed_principal_envelope_strict (q := q) hs 0
  have h1 := signedCost_le_envelope chi hs rho.im
  have h2 := signedCost_le_envelope (chi ^ 2) hs (2 * rho.im)
  have h3 := signedCost_le_envelope (chi ^ 3) hs (3 * rho.im)
  have h4 := signedCost_le_envelope (chi ^ 4) hs (4 * rho.im)
  linarith

end LiuWang.Proof.Campaign20260915.OriginalRegion
