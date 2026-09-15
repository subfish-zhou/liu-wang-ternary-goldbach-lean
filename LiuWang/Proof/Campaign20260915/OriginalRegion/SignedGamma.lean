import LiuWang.Proof.Campaign20260915.OriginalRegion.SignedCosts
import LiuWang.Proof.Campaign20260915.Parent.GammaConsumers

/-! Parent-accepted Gamma estimates, retaining signed Euler and pole corrections. -/

set_option autoImplicit false
noncomputable section

open Complex
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.OriginalRegion

theorem signed_principal_low {q : ℕ} [NeZero q] {sigma t : ℝ}
    (hs : sigma ∈ Set.Ioo (1 : ℝ) 1.15) (ht : |t| < 1) :
    signedCost (1 : DirichletCharacter ℂ q) sigma t <
      poleDifference sigma t - kappa * Real.log Real.pi + 0.0615 -
        principalEulerDifference q sigma t := by
  have hg := GammaLow.gammaHalfDifference_low hs ht
  rw [GammaLow.gammaHalfDifference_eq_gammaTerm] at hg
  simp only [signedCost, ite_true]
  linarith

theorem signed_principal_high {q : ℕ} [NeZero q] {sigma t : ℝ}
    (hs : sigma ∈ Set.Ioo (1 : ℝ) 1.15) (ht : 1 ≤ |t|) :
    signedCost (1 : DirichletCharacter ℂ q) sigma t <
      poleDifference sigma t + kappa * Real.log |t| - kappa * Real.log Real.pi +
        0.3316 - principalEulerDifference q sigma t := by
  have hg := GammaHigh.gammaTerm_two_high hs ht
  simp only [signedCost, ite_true]
  linarith

theorem signed_principal_real_strict {q : ℕ} [NeZero q] {sigma : ℝ}
    (hs : sigma ∈ Set.Ioo (1 : ℝ) 1.15) :
    signedCost (1 : DirichletCharacter ℂ q) sigma 0 <
      1 / (sigma - 1) - stechkinK / (stechkinSigma sigma - 1) -
        kappa * Real.log Real.pi + 0.0615 - principalPrimeCost q sigma := by
  have hh := signed_principal_low (q := q) hs (t := 0) (by norm_num)
  have he : principalEulerDifference q sigma 0 = principalPrimeCost q sigma := by
    simpa only [principalEulerDifference, ofReal_zero, mul_zero, add_zero,
      sub_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] using
      principal_real_correction_eq q sigma hs.1
  rw [he] at hh
  simpa only [poleDifference, ofReal_zero, mul_zero, add_zero,
    ← ofReal_one, ← ofReal_sub, ← ofReal_div, ofReal_re, mul_one_div] using hh

end LiuWang.Proof.Campaign20260915.OriginalRegion
