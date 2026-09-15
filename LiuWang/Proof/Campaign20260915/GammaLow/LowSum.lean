import LiuWang.Proof.Campaign20260915.GammaLow.Principal
import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases.Kernels

set_option autoImplicit false

noncomputable section

open Complex
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases

namespace LiuWang.Proof.Campaign20260915.GammaLow

theorem gammaHalfDifference_eq_gammaTerm (sigma t : ℝ) :
    gammaHalfDifference sigma t = gammaTerm 2 sigma t := by
  have hcast (u : ℝ) :
      ((u : ℂ) + I * t + 2) / 2 = ((u : ℂ) + I * t) / 2 + 1 := by ring
  simp only [gammaHalfDifference, gammaTerm, Complex.ofReal_ofNat, hcast]

theorem gammaHalfDifference_low {sigma t : ℝ}
    (hs : sigma ∈ Set.Ioo (1 : ℝ) 1.15) (ht : |t| < 1) :
    gammaHalfDifference sigma t < 0.0615 := by
  rw [gammaHalfDifference_eq_gammaTerm]
  exact gammaTerm_two_low hs ht

theorem source_gamma_low {x : ℝ} (hx : 8000000000 ≤ x) :
    ∀ t : ℝ, |t| < 1 → gammaHalfDifference (lwdSourceSigma x) t < 0.0615 := by
  have hs := (lwd_source_parameters hx).2.2
  intro t ht
  exact gammaHalfDifference_low ⟨hs.1, by linarith [hs.2]⟩ ht

#print axioms gammaHalfDifference_low
#print axioms source_gamma_low

end LiuWang.Proof.Campaign20260915.GammaLow
