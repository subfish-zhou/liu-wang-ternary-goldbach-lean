import LiuWang.Proof.Campaign20260915.GammaLow.Bound
import LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1.PrincipalIdentity

set_option autoImplicit false

noncomputable section

open Complex
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.GammaLow

theorem gammaTerm_two_low {sigma t : ℝ}
    (hs : sigma ∈ Set.Ioo (1 : ℝ) 1.15) (ht : |t| < 1) :
    gammaTerm 2 sigma t < 0.0615 := by
  have hcast (u : ℝ) :
      ((u : ℂ) + I * t + 2) / 2 = ((u : ℂ) + I * t) / 2 + 1 := by ring
  simpa only [gammaTerm, Complex.ofReal_ofNat, hcast] using
    shifted_digamma_low_strict hs ht

theorem l24_low {q : ℕ} [NeZero q] {sigma t : ℝ}
    (hs : sigma ∈ Set.Ioo (1 : ℝ) 1.15) (ht : |t| < 1) :
    f (1 : DirichletCharacter ℂ q) sigma t <
      (1 / ((sigma : ℂ) - 1 + I * t)).re - kappa * Real.log Real.pi +
        0.0615 + s q sigma - zetaZeroSum sigma t :=
  l24_low_of_gamma_estimate hs ht (fun _ hu => gammaTerm_two_low hs hu)

#print axioms gammaTerm_two_low
#print axioms l24_low

end LiuWang.Proof.Campaign20260915.GammaLow
