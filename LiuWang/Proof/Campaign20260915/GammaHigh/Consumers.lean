import LiuWang.Proof.Campaign20260915.GammaHigh.Bound
import LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1.PrincipalIdentity
import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountCap.Counts

set_option autoImplicit false
noncomputable section

open Complex
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.MultiZeroRepulsion

namespace LiuWang.Proof.Campaign20260915.GammaHigh

theorem gammaTerm_two_eq (sigma t : ℝ) :
    gammaTerm 2 sigma t = gammaHalfDifference sigma t := by
  have he (u : ℝ) : ((u : ℂ) + I * t + 2) / 2 = ((u : ℂ) + I * t) / 2 + 1 := by
    ring
  simp only [gammaTerm, gammaHalfDifference, Complex.ofReal_ofNat, he]

theorem gammaHalfDifference_high {sigma t : ℝ}
    (hs : sigma ∈ Set.Ioo (1 : ℝ) 1.15) (ht : 1 ≤ |t|) :
    gammaHalfDifference sigma t <
      stechkinConductorCoeff * Real.log |t| + 0.3316 :=
  shifted_digamma_high hs ht

theorem gammaTerm_two_high {sigma t : ℝ}
    (hs : sigma ∈ Set.Ioo (1 : ℝ) 1.15) (ht : 1 ≤ |t|) :
    gammaTerm 2 sigma t < kappa * Real.log |t| + 0.3316 := by
  rw [gammaTerm_two_eq, kappa_eq]
  exact gammaHalfDifference_high hs ht

theorem source_gammaHalfDifference_high {x : ℝ} (hx : 8000000000 ≤ x) :
    ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316 := by
  intro t ht
  have hs := lwd_source_parameters hx
  exact gammaHalfDifference_high ⟨hs.2.2.1, by linarith [hs.2.2.2]⟩ ht

theorem l24_high {q : ℕ} [NeZero q] {sigma t : ℝ}
    (hs : sigma ∈ Set.Ioo (1 : ℝ) 1.15) (ht : 1 ≤ |t|) :
    f (1 : DirichletCharacter ℂ q) sigma t <
      kappa * Real.log |t| - kappa * Real.log Real.pi +
        0.3316 + s q sigma - zetaZeroSum sigma t :=
  l24_high_of_gamma_estimate hs ht (gammaTerm_two_high hs ht)

theorem original_T1_strict_family_le_four {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2)
    (hgammaLow : ∀ t : ℝ, |t| < 1 → gammaHalfDifference (lwdSourceSigma x) t < 0.0615) :
    strictFamilyCount q (1 - 0.26213 / Real.log x) (x / q) ≤ 4 :=
  CountCap.original_T1_strict_family_le_four hx hq hRS
    (source_gammaHalfDifference_high hx) hgammaLow

theorem original_T1_closed_family_le_four {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2)
    (hgammaLow : ∀ t : ℝ, |t| < 1 → gammaHalfDifference (lwdSourceSigma x) t < 0.0615) :
    familyCount q (1 - 0.26213 / Real.log x) (x / q) ≤ 4 :=
  CountCap.closed_family_le_four hx hq hRS (source_gammaHalfDifference_high hx) hgammaLow

#print axioms gammaTerm_two_high
#print axioms source_gammaHalfDifference_high
#print axioms l24_high
#print axioms original_T1_strict_family_le_four
#print axioms original_T1_closed_family_le_four

end LiuWang.Proof.Campaign20260915.GammaHigh
