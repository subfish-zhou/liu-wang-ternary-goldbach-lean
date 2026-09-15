import LiuWang.Proof.Campaign20260915.ZetaLehmanKernel.SummedKernel
import LiuWang.Proof.Campaign20260915.ZetaWinding.ZetaLehmanIdentity

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory
open scoped ComplexConjugate

namespace LiuWang.Proof.Campaign20260915.ZetaLehmanKernel

open LiuWang.Proof.Campaign20260915.ZetaWinding
open LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.PrincipalPsi.Quantitative
open LiuWang.Proof.ChebyshevBound.HighHeight
open BombieriVinogradov.SiegelWalfisz

theorem horizontalLogMass_lehman_lower {T : ℝ} (hT : T ≠ 0) :
    -(37 / 25 : ℝ) * (logDeriv riemannXi (horizontalAt T (3 / 2))).re -
      (∫ x in (1 / 2 : ℝ)..(3 / 2), lehmanGammaLog T x) +
      (∫ x in (1 / 2 : ℝ)..(3 / 2), lehmanPoleLog T x) - Real.log Real.pi / 2 +
      (∫ x in Set.Ioi (3 / 2 : ℝ), Real.log ‖riemannZeta (horizontalAt T x)‖) +
      (∫ x in (3 / 2 : ℝ)..(5 / 2), Real.log ‖riemannZeta (horizontalAt T x)‖) ≤
        horizontalLogMass T := by
  rw [horizontalLogMass_lehman_zero_series hT]
  linarith [xi_zero_series_lehman T]

#print axioms zeroIntegral_pair_lehman
#print axioms xi_zero_series_lehman
#print axioms horizontalLogMass_lehman_lower
#print axioms xiReflection

end LiuWang.Proof.Campaign20260915.ZetaLehmanKernel
