import LiuWang.Proof.NonSymmetricContour.Kernel

/-! # 原被积函数自身在原点的实际留数 -/

set_option autoImplicit false
noncomputable section

open Filter Topology
open LiuWang.Proof.Interfaces
open LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.NonSymmetricContour

theorem residue_horizontalIntegrand_zero {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {t : Real} (ht : 0 < t) :
    residue (horizontalIntegrand chi t) 0 =
      -(lFunctionOriginMultiplicity chi : Complex) * (Real.log (t / 2.5) : Complex) := by
  rw [← residue_analyticIntegrand_zero hchi ht]
  unfold residue Filter.limUnder
  congr 1
  apply Filter.map_congr
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : s ≠ (0 : Complex) := hs
  rw [analyticIntegrand_eq chi t hs0]

end LiuWang.Proof.NonSymmetricContour
