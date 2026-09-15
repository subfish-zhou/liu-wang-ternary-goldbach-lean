import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.CellCertificate

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281

theorem cell_zero_bound : fixedCellUpper 0 ≤ (1 : ℝ) / 10 ^ (16 : ℕ) := by
  norm_num [fixedCellUpper, cellUpper, fixedPoint, fixedMidpoint,
    FixedIntegral.phaseSlope, FixedIntegral.phaseIntercept,
    primitiveAmplitude, primitiveCoefficient, expLower, expUpper, expBaseLower, expBaseUpper,
    roundDown, roundUp, expSeries, expError, Finset.sum_range_succ]

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281
