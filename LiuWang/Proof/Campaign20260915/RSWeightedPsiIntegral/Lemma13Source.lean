import LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.OriginalZeroIntegral

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open MeasureTheory Set
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral

theorem original_weighted_error_integrable {x : ℝ} (hx : 1 < x) :
    IntegrableOn (fun y =>
      (y - Chebyshev.psi y) * (1 + Real.log y) / (y ^ 2 * Real.log y ^ 2)) (Ioi x) := by
  exact (signedPsiError_integrableOn hx).congr (Filter.Eventually.of_forall (fun y => by
    dsimp [signedPsiError, weight]
    ring))

/-- The first term of RS1962 (8.4), obtained from the actual psi integral. -/
theorem lemma13_psi_L_contribution {x : ℝ} (hx : 1 < x) :
    |Real.log x * ∫ y in Ioi x,
      (y - Chebyshev.psi y) * (1 + Real.log y) / (y ^ 2 * Real.log y ^ 2)| <
      (2 + Real.log x) / Real.log x *
        ((∑' p : RiemannXiDivisorZeroIndex,
          x ^ ((riemannXiDivisorZeroValue p).re - 1) /
            |(riemannXiDivisorZeroValue p).im ^ (1 + 1)|) +
          (184 / 100 : ℝ) / x + (31 / 100 : ℝ) / x ^ 3) := by
  rw [abs_mul, abs_of_pos (Real.log_pos hx)]
  apply (mul_lt_mul_of_pos_left (lemma8 hx) (Real.log_pos hx)).trans_eq
  field_simp

#print axioms original_weighted_error_integrable
#print axioms lemma13_psi_L_contribution

end LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral
