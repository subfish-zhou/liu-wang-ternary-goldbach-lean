import LiuWang.Proof.WeightedHighZeros.Continuation.Consumer

/-!
# Removing the auxiliary strict-alpha filter from the source integral

The possible discrepancy at `alpha = 19/20` is outside the interval integral's
`Ioc` support. Every height boundary and the ordinary-L multiplicity remain
literal; the resulting density integral is still unpaid.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.WeightedHighZeros.Continuation

def sourceMass (N q : ℕ) [NeZero q] (alpha : ℝ) : ℝ :=
  ∑ chi : Character q, ∑ rho ∈ bandValues chi alpha (omegaCutoff N q) (sourceT N),
    (analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im|

theorem source_integrands_ae (N q : ℕ) [NeZero q] :
    (fun alpha => layerKernel N alpha * rightMass N q alpha) =ᵐ[
      volume.restrict (Set.uIoc (19 / 20 : ℝ) 1)]
      (fun alpha => layerKernel N alpha * sourceMass N q alpha) := by
  apply ae_restrict_of_forall_mem measurableSet_uIoc
  intro alpha ha
  rw [Set.uIoc_of_le (by norm_num : (19 / 20 : ℝ) ≤ 1)] at ha
  change layerKernel N alpha * rightMass N q alpha =
    layerKernel N alpha * sourceMass N q alpha
  rw [rightMass_eq_source_band ha.1]
  rfl

theorem source_integrand_integrable {N q : ℕ} [NeZero q] (hN : 0 < N) :
    IntervalIntegrable (fun alpha => layerKernel N alpha * sourceMass N q alpha)
      volume (19 / 20) 1 :=
  (layer_integrand_integrable hN).congr_ae (source_integrands_ae N q)

theorem excessHighSum_eq_source_integral {N q : ℕ} [NeZero q] (hN : 0 < N) :
    excessHighSum N q =
      ∫ alpha in (19 / 20 : ℝ)..1,
        (N : ℝ) ^ (alpha - 1) * sourceL N * sourceMass N q alpha := by
  rw [excessHighSum_eq_integral hN]
  exact intervalIntegral.integral_congr_ae_restrict (source_integrands_ae N q)

theorem original_source_integral_reduction {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    highSum N q ≤ Real.exp (-75) * q / sourceL N ^ (4 : ℕ) +
      ∫ alpha in (19 / 20 : ℝ)..1,
        (N : ℝ) ^ (alpha - 1) * sourceL N *
          (∑ chi : Character q,
            ∑ rho ∈ bandValues chi alpha (omegaCutoff N q) (sourceT N),
              (analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im|) := by
  change _ ≤ _ + ∫ alpha in (19 / 20 : ℝ)..1,
    (N : ℝ) ^ (alpha - 1) * sourceL N * sourceMass N q alpha
  rw [← excessHighSum_eq_source_integral (Parameters.nat_pos_of_exp_le hN)]
  exact original_threshold_reduction hN hq

theorem actual_highPacket_source_integral_reduction {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (ha : Nat.Coprime a q) {eta : ℝ} (heta : |eta| ≤ deltaRadius N q) :
    ‖highPacket N q a eta‖ ≤ (5 * (N : ℝ) * Real.sqrt q / q.totient) *
      (Real.exp (-75) * q / sourceL N ^ (4 : ℕ) +
        ∫ alpha in (19 / 20 : ℝ)..1,
          (N : ℝ) ^ (alpha - 1) * sourceL N * sourceMass N q alpha) := by
  apply (highPacket_le_weighted hN ha heta).trans
  exact mul_le_mul_of_nonneg_left (original_source_integral_reduction hN hq) (by positivity)

end LiuWang.Proof.WeightedHighZeros.Continuation
