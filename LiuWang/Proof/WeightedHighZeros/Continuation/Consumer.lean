import LiuWang.Proof.WeightedHighZeros.Continuation.LayerCake
import LiuWang.Proof.WeightedHighZeros.Packet

/-!
# Original-threshold consumers with the unpaid density edge exposed

The paid term is exponentially smaller than the original coefficient.
The remaining finite high-alpha integral is displayed, never assumed bounded.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.WeightedHighZeros.Continuation

theorem actual_left_real_part_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (∑ chi : Character q,
      ∑ rho ∈ (highValues N chi).filter (fun rho => rho.re ≤ 19 / 20),
        (analyticOrderNatAt chi.LFunction rho : ℝ) *
          ((N : ℝ) ^ (rho.re - 1) / |rho.im|)) ≤
            Real.exp (-75) * q / sourceL N ^ (4 : ℕ) := by
  have hn : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr (Parameters.nat_pos_of_exp_le hN)
  apply le_trans _ (cappedHighSum_le_original_threshold hN hq)
  apply Finset.sum_le_sum
  intro chi _
  calc
    _ = ∑ rho ∈ (highValues N chi).filter (fun rho => rho.re ≤ 19 / 20),
        (analyticOrderNatAt chi.LFunction rho : ℝ) * (capWeight N rho / |rho.im|) := by
      apply Finset.sum_congr rfl
      intro rho hrho
      have hh : (N : ℝ) ^ (rho.re - 1) ≤ (N : ℝ) ^ (-1 / 20 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hn (by linarith [(Finset.mem_filter.mp hrho).2])
      rw [capWeight, min_eq_left hh]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun rho _ _ => by unfold capWeight; positivity)

theorem actual_complete_values_reduction {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (∑ chi : Character q,
      ∑ rho ∈ (CompleteExpansion.zeroValues chi (sourceT N)).filter
        (fun rho => omegaCutoff N q ≤ |rho.im|),
          (analyticOrderNatAt chi.LFunction rho : ℝ) *
            ((N : ℝ) ^ (rho.re - 1) / |rho.im|)) ≤
      Real.exp (-75) * q / sourceL N ^ (4 : ℕ) +
        ∫ alpha in (19 / 20 : ℝ)..1,
          (N : ℝ) ^ (alpha - 1) * sourceL N * rightMass N q alpha := by
  simpa only [highSum, bandSum, bandValues, Applications.half_values_eq_complete] using
    original_threshold_integral_reduction hN hq

theorem actual_primed_integral_reduction {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {exceptional : Option ℂ} (he : ∀ beta, exceptional = some beta → beta.im = 0) :
    primedHighSum N q exceptional ≤
      Real.exp (-75) * q / sourceL N ^ (4 : ℕ) +
        ∫ alpha in (19 / 20 : ℝ)..1,
          (N : ℝ) ^ (alpha - 1) * sourceL N * rightMass N q alpha := by
  rw [primedHighSum_eq_highSum hN he]
  exact original_threshold_integral_reduction hN hq

theorem actual_highPacket_integral_reduction {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (ha : Nat.Coprime a q) {eta : ℝ} (heta : |eta| ≤ deltaRadius N q) :
    ‖highPacket N q a eta‖ ≤ (5 * (N : ℝ) * Real.sqrt q / q.totient) *
      (Real.exp (-75) * q / sourceL N ^ (4 : ℕ) +
        ∫ alpha in (19 / 20 : ℝ)..1,
          (N : ℝ) ^ (alpha - 1) * sourceL N * rightMass N q alpha) :=
  (highPacket_le_weighted hN ha heta).trans
    (mul_le_mul_of_nonneg_left (original_threshold_integral_reduction hN hq) (by positivity))

theorem original_threshold_paid_and_unpaid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    highSum N q = cappedHighSum N q + excessHighSum N q ∧
      0 ≤ cappedHighSum N q ∧
      cappedHighSum N q ≤ Real.exp (-75) * q / sourceL N ^ (4 : ℕ) ∧
      0 ≤ excessHighSum N q ∧
      IntervalIntegrable (fun alpha => layerKernel N alpha * rightMass N q alpha)
        volume (19 / 20) 1 ∧
      excessHighSum N q = ∫ alpha in (19 / 20 : ℝ)..1,
        (N : ℝ) ^ (alpha - 1) * sourceL N * rightMass N q alpha :=
  ⟨highSum_eq_capped_add_excess (Parameters.nat_pos_of_exp_le hN),
    cappedHighSum_nonneg N q, cappedHighSum_le_original_threshold hN hq,
    excessHighSum_nonneg (Parameters.nat_pos_of_exp_le hN),
    layer_integrand_integrable (Parameters.nat_pos_of_exp_le hN),
    excessHighSum_eq_integral (Parameters.nat_pos_of_exp_le hN)⟩

end LiuWang.Proof.WeightedHighZeros.Continuation
