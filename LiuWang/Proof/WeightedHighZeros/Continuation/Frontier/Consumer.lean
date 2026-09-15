import LiuWang.Proof.WeightedHighZeros.Continuation.Frontier.Payment

/-! # Original-height consumers after the certified `49/50` payment -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.WeightedHighZeros.Continuation.Frontier

theorem middle_integrable {N q : ℕ} [NeZero q] (hN : 0 < N) :
    IntervalIntegrable (fun alpha => layerKernel N alpha * sourceMass N q alpha)
      volume (19 / 20) (49 / 50) := by
  apply (source_integrand_integrable hN).mono_set
  simp only [Set.uIcc_of_le (by norm_num : (19 / 20 : ℝ) ≤ 49 / 50),
    Set.uIcc_of_le (by norm_num : (19 / 20 : ℝ) ≤ 1)]
  exact Set.Icc_subset_Icc le_rfl (by norm_num)

theorem frontier_integrable {N q : ℕ} [NeZero q] (hN : 0 < N) :
    IntervalIntegrable (fun alpha => layerKernel N alpha * sourceMass N q alpha)
      volume (49 / 50) 1 := by
  apply (source_integrand_integrable hN).mono_set
  simp only [Set.uIcc_of_le (by norm_num : (49 / 50 : ℝ) ≤ 1),
    Set.uIcc_of_le (by norm_num : (19 / 20 : ℝ) ≤ 1)]
  exact Set.Icc_subset_Icc (by norm_num) le_rfl

theorem highSum_eq_frontierCap_add_integral {N q : ℕ} [NeZero q] (hN : 1 ≤ N) :
    highSum N q = frontierCap N q +
      ∫ alpha in (49 / 50 : ℝ)..1, layerKernel N alpha * sourceMass N q alpha := by
  rw [highSum_eq_capped_add_excess hN, excessHighSum_eq_source_integral hN,
    frontierCap_eq_old_cap_add_middle hN]
  rw [add_assoc, intervalIntegral.integral_add_adjacent_intervals
    (middle_integrable hN) (frontier_integrable hN)]
  rfl

theorem original_frontier_reduction {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    highSum N q ≤ (1 / 10000 : ℝ) * q / sourceL N ^ (4 : ℕ) +
      ∫ alpha in (49 / 50 : ℝ)..1,
        (N : ℝ) ^ (alpha - 1) * sourceL N * sourceMass N q alpha := by
  rw [highSum_eq_frontierCap_add_integral (Parameters.nat_pos_of_exp_le hN)]
  exact add_le_add (frontierCap_paid hN hq) le_rfl

theorem actual_left_real_part_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (∑ chi : Character q,
      ∑ rho ∈ (highValues N chi).filter (fun rho => rho.re ≤ 49 / 50),
        (analyticOrderNatAt chi.LFunction rho : ℝ) *
          ((N : ℝ) ^ (rho.re - 1) / |rho.im|)) ≤
            (1 / 10000 : ℝ) * q / sourceL N ^ (4 : ℕ) := by
  have hn : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr (Parameters.nat_pos_of_exp_le hN)
  apply le_trans _ (frontierCap_paid hN hq)
  apply Finset.sum_le_sum
  intro chi _
  calc
    _ = ∑ rho ∈ (highValues N chi).filter (fun rho => rho.re ≤ 49 / 50),
        (analyticOrderNatAt chi.LFunction rho : ℝ) *
          (min ((N : ℝ) ^ (rho.re - 1)) ((N : ℝ) ^ (-1 / 50 : ℝ)) / |rho.im|) := by
      apply Finset.sum_congr rfl
      intro rho hrho
      have hh : (N : ℝ) ^ (rho.re - 1) ≤ (N : ℝ) ^ (-1 / 50 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hn (by linarith [(Finset.mem_filter.mp hrho).2])
      rw [min_eq_left hh]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun rho _ _ => by positivity)

theorem actual_complete_frontier_reduction {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (∑ chi : Character q,
      ∑ rho ∈ (CompleteExpansion.zeroValues chi (sourceT N)).filter
        (fun rho => omegaCutoff N q ≤ |rho.im|),
          (analyticOrderNatAt chi.LFunction rho : ℝ) *
            ((N : ℝ) ^ (rho.re - 1) / |rho.im|)) ≤
      (1 / 10000 : ℝ) * q / sourceL N ^ (4 : ℕ) +
        ∫ alpha in (49 / 50 : ℝ)..1, layerKernel N alpha * sourceMass N q alpha := by
  simpa only [highSum, bandSum, bandValues, Applications.half_values_eq_complete, layerKernel] using
    original_frontier_reduction hN hq

theorem actual_primed_frontier_reduction {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {exceptional : Option ℂ} (he : ∀ beta, exceptional = some beta → beta.im = 0) :
    primedHighSum N q exceptional ≤
      (1 / 10000 : ℝ) * q / sourceL N ^ (4 : ℕ) +
        ∫ alpha in (49 / 50 : ℝ)..1, layerKernel N alpha * sourceMass N q alpha := by
  rw [primedHighSum_eq_highSum hN he]
  exact original_frontier_reduction hN hq

theorem actual_highPacket_frontier_reduction {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (ha : Nat.Coprime a q) {eta : ℝ} (heta : |eta| ≤ deltaRadius N q) :
    ‖highPacket N q a eta‖ ≤ (5 * (N : ℝ) * Real.sqrt q / q.totient) *
      ((1 / 10000 : ℝ) * q / sourceL N ^ (4 : ℕ) +
        ∫ alpha in (49 / 50 : ℝ)..1, layerKernel N alpha * sourceMass N q alpha) :=
  (highPacket_le_weighted hN ha heta).trans
    (mul_le_mul_of_nonneg_left (original_frontier_reduction hN hq) (by positivity))

end LiuWang.Proof.WeightedHighZeros.Continuation.Frontier
