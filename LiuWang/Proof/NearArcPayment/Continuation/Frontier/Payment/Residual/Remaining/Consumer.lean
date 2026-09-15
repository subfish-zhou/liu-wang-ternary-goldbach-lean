import LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual.Remaining.ScalarLeft

/-! 同一非实高包上比较两种已支付费用；左族标量费只收在真实大模数能量上。 -/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual.Remaining

open Interfaces Parameters ArcGeometry CompleteExpansion MajorArcApproximation MinorArcEnergy
open AnalyticNumberTheory.LargeSieve

def nearFee (N q : ℕ) : ℝ :=
  if realModulusLimit N < (q : ℝ) then
    lowKernel N q * (gaussCap q / (q.totient : ℝ) * (7 + 14000 * innerWeight N)) else 0

def alternateLayerFee (N q : ℕ) : ℝ :=
  if realModulusLimit N < (q : ℝ) then alternativePacketFee N q else 0

def nearLayerCost (N : ℕ) : ℝ :=
  ∑ i ∈ coreIndices N, nearFee N i.1 * shellEnergy N i.2 i.1

theorem norm_selectedRest_le_alternate_high {N a q : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hq : (q : ℝ) ≤ sourceP N) (hi : sourceIndex a q) {eta : ℝ}
    (he : deltaRadius N q < |eta|) :
    ‖selectedRest N a q eta‖ ≤ alternateLayerFee N q + ‖selectedHigh N a q eta‖ := by
  let : NeZero q := ⟨Nat.ne_of_gt (sourceIndex_den_pos hi)⟩
  have hh (positive : Bool) :
      ‖restPart N a q positive eta‖ ≤ alternateLayerFee N q + ‖highPart N a q positive eta‖ := by
    rw [restPart_eq, highPart_eq, restPacket_eq_largeLow_add_high]
    unfold alternateLayerFee
    by_cases hlarge : realModulusLimit N < (q : ℝ)
    · rw [if_pos hlarge]
      exact (norm_add_le _ _).trans
        (add_le_add (norm_largeLowPacket_alternative hN hq hi positive he) le_rfl)
    · rw [if_neg hlarge]
      have hz : realPacketOn q a (fun chi => largeLowValues chi N positive) N eta = 0 := by
        simp [realPacketOn, largeLow_empty hN (le_of_not_gt hlarge)]
      simp only [hz, zero_add, le_refl]
  unfold selectedRest selectedHigh
  split_ifs
  · exact hh true
  · exact hh false

theorem restShellCost_le_alternate_high {N a q : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hq : (q : ℝ) ≤ sourceP N) (hi : sourceIndex a q) :
    restShellCost N a q ≤ alternateLayerFee N q * shellEnergy N a q + highShellCost N a q := by
  have he : IntegrableOn (fun alpha : ℝ => ‖S N alpha‖ ^ 2) (shell N a q) :=
    (continuous_energy N).integrableOn_Icc.mono_set Set.sdiff_subset
  have hf := integrable_rest_weight (nat_pos_of_exp_le hN) a q
  have hg := integrable_high_weight (nat_pos_of_exp_le hN) a q
  unfold restShellCost highShellCost shellEnergy
  calc
    _ ≤ ∫ alpha in shell N a q, alternateLayerFee N q * ‖S N alpha‖ ^ 2 +
        ‖selectedHigh N a q (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2 := by
      apply setIntegral_mono_on hf ((he.const_mul _).add hg) (measurableSet_shell N a q)
      intro alpha ha
      simpa only [add_mul, Pi.add_apply] using mul_le_mul_of_nonneg_right
        (norm_selectedRest_le_alternate_high hN hq hi (shell_same_eta hq hi ha).1)
        (sq_nonneg ‖S N alpha‖)
    _ = _ := by rw [integral_add (he.const_mul _) hg, integral_const_mul]

theorem alternate_cost_eq (N : ℕ) :
    (∑ i ∈ coreIndices N, alternateLayerFee N i.1 * shellEnergy N i.2 i.1) =
      nearLayerCost N + leftScalarFee N * largeEnergy N := by
  unfold nearLayerCost largeEnergy
  rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold alternateLayerFee nearFee alternativePacketFee
  by_cases hh : realModulusLimit N < (i.1 : ℝ) <;> simp only [hh, if_true, if_false] <;> ring

theorem restCost_le_near_scalar_high {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    restCost N ≤ nearLayerCost N + leftScalarFee N * largeEnergy N + highCost N := by
  rw [← alternate_cost_eq]
  unfold restCost highCost
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hh := (mem_coreIndices (exp_2000_le_of_exp_3100_le hN) i).mp hi
  exact restShellCost_le_alternate_high hN hh.1 hh.2

theorem restCost_le_near_069_high {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    restCost N ≤ nearLayerCost N +
      (0.069 * (N : ℝ) / sourceL N) * largeEnergy N + highCost N := by
  have he : 0 ≤ largeEnergy N :=
    Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  exact (restCost_le_near_scalar_high hN).trans (add_le_add
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right (leftScalarFee_le_069 hN) he)) le_rfl)

def paidCost (N : ℕ) : ℝ :=
  min (layerCost N) (nearLayerCost N + leftScalarFee N * largeEnergy N)

theorem restCost_le_paid_high {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    restCost N ≤ paidCost N + highCost N := by
  unfold paidCost
  by_cases hh : layerCost N ≤ nearLayerCost N + leftScalarFee N * largeEnergy N
  · rw [min_eq_left hh]
    exact restCost_le_layer_high hN
  · rw [min_eq_right (le_of_not_ge hh)]
    exact restCost_le_near_scalar_high hN

theorem M2_integral_le_mothers_paid_high {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
      fullFee N * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) + paidCost N + highCost N := by
  have hh := M2_integral_le_full_mothers_rest hN
  have hc := restCost_le_paid_high hN
  linarith only [hh, hc]

theorem C_le_mothers_paid_high {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    weightedPacketCost N ≤
      (0.0005 * (N : ℝ) / sourceL N + frontierFee N + lowFee N) *
        (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) + paidCost N + highCost N := by
  have hh := C_le_full_mothers_rest hN
  have hc := restCost_le_paid_high hN
  linarith only [hh, hc]

theorem lambdaTripleCount_ge_mothers_paid_high {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∫ alpha in M1 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re +
      (∫ alpha in M3 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re +
      (∫ alpha in M4 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re -
      fullFee N * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) - paidCost N - highCost N ≤ lambdaTripleCount N := by
  have hh := lambdaTripleCount_ge_full_mothers_rest hN
  have hc := restCost_le_paid_high hN
  linarith only [hh, hc]

theorem layer_paid_same_high_comparison (N : ℕ) :
    paidCost N + highCost N ≤ layerCost N + highCost N :=
  add_le_add (min_le_left _ _) (le_rfl : highCost N ≤ highCost N)

end LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual.Remaining
