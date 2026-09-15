import LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual.Remaining.Packet

/-! 按真实 q,a shell 收费，不把每层能量都换成完整 E2；低高度费用不含零点求和。 -/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual.Remaining

open Interfaces Parameters ArcGeometry CompleteExpansion MajorArcApproximation MinorArcEnergy
open AnalyticNumberTheory.LargeSieve

def highPart (N a q : ℕ) (positive : Bool) (eta : ℝ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    realPacketOn q a (fun chi => highValues chi N positive) N eta

theorem highPart_eq {q : ℕ} [NeZero q] (N a : ℕ) (positive : Bool) (eta : ℝ) :
    highPart N a q positive eta = realPacketOn q a (fun chi => highValues chi N positive) N eta := by
  simp only [highPart, dif_neg (NeZero.ne q)]

def selectedHigh (N a q : ℕ) (eta : ℝ) : ℂ :=
  if 0 ≤ eta then highPart N a q true eta else highPart N a q false eta

def layerFee (N a q : ℕ) : ℝ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    if realModulusLimit N < (q : ℝ) then packetFee N a q else 0

theorem layerFee_eq {q : ℕ} [NeZero q] (N a : ℕ) :
    layerFee N a q = if realModulusLimit N < (q : ℝ) then packetFee N a q else 0 := by
  simp only [layerFee, dif_neg (NeZero.ne q)]

theorem continuous_highPart {N : ℕ} (hN : 0 < N) (a q : ℕ) (positive : Bool) :
    Continuous (highPart N a q positive) := by
  by_cases hq : q = 0
  · subst q
    change Continuous (fun _ : ℝ => (0 : ℂ))
    exact continuous_const
  · let : NeZero q := ⟨hq⟩
    simp only [funext (highPart_eq N a positive)]
    unfold realPacketOn
    exact continuous_const.mul (continuous_finsetSum _ (fun chi _ =>
      continuous_const.mul (continuous_finsetSum _ (fun rho _ =>
        continuous_const.mul (SingularIntegral.Jrho_continuous hN rho)))))

theorem norm_selectedRest_le_layer_high {N a q : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hq : (q : ℝ) ≤ sourceP N) (hi : sourceIndex a q) {eta : ℝ}
    (he : deltaRadius N q < |eta|) :
    ‖selectedRest N a q eta‖ ≤ layerFee N a q + ‖selectedHigh N a q eta‖ := by
  let : NeZero q := ⟨Nat.ne_of_gt (sourceIndex_den_pos hi)⟩
  have hh (positive : Bool) :
      ‖restPart N a q positive eta‖ ≤ layerFee N a q + ‖highPart N a q positive eta‖ := by
    rw [restPart_eq, highPart_eq, restPacket_eq_largeLow_add_high, layerFee_eq]
    by_cases hlarge : realModulusLimit N < (q : ℝ)
    · rw [if_pos hlarge]
      exact (norm_add_le _ _).trans (add_le_add (norm_largeLowPacket hN hq hi positive he) le_rfl)
    · rw [if_neg hlarge]
      have hz : realPacketOn q a (fun chi => largeLowValues chi N positive) N eta = 0 := by
        simp [realPacketOn, largeLow_empty hN (le_of_not_gt hlarge)]
      simp only [hz, zero_add, le_refl]
  unfold selectedRest selectedHigh
  split_ifs
  · exact hh true
  · exact hh false

def highShellCost (N a q : ℕ) : ℝ :=
  ∫ alpha in shell N a q,
    ‖selectedHigh N a q (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2

def highCost (N : ℕ) : ℝ := ∑ i ∈ coreIndices N, highShellCost N i.2 i.1

def shellEnergy (N a q : ℕ) : ℝ := ∫ alpha in shell N a q, ‖S N alpha‖ ^ 2

def layerCost (N : ℕ) : ℝ := ∑ i ∈ coreIndices N, layerFee N i.2 i.1 * shellEnergy N i.2 i.1

theorem integrable_high_weight {N : ℕ} (hN : 0 < N) (a q : ℕ) :
    IntegrableOn (fun alpha : ℝ =>
      ‖selectedHigh N a q (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2) (shell N a q) :=
  integrable_selected_weight a q _ _ (continuous_highPart hN a q true) (continuous_highPart hN a q false)

theorem highCost_nonneg (N : ℕ) : 0 ≤ highCost N :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)))

theorem restShellCost_le_layer_high {N a q : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hq : (q : ℝ) ≤ sourceP N) (hi : sourceIndex a q) :
    restShellCost N a q ≤ layerFee N a q * shellEnergy N a q + highShellCost N a q := by
  have he : IntegrableOn (fun alpha : ℝ => ‖S N alpha‖ ^ 2) (shell N a q) :=
    (continuous_energy N).integrableOn_Icc.mono_set Set.sdiff_subset
  have hf := integrable_rest_weight (nat_pos_of_exp_le hN) a q
  have hg := integrable_high_weight (nat_pos_of_exp_le hN) a q
  unfold restShellCost highShellCost shellEnergy
  calc
    _ ≤ ∫ alpha in shell N a q, layerFee N a q * ‖S N alpha‖ ^ 2 +
        ‖selectedHigh N a q (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2 := by
      apply setIntegral_mono_on hf ((he.const_mul _).add hg) (measurableSet_shell N a q)
      intro alpha ha
      simpa only [add_mul, Pi.add_apply] using mul_le_mul_of_nonneg_right
        (norm_selectedRest_le_layer_high hN hq hi (shell_same_eta hq hi ha).1) (sq_nonneg ‖S N alpha‖)
    _ = _ := by rw [integral_add (he.const_mul _) hg, integral_const_mul]

theorem restCost_le_layer_high {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    restCost N ≤ layerCost N + highCost N := by
  unfold restCost layerCost highCost
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hh := (mem_coreIndices (exp_2000_le_of_exp_3100_le hN) i).mp hi
  exact restShellCost_le_layer_high hN hh.1 hh.2

def largeEnergy (N : ℕ) : ℝ :=
  ∑ i ∈ (coreIndices N).filter (fun i => realModulusLimit N < (i.1 : ℝ)), shellEnergy N i.2 i.1

def smallEnergy (N : ℕ) : ℝ :=
  ∑ i ∈ (coreIndices N).filter (fun i => (i.1 : ℝ) ≤ realModulusLimit N), shellEnergy N i.2 i.1

theorem energy_partition {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    smallEnergy N + largeEnergy N = ∫ alpha in M2 N, ‖S N alpha‖ ^ 2 := by
  rw [integral_M2_eq_shell_sum (exp_2000_le_of_exp_3100_le hN) _ (continuous_energy N)]
  unfold smallEnergy largeEnergy shellEnergy
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : (i.1 : ℝ) ≤ realModulusLimit N <;> simp [h, not_le.mp, not_lt.mpr]

theorem largeEnergy_le_E2 {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    largeEnergy N ≤ ∫ alpha in M2 N, ‖S N alpha‖ ^ 2 := by
  rw [← energy_partition hN]
  exact le_add_of_nonneg_left (Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)))

theorem layerFee_small {N a q : ℕ} (hq : (q : ℝ) ≤ realModulusLimit N) :
    layerFee N a q = 0 := by
  unfold layerFee
  split_ifs <;> simp_all only [not_lt_of_ge hq]

theorem layerCost_only_large (N : ℕ) :
    layerCost N =
      ∑ i ∈ (coreIndices N).filter (fun i => realModulusLimit N < (i.1 : ℝ)),
        layerFee N i.2 i.1 * shellEnergy N i.2 i.1 := by
  unfold layerCost
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : realModulusLimit N < (i.1 : ℝ)
  · simp only [h, if_true]
  · simp only [h, if_false, layerFee_small (le_of_not_gt h), zero_mul]

theorem M2_integral_le_mothers_layer_high {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
      fullFee N * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) + layerCost N + highCost N := by
  have hh := M2_integral_le_full_mothers_rest hN
  have hl := restCost_le_layer_high hN
  linarith only [hh, hl]

theorem M2_same_witness_layer_high {N : ℕ} {alpha : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (ha : alpha ∈ M2 N) :
    ∃ (q a : ℕ) (eta : ℝ), (q : ℝ) ≤ sourceP N ∧ sourceIndex a q ∧
      alpha = rationalCenter a q + eta ∧ deltaRadius N q < |eta| ∧
      |eta| ≤ 1 / ((q : ℝ) * sourceQ N) ∧
      ‖S N alpha‖ ≤ fullFee N + layerFee N a q + ‖selectedHigh N a q eta‖ := by
  obtain ⟨q, a, eta, hq, hi, heq, hlo, hhi, hs⟩ := M2_same_witness_full_mothers_rest hN ha
  refine ⟨q, a, eta, hq, hi, heq, hlo, hhi, ?_⟩
  have hl := norm_selectedRest_le_layer_high hN hq hi hlo
  linarith only [hs, hl]

theorem lambdaTripleCount_ge_mothers_layer_high {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∫ alpha in M1 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re +
      (∫ alpha in M3 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re +
      (∫ alpha in M4 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re -
      fullFee N * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) - layerCost N - highCost N ≤ lambdaTripleCount N := by
  have hh := lambdaTripleCount_ge_full_mothers_rest hN
  have hl := restCost_le_layer_high hN
  linarith only [hh, hl]

end LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual.Remaining
