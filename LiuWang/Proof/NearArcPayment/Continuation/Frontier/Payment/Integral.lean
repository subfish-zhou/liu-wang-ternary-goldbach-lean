import LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Packet

/-! 从原 frontierCost 中实际支付整段近一高尾，保留原符号选择与 S² 权。 -/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment

open Interfaces Parameters ArcGeometry CompleteExpansion
open MajorArcApproximation MinorArcEnergy
open AnalyticNumberTheory.LargeSieve

def residualPart (N a q : ℕ) (positive : Bool) (eta : ℝ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    residualPacket q N a positive eta

theorem residualPart_eq {q : ℕ} [NeZero q] (N a : ℕ) (positive : Bool) (eta : ℝ) :
    residualPart N a q positive eta = residualPacket q N a positive eta := by
  simp only [residualPart, dif_neg (NeZero.ne q)]

def selectedResidual (N a q : ℕ) (eta : ℝ) : ℂ :=
  if 0 ≤ eta then residualPart N a q true eta else residualPart N a q false eta

theorem continuous_residualPart {N : ℕ} (hN : 0 < N) (a q : ℕ) (positive : Bool) :
    Continuous (residualPart N a q positive) := by
  by_cases hq : q = 0
  · subst q
    change Continuous (fun _ : ℝ => (0 : ℂ))
    exact continuous_const
  · let : NeZero q := ⟨hq⟩
    simp only [funext (residualPart_eq N a positive)]
    unfold residualPacket
    exact continuous_const.mul (continuous_finsetSum _ (fun chi _ =>
      continuous_const.mul (continuous_finsetSum _ (fun rho _ =>
        continuous_const.mul (SingularIntegral.Jrho_continuous hN rho)))))

theorem norm_selectedTail_le_polynomial_residual {N a q : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hi : sourceIndex a q) (eta : ℝ) :
    ‖selectedTail N a q eta‖ ≤
      280000 * (N : ℝ) / sourceL N ^ 3 + ‖selectedResidual N a q eta‖ := by
  let : NeZero q := ⟨Nat.ne_of_gt (sourceIndex_den_pos hi)⟩
  have hh (positive : Bool) (he : if positive then 0 ≤ eta else eta ≤ 0) :
      ‖signedTail N a q positive eta‖ ≤
        280000 * (N : ℝ) / sourceL N ^ 3 + ‖residualPart N a q positive eta‖ := by
    rw [signedTail_eq, residualPart_eq, tailPacket_eq_density_add_residual N a positive]
    exact (norm_add_le _ _).trans (add_le_add (norm_densityPacket_le_polynomial hN hq he) le_rfl)
  unfold selectedTail selectedResidual
  split_ifs with he
  · exact hh true he
  · exact hh false (le_of_lt (lt_of_not_ge he))

theorem norm_selectedTail_le_paid_residual {N a q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hi : sourceIndex a q) (eta : ℝ) :
    ‖selectedTail N a q eta‖ ≤
      0.03 * (N : ℝ) / sourceL N + ‖selectedResidual N a q eta‖ := by
  let : NeZero q := ⟨Nat.ne_of_gt (sourceIndex_den_pos hi)⟩
  have hh (positive : Bool) (he : if positive then 0 ≤ eta else eta ≤ 0) :
      ‖signedTail N a q positive eta‖ ≤
        0.03 * (N : ℝ) / sourceL N + ‖residualPart N a q positive eta‖ := by
    rw [signedTail_eq, residualPart_eq, tailPacket_eq_density_add_residual N a positive]
    exact (norm_add_le _ _).trans (add_le_add (norm_densityPacket_le_paid hN hq he) le_rfl)
  unfold selectedTail selectedResidual
  split_ifs with he
  · exact hh true he
  · exact hh false (le_of_lt (lt_of_not_ge he))

def residualShellCost (N a q : ℕ) : ℝ :=
  ∫ alpha in shell N a q,
    ‖selectedResidual N a q (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2

def residualCost (N : ℕ) : ℝ :=
  ∑ i ∈ coreIndices N, residualShellCost N i.2 i.1

theorem integrable_residual_weight {N : ℕ} (hN : 0 < N) (a q : ℕ) :
    IntegrableOn (fun alpha : ℝ =>
      ‖selectedResidual N a q (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2) (shell N a q) :=
  integrable_selected_weight a q _ _
    (continuous_residualPart hN a q true) (continuous_residualPart hN a q false)

theorem residualCost_nonneg (N : ℕ) : 0 ≤ residualCost N :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg
    (fun _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)))

theorem frontierShellCost_transfer {N a q : ℕ} (hN : 0 < N) {B : ℝ}
    (hb : ∀ eta : ℝ, ‖selectedTail N a q eta‖ ≤ B + ‖selectedResidual N a q eta‖) :
    frontierShellCost N a q ≤
      B * (∫ alpha in shell N a q, ‖S N alpha‖ ^ 2) + residualShellCost N a q := by
  have he : IntegrableOn (fun alpha : ℝ => ‖S N alpha‖ ^ 2) (shell N a q) :=
    (continuous_energy N).integrableOn_Icc.mono_set Set.sdiff_subset
  have hf := integrable_tail_weight hN a q
  have hg := integrable_residual_weight hN a q
  unfold frontierShellCost residualShellCost
  calc
    _ ≤ ∫ alpha in shell N a q, B * ‖S N alpha‖ ^ 2 +
          ‖selectedResidual N a q (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2 := by
      apply setIntegral_mono_on hf ((he.const_mul _).add hg) (measurableSet_shell N a q)
      intro alpha _
      simpa only [add_mul, Pi.add_apply] using
        mul_le_mul_of_nonneg_right (hb (alpha - rationalCenter a q)) (sq_nonneg ‖S N alpha‖)
    _ = _ := by rw [integral_add (he.const_mul _) hg, integral_const_mul]

theorem frontierCost_transfer {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) {B : ℝ}
    (hb : ∀ (a q : ℕ), (q : ℝ) ≤ sourceP N → sourceIndex a q → ∀ eta : ℝ,
      ‖selectedTail N a q eta‖ ≤ B + ‖selectedResidual N a q eta‖) :
    frontierCost N ≤ B * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) + residualCost N := by
  unfold frontierCost residualCost
  calc
    _ ≤ ∑ i ∈ coreIndices N,
        (B * (∫ alpha in shell N i.2 i.1, ‖S N alpha‖ ^ 2) +
          residualShellCost N i.2 i.1) := by
      apply Finset.sum_le_sum
      intro i hi
      have hh := (mem_coreIndices hN i).mp hi
      exact frontierShellCost_transfer (nat_pos_of_exp_le hN) (hb i.2 i.1 hh.1 hh.2)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        ← integral_M2_eq_shell_sum hN _ (continuous_energy N)]

theorem frontierCost_le_polynomial_residual {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    frontierCost N ≤
      (280000 * (N : ℝ) / sourceL N ^ 3) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        residualCost N :=
  frontierCost_transfer hN (fun _ _ hq hi => norm_selectedTail_le_polynomial_residual hN hq hi)

theorem frontierCost_le_paid_residual {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    frontierCost N ≤
      (0.03 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        residualCost N :=
  frontierCost_transfer (exp_2000_le_of_exp_3100_le hN)
    (fun _ _ hq hi => norm_selectedTail_le_paid_residual hN hq hi)

theorem C_le_density_paid {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    weightedPacketCost N ≤
      (0.0305 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        residualCost N := by
  calc
    _ ≤ (0.0005 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        ((0.03 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
          residualCost N) :=
      (C_le_five_paid_frontier hN).trans (add_le_add le_rfl (frontierCost_le_paid_residual hN))
    _ = _ := by ring

theorem M2_integral_le_density_paid {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
      (0.1086 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        residualCost N := by
  calc
    _ ≤ (0.0786 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        ((0.03 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
          residualCost N) :=
      (M2_integral_le_five_paid_frontier hN).trans
        (add_le_add le_rfl (frontierCost_le_paid_residual hN))
    _ = _ := by ring

theorem M2_same_witness_density_paid {N : ℕ} {alpha : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (ha : alpha ∈ M2 N) :
    ∃ (q a : ℕ) (eta : ℝ), (q : ℝ) ≤ sourceP N ∧ sourceIndex a q ∧
      alpha = rationalCenter a q + eta ∧ deltaRadius N q < |eta| ∧
      |eta| ≤ 1 / ((q : ℝ) * sourceQ N) ∧
      ‖S N alpha‖ ≤ 0.1086 * (N : ℝ) / sourceL N + ‖selectedResidual N a q eta‖ := by
  obtain ⟨q, a, eta, hq, hi, heq, hlo, hhi, hs⟩ := M2_same_witness_five_paid hN ha
  refine ⟨q, a, eta, hq, hi, heq, hlo, hhi, ?_⟩
  calc
    _ ≤ 0.0786 * (N : ℝ) / sourceL N +
        (0.03 * (N : ℝ) / sourceL N + ‖selectedResidual N a q eta‖) :=
      hs.trans (add_le_add le_rfl (norm_selectedTail_le_paid_residual hN hq hi eta))
    _ = _ := by ring

theorem M2_integral_le_4012_of_residualCost {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hz : residualCost N ≤
      (0.2926 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2)) :
    ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
      (0.4012 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) := by
  calc
    _ ≤ (0.1086 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        (0.2926 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) :=
      (M2_integral_le_density_paid hN).trans (add_le_add le_rfl hz)
    _ = _ := by ring

theorem lambdaTripleCount_ge_density_paid {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∫ alpha in M1 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re +
      (∫ alpha in M3 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re +
      (∫ alpha in M4 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re -
      (0.1086 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) -
      residualCost N ≤ lambdaTripleCount N := by
  have hh := lambdaTripleCount_ge_five_paid hN
  have hc := frontierCost_le_paid_residual hN
  have he : (0.1086 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) =
      (0.0786 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        (0.03 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) := by ring
  linarith only [hh, hc, he]

end LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment
