import LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.RealFamily

/-! 高尾和未付实零族的两笔密度费用共同接入原 frontier 与共享 E2。 -/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment

open Interfaces Parameters ArcGeometry CompleteExpansion
open MajorArcApproximation MinorArcEnergy
open AnalyticNumberTheory.LargeSieve

def lastPart (N a q : ℕ) (positive : Bool) (eta : ℝ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    lastPacket q N a positive eta

theorem lastPart_eq {q : ℕ} [NeZero q] (N a : ℕ) (positive : Bool) (eta : ℝ) :
    lastPart N a q positive eta = lastPacket q N a positive eta := by
  simp only [lastPart, dif_neg (NeZero.ne q)]

def selectedLast (N a q : ℕ) (eta : ℝ) : ℂ :=
  if 0 ≤ eta then lastPart N a q true eta else lastPart N a q false eta

theorem continuous_lastPart {N : ℕ} (hN : 0 < N) (a q : ℕ) (positive : Bool) :
    Continuous (lastPart N a q positive) := by
  by_cases hq : q = 0
  · subst q
    change Continuous (fun _ : ℝ => (0 : ℂ))
    exact continuous_const
  · let : NeZero q := ⟨hq⟩
    simp only [funext (lastPart_eq N a positive)]
    unfold lastPacket
    exact continuous_const.mul (continuous_finsetSum _ (fun chi _ =>
      continuous_const.mul (continuous_finsetSum _ (fun rho _ =>
        continuous_const.mul (SingularIntegral.Jrho_continuous hN rho)))))

theorem norm_selectedResidual_le_paid_last {N a q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hi : sourceIndex a q) {eta : ℝ}
    (he : deltaRadius N q < |eta|) :
    ‖selectedResidual N a q eta‖ ≤
      0.007 * (N : ℝ) / sourceL N + ‖selectedLast N a q eta‖ := by
  let : NeZero q := ⟨Nat.ne_of_gt (sourceIndex_den_pos hi)⟩
  have hh (positive : Bool) :
      ‖residualPart N a q positive eta‖ ≤
        0.007 * (N : ℝ) / sourceL N + ‖lastPart N a q positive eta‖ := by
    rw [residualPart_eq, lastPart_eq, residualPacket_eq_real_add_last N a positive]
    exact (norm_add_le _ _).trans (add_le_add (norm_realPacket_le_paid hN positive he) le_rfl)
  unfold selectedResidual selectedLast
  split_ifs
  · exact hh true
  · exact hh false

def lastShellCost (N a q : ℕ) : ℝ :=
  ∫ alpha in shell N a q,
    ‖selectedLast N a q (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2

def lastCost (N : ℕ) : ℝ :=
  ∑ i ∈ coreIndices N, lastShellCost N i.2 i.1

theorem integrable_last_weight {N : ℕ} (hN : 0 < N) (a q : ℕ) :
    IntegrableOn (fun alpha : ℝ =>
      ‖selectedLast N a q (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2) (shell N a q) :=
  integrable_selected_weight a q _ _
    (continuous_lastPart hN a q true) (continuous_lastPart hN a q false)

theorem lastCost_nonneg (N : ℕ) : 0 ≤ lastCost N :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg
    (fun _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)))

theorem residualShellCost_le_paid_last {N a q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) (hi : sourceIndex a q) :
    residualShellCost N a q ≤
      (0.007 * (N : ℝ) / sourceL N) * (∫ alpha in shell N a q, ‖S N alpha‖ ^ 2) +
        lastShellCost N a q := by
  have he : IntegrableOn (fun alpha : ℝ => ‖S N alpha‖ ^ 2) (shell N a q) :=
    (continuous_energy N).integrableOn_Icc.mono_set Set.sdiff_subset
  have hf := integrable_residual_weight (nat_pos_of_exp_le hN) a q
  have hg := integrable_last_weight (nat_pos_of_exp_le hN) a q
  unfold residualShellCost lastShellCost
  calc
    _ ≤ ∫ alpha in shell N a q,
        (0.007 * (N : ℝ) / sourceL N) * ‖S N alpha‖ ^ 2 +
          ‖selectedLast N a q (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2 := by
      apply setIntegral_mono_on hf ((he.const_mul _).add hg) (measurableSet_shell N a q)
      intro alpha ha
      simpa only [add_mul, Pi.add_apply] using
        mul_le_mul_of_nonneg_right
          (norm_selectedResidual_le_paid_last hN hi (shell_same_eta hq hi ha).1)
          (sq_nonneg ‖S N alpha‖)
    _ = _ := by rw [integral_add (he.const_mul _) hg, integral_const_mul]

theorem residualCost_le_paid_last {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    residualCost N ≤
      (0.007 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) + lastCost N := by
  have hN0 := exp_2000_le_of_exp_3100_le hN
  unfold residualCost lastCost
  calc
    _ ≤ ∑ i ∈ coreIndices N,
        ((0.007 * (N : ℝ) / sourceL N) * (∫ alpha in shell N i.2 i.1, ‖S N alpha‖ ^ 2) +
          lastShellCost N i.2 i.1) := by
      apply Finset.sum_le_sum
      intro i hi
      have hh := (mem_coreIndices hN0 i).mp hi
      exact residualShellCost_le_paid_last hN hh.1 hh.2
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        ← integral_M2_eq_shell_sum hN0 _ (continuous_energy N)]

theorem frontierCost_le_density_real_paid {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    frontierCost N ≤
      (0.037 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) + lastCost N := by
  calc
    _ ≤ (0.03 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        ((0.007 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) + lastCost N) :=
      (frontierCost_le_paid_residual hN).trans (add_le_add le_rfl (residualCost_le_paid_last hN))
    _ = _ := by ring

theorem C_le_density_real_paid {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    weightedPacketCost N ≤
      (0.0375 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) + lastCost N := by
  calc
    _ ≤ (0.0005 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        ((0.037 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) + lastCost N) :=
      (C_le_five_paid_frontier hN).trans (add_le_add le_rfl (frontierCost_le_density_real_paid hN))
    _ = _ := by ring

theorem M2_integral_le_density_real_paid {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
      (0.1156 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) + lastCost N := by
  calc
    _ ≤ (0.0786 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        ((0.037 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) + lastCost N) :=
      (M2_integral_le_five_paid_frontier hN).trans
        (add_le_add le_rfl (frontierCost_le_density_real_paid hN))
    _ = _ := by ring

theorem M2_same_witness_density_real_paid {N : ℕ} {alpha : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (ha : alpha ∈ M2 N) :
    ∃ (q a : ℕ) (eta : ℝ), (q : ℝ) ≤ sourceP N ∧ sourceIndex a q ∧
      alpha = rationalCenter a q + eta ∧ deltaRadius N q < |eta| ∧
      |eta| ≤ 1 / ((q : ℝ) * sourceQ N) ∧
      ‖S N alpha‖ ≤ 0.1156 * (N : ℝ) / sourceL N + ‖selectedLast N a q eta‖ := by
  obtain ⟨q, a, eta, hq, hi, heq, hlo, hhi, hs⟩ := M2_same_witness_density_paid hN ha
  refine ⟨q, a, eta, hq, hi, heq, hlo, hhi, ?_⟩
  calc
    _ ≤ 0.1086 * (N : ℝ) / sourceL N +
        (0.007 * (N : ℝ) / sourceL N + ‖selectedLast N a q eta‖) :=
      hs.trans (add_le_add le_rfl (norm_selectedResidual_le_paid_last hN hi hlo))
    _ = _ := by ring

theorem M2_integral_le_4012_of_lastCost {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hz : lastCost N ≤
      (0.2856 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2)) :
    ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
      (0.4012 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) := by
  calc
    _ ≤ (0.1156 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        (0.2856 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) :=
      (M2_integral_le_density_real_paid hN).trans (add_le_add le_rfl hz)
    _ = _ := by ring

theorem lambdaTripleCount_ge_density_real_paid {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∫ alpha in M1 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re +
      (∫ alpha in M3 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re +
      (∫ alpha in M4 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re -
      (0.1156 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) -
      lastCost N ≤ lambdaTripleCount N := by
  have hh := lambdaTripleCount_ge_five_paid hN
  have hc := frontierCost_le_density_real_paid hN
  have he : (0.1156 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) =
      (0.0786 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        (0.037 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) := by ring
  linarith only [hh, hc, he]

end LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment
