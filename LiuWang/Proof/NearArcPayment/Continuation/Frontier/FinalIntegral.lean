import LiuWang.Proof.NearArcPayment.Continuation.Frontier.SquareRootBand

/-! 两个新振荡付款连续接入原 finalCost，不重复计旧 A/B/D 或能量。 -/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearArcPayment.Continuation.Frontier

open Interfaces Parameters ArcGeometry CompleteExpansion
open MajorArcApproximation MinorArcEnergy
open AnalyticNumberTheory.LargeSieve

def signedTail (N a q : ℕ) (positive : Bool) (eta : ℝ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    tailPacket q N a positive eta

theorem signedTail_eq {q : ℕ} [NeZero q] (N a : ℕ) (positive : Bool) (eta : ℝ) :
    signedTail N a q positive eta = tailPacket q N a positive eta := by
  simp only [signedTail, dif_neg (NeZero.ne q)]

def selectedTail (N a q : ℕ) (eta : ℝ) : ℂ :=
  if 0 ≤ eta then signedTail N a q true eta else signedTail N a q false eta

theorem continuous_signedTail {N : ℕ} (hN : 0 < N) (a q : ℕ) (positive : Bool) :
    Continuous (signedTail N a q positive) := by
  by_cases hq : q = 0
  · subst q
    change Continuous (fun _ : ℝ => (0 : ℂ))
    exact continuous_const
  · let : NeZero q := ⟨hq⟩
    simp only [funext (signedTail_eq N a positive)]
    unfold tailPacket
    exact continuous_const.mul (continuous_finsetSum _ (fun chi _ =>
      continuous_const.mul (continuous_finsetSum _ (fun rho _ =>
        continuous_const.mul (SingularIntegral.Jrho_continuous hN rho)))))

theorem norm_activePart_le_paid_tail {N a q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hi : sourceIndex a q) (eta : ℝ) :
    ‖activePart N a q eta‖ ≤ 0.0001 * (N : ℝ) / sourceL N + ‖selectedTail N a q eta‖ := by
  let : NeZero q := ⟨Nat.ne_of_gt (sourceIndex_den_pos hi)⟩
  have hh (positive : Bool) :
      ‖signedPart N a q positive eta‖ ≤
        0.0001 * (N : ℝ) / sourceL N + ‖signedTail N a q positive eta‖ := by
    rw [signedPart_eq, signedTail_eq, remainingPacket_eq_square_add_tail N a positive]
    exact (norm_add_le _ _).trans
      (add_le_add (norm_squarePacket_le_paid hN hq positive eta) le_rfl)
  unfold activePart selectedTail
  split_ifs
  · exact hh true
  · exact hh false

def frontierShellCost (N a q : ℕ) : ℝ :=
  ∫ alpha in shell N a q,
    ‖selectedTail N a q (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2

def frontierCost (N : ℕ) : ℝ :=
  ∑ i ∈ coreIndices N, frontierShellCost N i.2 i.1

theorem integrable_selected_weight {N : ℕ} (a q : ℕ)
    (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G) :
    IntegrableOn (fun alpha : ℝ =>
      ‖if 0 ≤ alpha - rationalCenter a q then F (alpha - rationalCenter a q)
        else G (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2) (shell N a q) := by
  let U : Set ℝ := {alpha | 0 ≤ alpha - rationalCenter a q}
  have hU : MeasurableSet U := measurableSet_le measurable_const
    (measurable_id.sub measurable_const)
  have hf : Integrable (fun alpha : ℝ =>
      ‖F (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2)
      (volume.restrict (shell N a q)) :=
    ((hF.comp (continuous_id.sub continuous_const)).norm.mul
      (continuous_energy N)).integrableOn_Icc.mono_set Set.sdiff_subset
  have hg : Integrable (fun alpha : ℝ =>
      ‖G (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2)
      (volume.restrict (shell N a q)) :=
    ((hG.comp (continuous_id.sub continuous_const)).norm.mul
      (continuous_energy N)).integrableOn_Icc.mono_set Set.sdiff_subset
  apply ((hf.indicator hU).add (hg.indicator hU.compl)).congr
  filter_upwards [] with alpha
  by_cases he : 0 ≤ alpha - rationalCenter a q
  · have hp := sub_nonneg.mp he
    simp [U, Set.indicator, he, hp]
  · have hp : alpha < rationalCenter a q := by linarith
    simp [U, Set.indicator, he, not_le_of_gt hp]

theorem integrable_tail_weight {N : ℕ} (hN : 0 < N) (a q : ℕ) :
    IntegrableOn (fun alpha : ℝ =>
      ‖selectedTail N a q (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2) (shell N a q) :=
  integrable_selected_weight a q _ _
    (continuous_signedTail hN a q true) (continuous_signedTail hN a q false)

theorem frontierCost_nonneg (N : ℕ) : 0 ≤ frontierCost N :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg
    (fun _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)))

theorem activeShellCost_le_paid_tail {N a q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hi : sourceIndex a q) :
    activeShellCost N a q ≤
      (0.0001 * (N : ℝ) / sourceL N) * (∫ alpha in shell N a q, ‖S N alpha‖ ^ 2) +
        frontierShellCost N a q := by
  have he : IntegrableOn (fun alpha : ℝ => ‖S N alpha‖ ^ 2) (shell N a q) :=
    (continuous_energy N).integrableOn_Icc.mono_set Set.sdiff_subset
  have hf := integrable_active_weight (nat_pos_of_exp_le hN) a q
  have hg := integrable_tail_weight (nat_pos_of_exp_le hN) a q
  unfold activeShellCost frontierShellCost
  calc
    _ ≤ ∫ alpha in shell N a q,
        (0.0001 * (N : ℝ) / sourceL N) * ‖S N alpha‖ ^ 2 +
          ‖selectedTail N a q (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2 := by
      apply setIntegral_mono_on hf ((he.const_mul _).add hg) (measurableSet_shell N a q)
      intro alpha _
      simpa only [add_mul, Pi.add_apply] using
        mul_le_mul_of_nonneg_right
          (norm_activePart_le_paid_tail hN hq hi (alpha - rationalCenter a q))
          (sq_nonneg ‖S N alpha‖)
    _ = _ := by rw [integral_add (he.const_mul _) hg, integral_const_mul]

theorem activeCost_le_paid_tail {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    activeCost N ≤
      (0.0001 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        frontierCost N := by
  have hN0 := exp_2000_le_of_exp_3100_le hN
  unfold activeCost frontierCost
  calc
    _ ≤ ∑ i ∈ coreIndices N,
        ((0.0001 * (N : ℝ) / sourceL N) * (∫ alpha in shell N i.2 i.1, ‖S N alpha‖ ^ 2) +
          frontierShellCost N i.2 i.1) := by
      apply Finset.sum_le_sum
      intro i hi
      have hh := (mem_coreIndices hN0 i).mp hi
      exact activeShellCost_le_paid_tail hN hh.1 hh.2
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        ← integral_M2_eq_shell_sum hN0 _ (continuous_energy N)]

theorem finalCost_le_two_paid_frontier {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    finalCost N ≤
      (0.0002 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        frontierCost N := by
  calc
    _ ≤ (0.0001 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        ((0.0001 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
          frontierCost N) :=
      (finalCost_le_paid_active hN).trans (add_le_add le_rfl (activeCost_le_paid_tail hN))
    _ = _ := by ring

theorem C_le_five_paid_frontier {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    weightedPacketCost N ≤
      (0.0005 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        frontierCost N := by
  calc
    _ ≤ (0.0003 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        ((0.0002 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
          frontierCost N) :=
      (C_le_three_paid_final hN).trans (add_le_add le_rfl (finalCost_le_two_paid_frontier hN))
    _ = _ := by ring

theorem M2_integral_le_five_paid_frontier {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
      (0.0786 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        frontierCost N := by
  calc
    _ ≤ (0.0784 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        ((0.0002 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
          frontierCost N) :=
      (M2_integral_le_three_paid_final hN).trans
        (add_le_add le_rfl (finalCost_le_two_paid_frontier hN))
    _ = _ := by ring

theorem M2_same_witness_five_paid {N : ℕ} {alpha : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (ha : alpha ∈ M2 N) :
    ∃ (q a : ℕ) (eta : ℝ), (q : ℝ) ≤ sourceP N ∧ sourceIndex a q ∧
      alpha = rationalCenter a q + eta ∧ deltaRadius N q < |eta| ∧
      |eta| ≤ 1 / ((q : ℝ) * sourceQ N) ∧
      ‖S N alpha‖ ≤ 0.0786 * (N : ℝ) / sourceL N + ‖selectedTail N a q eta‖ := by
  obtain ⟨q, a, eta, hq, hi, heq, hlo, hhi, hs⟩ := M2_same_witness_four_paid hN ha
  refine ⟨q, a, eta, hq, hi, heq, hlo, hhi, ?_⟩
  calc
    _ ≤ 0.0785 * (N : ℝ) / sourceL N +
        (0.0001 * (N : ℝ) / sourceL N + ‖selectedTail N a q eta‖) :=
      hs.trans (add_le_add le_rfl (norm_activePart_le_paid_tail hN hq hi eta))
    _ = _ := by ring

theorem M2_integral_le_4012_of_frontierCost {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hz : frontierCost N ≤
      (0.3226 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2)) :
    ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
      (0.4012 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) := by
  calc
    _ ≤ (0.0786 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        (0.3226 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) :=
      (M2_integral_le_five_paid_frontier hN).trans (add_le_add le_rfl hz)
    _ = _ := by ring

theorem lambdaTripleCount_ge_five_paid {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∫ alpha in M1 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re +
      (∫ alpha in M3 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re +
      (∫ alpha in M4 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re -
      (0.0786 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) -
      frontierCost N ≤ lambdaTripleCount N := by
  have hh := lambdaTripleCount_ge_three_paid hN
  have hc := finalCost_le_two_paid_frontier hN
  have he : (0.0786 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) =
      (0.0784 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        (0.0002 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) := by ring
  linarith only [hh, hc, he]

end LiuWang.Proof.NearArcPayment.Continuation.Frontier
