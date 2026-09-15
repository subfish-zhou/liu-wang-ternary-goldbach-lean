import LiuWang.Proof.NearArcPayment.Continuation.Frontier.AlignedBand

/-!
按 eta 的符号选择固定零点有限集。两支连续，选择函数只需可积；
在 eta = 0 不伪称连续。指示函数在每个真实 shell 上给出可积性。
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearArcPayment.Continuation.Frontier

open Interfaces Parameters ArcGeometry CompleteExpansion
open MajorArcApproximation MinorArcEnergy
open AnalyticNumberTheory.LargeSieve

def signedPart (N a q : ℕ) (positive : Bool) (eta : ℝ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    remainingPacket q N a positive eta

theorem signedPart_eq {q : ℕ} [NeZero q] (N a : ℕ) (positive : Bool) (eta : ℝ) :
    signedPart N a q positive eta = remainingPacket q N a positive eta := by
  simp only [signedPart, dif_neg (NeZero.ne q)]

def activePart (N a q : ℕ) (eta : ℝ) : ℂ :=
  if 0 ≤ eta then signedPart N a q true eta else signedPart N a q false eta

theorem continuous_signedPart {N : ℕ} (hN : 0 < N) (a q : ℕ) (positive : Bool) :
    Continuous (signedPart N a q positive) := by
  by_cases hq : q = 0
  · subst q
    change Continuous (fun _ : ℝ => (0 : ℂ))
    exact continuous_const
  · let : NeZero q := ⟨hq⟩
    simp only [funext (signedPart_eq N a positive)]
    unfold remainingPacket
    exact continuous_const.mul (continuous_finsetSum _ (fun chi _ =>
      continuous_const.mul (continuous_finsetSum _ (fun rho _ =>
        continuous_const.mul (SingularIntegral.Jrho_continuous hN rho)))))

theorem norm_finalPart_le_paid_active {N a q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hi : sourceIndex a q) (eta : ℝ) :
    ‖finalPart N a q eta‖ ≤ 0.0001 * (N : ℝ) / sourceL N + ‖activePart N a q eta‖ := by
  let : NeZero q := ⟨Nat.ne_of_gt (sourceIndex_den_pos hi)⟩
  have hh (positive : Bool) (he : if positive then 0 ≤ eta else eta ≤ 0) :
      ‖finalPart N a q eta‖ ≤
        0.0001 * (N : ℝ) / sourceL N + ‖signedPart N a q positive eta‖ := by
    rw [finalPart_eq, signedPart_eq, finalPacket_eq_aligned_add_remaining N a positive]
    exact (norm_add_le _ _).trans (add_le_add (norm_alignedPacket_le_paid hN hq he) le_rfl)
  unfold activePart
  split_ifs with he
  · exact hh true he
  · exact hh false (le_of_lt (lt_of_not_ge he))

def activeShellCost (N a q : ℕ) : ℝ :=
  ∫ alpha in shell N a q,
    ‖activePart N a q (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2

def activeCost (N : ℕ) : ℝ :=
  ∑ i ∈ coreIndices N, activeShellCost N i.2 i.1

theorem integrable_active_weight {N : ℕ} (hN : 0 < N) (a q : ℕ) :
    IntegrableOn (fun alpha : ℝ =>
      ‖activePart N a q (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2) (shell N a q) := by
  let U : Set ℝ := {alpha | 0 ≤ alpha - rationalCenter a q}
  have hU : MeasurableSet U := measurableSet_le measurable_const
    (measurable_id.sub measurable_const)
  have hf (positive : Bool) :
      Integrable (fun alpha : ℝ =>
        ‖signedPart N a q positive (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2)
        (volume.restrict (shell N a q)) :=
    (((continuous_signedPart hN a q positive).comp
      (continuous_id.sub continuous_const)).norm.mul
        (continuous_energy N)).integrableOn_Icc.mono_set Set.sdiff_subset
  have hh := ((hf true).indicator hU).add ((hf false).indicator hU.compl)
  apply hh.congr
  filter_upwards [] with alpha
  by_cases he : 0 ≤ alpha - rationalCenter a q
  · have hp := sub_nonneg.mp he
    simp [U, activePart, Set.indicator, he, hp]
  · have hp : alpha < rationalCenter a q := by linarith
    simp [U, activePart, Set.indicator, he, not_le_of_gt hp]

theorem activeCost_nonneg (N : ℕ) : 0 ≤ activeCost N :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg
    (fun _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)))

theorem finalShellCost_le_paid_active {N a q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hi : sourceIndex a q) :
    finalShellCost N a q ≤
      (0.0001 * (N : ℝ) / sourceL N) * (∫ alpha in shell N a q, ‖S N alpha‖ ^ 2) +
        activeShellCost N a q := by
  have he : IntegrableOn (fun alpha : ℝ => ‖S N alpha‖ ^ 2) (shell N a q) :=
    (continuous_energy N).integrableOn_Icc.mono_set Set.sdiff_subset
  have hf : IntegrableOn (fun alpha : ℝ =>
      ‖finalPart N a q (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2) (shell N a q) :=
    (((continuous_finalPart (nat_pos_of_exp_le hN) a q).comp
      (continuous_id.sub continuous_const)).norm.mul
        (continuous_energy N)).integrableOn_Icc.mono_set Set.sdiff_subset
  have hg := integrable_active_weight (nat_pos_of_exp_le hN) a q
  unfold finalShellCost activeShellCost
  calc
    _ ≤ ∫ alpha in shell N a q,
        (0.0001 * (N : ℝ) / sourceL N) * ‖S N alpha‖ ^ 2 +
          ‖activePart N a q (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2 := by
      apply setIntegral_mono_on hf ((he.const_mul _).add hg) (measurableSet_shell N a q)
      intro alpha _
      simpa only [add_mul, Pi.add_apply] using
        mul_le_mul_of_nonneg_right
          (norm_finalPart_le_paid_active hN hq hi (alpha - rationalCenter a q))
          (sq_nonneg ‖S N alpha‖)
    _ = _ := by rw [integral_add (he.const_mul _) hg, integral_const_mul]

theorem finalCost_le_paid_active {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    finalCost N ≤
      (0.0001 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        activeCost N := by
  have hN0 := exp_2000_le_of_exp_3100_le hN
  unfold finalCost activeCost
  calc
    _ ≤ ∑ i ∈ coreIndices N,
        ((0.0001 * (N : ℝ) / sourceL N) * (∫ alpha in shell N i.2 i.1, ‖S N alpha‖ ^ 2) +
          activeShellCost N i.2 i.1) := by
      apply Finset.sum_le_sum
      intro i hi
      have hh := (mem_coreIndices hN0 i).mp hi
      exact finalShellCost_le_paid_active hN hh.1 hh.2
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        ← integral_M2_eq_shell_sum hN0 _ (continuous_energy N)]

theorem C_le_four_paid_active {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    weightedPacketCost N ≤
      (0.0004 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        activeCost N := by
  calc
    _ ≤ (0.0003 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        ((0.0001 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
          activeCost N) :=
      (C_le_three_paid_final hN).trans (add_le_add le_rfl (finalCost_le_paid_active hN))
    _ = _ := by ring

theorem M2_integral_le_four_paid_active {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
      (0.0785 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        activeCost N := by
  calc
    _ ≤ (0.0784 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        ((0.0001 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
          activeCost N) :=
      (M2_integral_le_three_paid_final hN).trans (add_le_add le_rfl (finalCost_le_paid_active hN))
    _ = _ := by ring

theorem M2_same_witness_four_paid {N : ℕ} {alpha : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (ha : alpha ∈ M2 N) :
    ∃ (q a : ℕ) (eta : ℝ), (q : ℝ) ≤ sourceP N ∧ sourceIndex a q ∧
      alpha = rationalCenter a q + eta ∧ deltaRadius N q < |eta| ∧
      |eta| ≤ 1 / ((q : ℝ) * sourceQ N) ∧
      ‖S N alpha‖ ≤ 0.0785 * (N : ℝ) / sourceL N + ‖activePart N a q eta‖ := by
  obtain ⟨q, a, eta, hq, hi, heq, hlo, hhi, hs⟩ := M2_same_witness_three_paid hN ha
  refine ⟨q, a, eta, hq, hi, heq, hlo, hhi, ?_⟩
  calc
    _ ≤ 0.0784 * (N : ℝ) / sourceL N +
        (0.0001 * (N : ℝ) / sourceL N + ‖activePart N a q eta‖) :=
      hs.trans (add_le_add le_rfl (norm_finalPart_le_paid_active hN hq hi eta))
    _ = _ := by ring

theorem M2_integral_le_4012_of_activeCost {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hz : activeCost N ≤
      (0.3227 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2)) :
    ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
      (0.4012 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) := by
  calc
    _ ≤ (0.0785 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        (0.3227 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) :=
      (M2_integral_le_four_paid_active hN).trans (add_le_add le_rfl hz)
    _ = _ := by ring

theorem lambdaTripleCount_ge_four_paid {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∫ alpha in M1 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re +
      (∫ alpha in M3 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re +
      (∫ alpha in M4 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re -
      (0.0785 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) -
      activeCost N ≤ lambdaTripleCount N := by
  have hh := lambdaTripleCount_ge_three_paid hN
  have hc := finalCost_le_paid_active hN
  have he : (0.0785 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) =
      (0.0784 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        (0.0001 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) := by ring
  linarith only [hh, hc, he]

end LiuWang.Proof.NearArcPayment.Continuation.Frontier
