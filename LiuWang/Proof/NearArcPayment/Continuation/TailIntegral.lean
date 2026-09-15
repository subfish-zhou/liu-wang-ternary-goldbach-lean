import LiuWang.Proof.NearArcPayment.Continuation.WholeHeight
import LiuWang.Proof.NearArcPayment.Continuation.Regression

/-! The third disjoint payment is consumed by the actual M2 integral. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearArcPayment.Continuation

open Interfaces Parameters ArcGeometry CompleteExpansion
open MajorArcApproximation MinorArcEnergy
open AnalyticNumberTheory.LargeSieve

def finalPart (N a q : ℕ) (eta : ℝ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    finalPacket q N a eta

theorem finalPart_eq {q : ℕ} [NeZero q] (N a : ℕ) (eta : ℝ) :
    finalPart N a q eta = finalPacket q N a eta := by
  simp only [finalPart, dif_neg (NeZero.ne q)]

theorem continuous_finalPart {N : ℕ} (hN : 0 < N) (a q : ℕ) :
    Continuous (finalPart N a q) := by
  by_cases hq : q = 0
  · subst q
    change Continuous (fun _ : ℝ => (0 : ℂ))
    exact continuous_const
  · let : NeZero q := ⟨hq⟩
    simp only [funext (finalPart_eq N a)]
    unfold finalPacket
    exact continuous_const.mul (continuous_finsetSum _ (fun chi _ =>
      continuous_const.mul (continuous_finsetSum _ (fun rho _ =>
        continuous_const.mul (SingularIntegral.Jrho_continuous hN rho)))))

theorem norm_unpaidPart_le_paid_final {N a q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hi : sourceIndex a q) (eta : ℝ) :
    ‖unpaidPart N a q eta‖ ≤
      0.0001 * (N : ℝ) / sourceL N + ‖finalPart N a q eta‖ := by
  let : NeZero q := ⟨Nat.ne_of_gt (sourceIndex_den_pos hi)⟩
  rw [unpaidPart_eq, finalPart_eq, unpaidPacket_eq_whole_add_final]
  exact (norm_add_le _ _).trans (add_le_add (norm_wholePaidPacket_le_paid hN hq eta) le_rfl)

def finalShellCost (N a q : ℕ) : ℝ :=
  ∫ alpha in shell N a q,
    ‖finalPart N a q (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2

def finalCost (N : ℕ) : ℝ :=
  ∑ i ∈ coreIndices N, finalShellCost N i.2 i.1

theorem finalCost_nonneg (N : ℕ) : 0 ≤ finalCost N :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg
    (fun _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)))

theorem unpaidShellCost_le_paid_final {N a q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hi : sourceIndex a q) :
    unpaidShellCost N a q ≤
      (0.0001 * (N : ℝ) / sourceL N) * (∫ alpha in shell N a q, ‖S N alpha‖ ^ 2) +
        finalShellCost N a q :=
  weighted_shell_transfer N a q _ _
    (continuous_unpaidPart (nat_pos_of_exp_le hN) a q)
    (continuous_finalPart (nat_pos_of_exp_le hN) a q)
    (fun alpha _ => norm_unpaidPart_le_paid_final hN hq hi (alpha - rationalCenter a q))

theorem unpaidCost_le_paid_final {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    unpaidCost N ≤
      (0.0001 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        finalCost N := by
  have hN0 := exp_2000_le_of_exp_3100_le hN
  unfold unpaidCost finalCost
  calc
    _ ≤ ∑ i ∈ coreIndices N,
        ((0.0001 * (N : ℝ) / sourceL N) * (∫ alpha in shell N i.2 i.1, ‖S N alpha‖ ^ 2) +
          finalShellCost N i.2 i.1) := by
      apply Finset.sum_le_sum
      intro i hi
      have hh := (mem_coreIndices hN0 i).mp hi
      exact unpaidShellCost_le_paid_final hN hh.1 hh.2
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        ← integral_M2_eq_shell_sum hN0 _ (continuous_energy N)]

theorem C_le_three_paid_final {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    weightedPacketCost N ≤
      (0.0003 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        finalCost N := by
  calc
    _ ≤ (0.0002 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        ((0.0001 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
          finalCost N) :=
      (C_le_paid_unpaid hN).trans (add_le_add le_rfl (unpaidCost_le_paid_final hN))
    _ = _ := by ring

theorem M2_integral_le_three_paid_final {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
      (0.0784 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        finalCost N := by
  calc
    _ ≤ (0.0783 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        ((0.0001 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
          finalCost N) :=
      (M2_integral_le_paid_unpaid hN).trans (add_le_add le_rfl (unpaidCost_le_paid_final hN))
    _ = _ := by ring

theorem M2_same_witness_three_paid {N : ℕ} {alpha : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (ha : alpha ∈ M2 N) :
    ∃ (q a : ℕ) (eta : ℝ), (q : ℝ) ≤ sourceP N ∧ sourceIndex a q ∧
      alpha = rationalCenter a q + eta ∧ deltaRadius N q < |eta| ∧
      |eta| ≤ 1 / ((q : ℝ) * sourceQ N) ∧
      ‖S N alpha‖ ≤ 0.0784 * (N : ℝ) / sourceL N + ‖finalPart N a q eta‖ := by
  obtain ⟨q, a, eta, hq, hi, heq, hlo, hhi, hs⟩ := M2_same_witness_reduced hN ha
  refine ⟨q, a, eta, hq, hi, heq, hlo, hhi, ?_⟩
  calc
    _ ≤ 0.0783 * (N : ℝ) / sourceL N +
        (0.0001 * (N : ℝ) / sourceL N + ‖finalPart N a q eta‖) :=
      hs.trans (add_le_add le_rfl (norm_unpaidPart_le_paid_final hN hq hi eta))
    _ = _ := by ring

theorem finalValues_literal {N q : ℕ} [NeZero q] (chi : Character q) {rho : ℂ} :
    rho ∈ finalValues chi N ↔
      chi.LFunction rho = 0 ∧ 0 < rho.re ∧ rho.re < 1 ∧ |rho.im| ≤ sourceT N ∧
      3 / 4 < rho.re ∧
        (omegaCutoff N q / 10000 < |rho.im| ∨ realCutoff N < rho.re) ∧
          wholeCutoff N < rho.re := by
  simp only [finalValues, Finset.mem_filter, unpaidValues_literal]
  tauto

theorem whole_final_disjoint {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ) :
    Disjoint (wholePaidValues chi N) (finalValues chi N) := by
  apply Finset.disjoint_left.mpr
  intro rho hl hr
  exact (not_lt_of_ge (Finset.mem_filter.mp hl).2) (Finset.mem_filter.mp hr).2

theorem unpaid_values_partition {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ) :
    unpaidValues chi N = wholePaidValues chi N ∪ finalValues chi N := by
  ext rho
  simp only [wholePaidValues, finalValues, Finset.mem_union, Finset.mem_filter]
  by_cases hb : rho.re ≤ wholeCutoff N
  · have hn : ¬ wholeCutoff N < rho.re := not_lt_of_ge hb
    simp [hb, hn]
  · have hh : wholeCutoff N < rho.re := lt_of_not_ge hb
    simp [hb, hh]

theorem four_values_partition {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ) :
    zeroValues chi (sourceT N) =
      leftValues chi N ∪ farPaidValues chi N ∪ wholePaidValues chi N ∪ finalValues chi N := by
  simp only [full_values_partition, unpaid_values_partition, Finset.union_assoc]

theorem whole_boundary_paid {N q : ℕ} [NeZero q] (chi : Character q)
    {rho : ℂ} (hr : rho ∈ unpaidValues chi N) (hb : rho.re = wholeCutoff N) :
    rho ∈ wholePaidValues chi N ∧ rho ∉ finalValues chi N := by
  constructor
  · exact Finset.mem_filter.mpr ⟨hr, hb.le⟩
  · intro hh
    exact (not_lt_of_ge hb.le) (Finset.mem_filter.mp hh).2

theorem finalShellCost_eq_values {q : ℕ} [NeZero q] (N a : ℕ) :
    finalShellCost N a q =
      ∫ alpha in shell N a q,
        ‖(q.totient : ℂ)⁻¹ * ∑ chi : Character q, CharacterExpansion.G a chi *
          ∑ rho ∈ finalValues chi N, (analyticOrderNatAt chi.LFunction rho : ℂ) *
            Jrho N rho (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2 := by
  unfold finalShellCost
  simp only [finalPart_eq, finalPacket]

theorem C_le_three_paid_shared_energy {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    weightedPacketCost N ≤ (0.0003 * (N : ℝ) / sourceL N) *
      ((∑ n ∈ windowFinset N, ArithmeticFunction.vonMangoldt n ^ 2) -
        (∫ alpha in M1 N, ‖S N alpha‖ ^ 2) -
        (∫ alpha in M3 N, ‖S N alpha‖ ^ 2) -
        (∫ alpha in M4 N, ‖S N alpha‖ ^ 2)) + finalCost N := by
  have he := minor_energy_eq_source_sub_major (exp_2000_le_of_exp_3100_le hN)
  rw [source_energy_eq] at he
  have hh : (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) =
      (∑ n ∈ windowFinset N, ArithmeticFunction.vonMangoldt n ^ 2) -
        (∫ alpha in M1 N, ‖S N alpha‖ ^ 2) -
        (∫ alpha in M3 N, ‖S N alpha‖ ^ 2) -
        (∫ alpha in M4 N, ‖S N alpha‖ ^ 2) := by linarith
  rw [← hh]
  exact C_le_three_paid_final hN

theorem M2_integral_le_4012_of_finalCost {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hz : finalCost N ≤
      (0.3228 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2)) :
    ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
      (0.4012 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) := by
  calc
    _ ≤ (0.0784 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        (0.3228 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) :=
      (M2_integral_le_three_paid_final hN).trans (add_le_add le_rfl hz)
    _ = _ := by ring

theorem lambdaTripleCount_ge_three_paid {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∫ alpha in M1 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re +
      (∫ alpha in M3 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re +
      (∫ alpha in M4 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re -
      (0.0784 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) -
      finalCost N ≤ lambdaTripleCount N := by
  have hh := lambdaTripleCount_ge_reduced hN
  have hc := unpaidCost_le_paid_final hN
  have he : (0.0784 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) =
      (0.0783 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        (0.0001 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) := by ring
  linarith only [hh, hc, he]

end LiuWang.Proof.NearArcPayment.Continuation
