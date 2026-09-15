import LiuWang.Proof.NearArcPayment.Continuation.Frontier.FinalIntegral

/-! 真正新支持、反号保留、实零点保留、闭端点及单份共享能量。 -/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearArcPayment.Continuation.Frontier

open Interfaces Parameters ArcGeometry CompleteExpansion
open MajorArcApproximation MinorArcEnergy

theorem cutoff_chain {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    wholeCutoff N < squareCutoff N ∧ squareCutoff N < alignedCutoff N ∧
      alignedCutoff N < 1 := by
  have hL := sourceL_pos hN
  have hl : 0 < Real.log (sourceL N) :=
    Real.log_pos (by linarith [sourceL_ge_2000 hN])
  have hp : 0 < Real.log (sourceL N) / sourceL N := div_pos hl hL
  unfold wholeCutoff squareCutoff alignedCutoff
  constructor
  · rw [mul_div_assoc, mul_div_assoc]
    linarith
  constructor <;> simp only [mul_div_assoc] <;> linarith

theorem square_opposite {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) {chi : Character q} {rho : ℂ}
    {positive : Bool} (hr : rho ∈ squareValues chi N positive) :
    if positive then rho.im < 0 else 0 < rho.im := by
  obtain ⟨hr, hl, hu, hb⟩ := Finset.mem_filter.mp hr
  have hn := (Finset.mem_filter.mp hr).2
  have hb' := hb.trans (cutoff_chain hN).2.1.le
  have hg : rho.im ≠ 0 := abs_pos.mp ((pow_pos (sourceL_pos hN) 4).trans_le hl)
  cases positive
  · have hh : ¬ rho.im < 0 := fun hh => hn ⟨hl, hu, hb', hh⟩
    exact lt_of_le_of_ne (le_of_not_gt hh) (Ne.symm hg)
  · have hh : ¬ 0 < rho.im := fun hh => hn ⟨hl, hu, hb', hh⟩
    exact lt_of_le_of_ne (le_of_not_gt hh) hg

theorem final_values_partition {N q : ℕ} [NeZero q]
    (chi : Character q) (positive : Bool) :
    finalValues chi N =
      alignedValues chi N positive ∪ squareValues chi N positive ∪ tailValues chi N positive := by
  ext rho
  simp only [alignedValues, remainingValues, squareValues, tailValues,
    Finset.mem_union, Finset.mem_filter]
  tauto

theorem aligned_square_disjoint {N q : ℕ} [NeZero q]
    (chi : Character q) (positive : Bool) :
    Disjoint (alignedValues chi N positive) (squareValues chi N positive) := by
  apply Finset.disjoint_left.mpr
  intro rho ha hs
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).2 (Finset.mem_filter.mp ha).2

theorem square_tail_disjoint {N q : ℕ} [NeZero q]
    (chi : Character q) (positive : Bool) :
    Disjoint (squareValues chi N positive) (tailValues chi N positive) := by
  apply Finset.disjoint_left.mpr
  intro rho hs ht
  exact (Finset.mem_filter.mp ht).2 (Finset.mem_filter.mp hs).2

theorem aligned_tail_disjoint {N q : ℕ} [NeZero q]
    (chi : Character q) (positive : Bool) :
    Disjoint (alignedValues chi N positive) (tailValues chi N positive) := by
  apply Finset.disjoint_left.mpr
  intro rho ha ht
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).2 (Finset.mem_filter.mp ha).2

theorem real_values_retained {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (chi : Character q) (positive : Bool)
    {rho : ℂ} (hg : rho.im = 0) :
    rho ∈ tailValues chi N positive ↔ rho ∈ finalValues chi N := by
  have hl : ¬ sourceL N ^ 4 ≤ |rho.im| := by
    rw [hg, abs_zero]
    exact not_le_of_gt (pow_pos (sourceL_pos hN) 4)
  simp only [tailValues, remainingValues, Finset.mem_filter, hl, false_and, not_false_eq_true,
    and_true]

theorem aligned_boundary_paid {N q : ℕ} [NeZero q]
    (chi : Character q) (positive : Bool) {rho : ℂ} (hr : rho ∈ finalValues chi N)
    (hl : sourceL N ^ 4 ≤ |rho.im|) (hu : |rho.im| ≤ sourceL N ^ 8)
    (hb : rho.re = alignedCutoff N)
    (hs : if positive then 0 < rho.im else rho.im < 0) :
    rho ∈ alignedValues chi N positive ∧ rho ∉ remainingValues chi N positive := by
  constructor
  · exact Finset.mem_filter.mpr ⟨hr, hl, hu, hb.le, hs⟩
  · intro hh
    exact (Finset.mem_filter.mp hh).2 ⟨hl, hu, hb.le, hs⟩

theorem square_boundary_paid {N q : ℕ} [NeZero q]
    (chi : Character q) (positive : Bool) {rho : ℂ} (hr : rho ∈ remainingValues chi N positive)
    (hl : sourceL N ^ 4 ≤ |rho.im|) (hu : |rho.im| ≤ sourceL N ^ 8)
    (hb : rho.re = squareCutoff N) :
    rho ∈ squareValues chi N positive ∧ rho ∉ tailValues chi N positive := by
  constructor
  · exact Finset.mem_filter.mpr ⟨hr, hl, hu, hb.le⟩
  · intro hh
    exact (Finset.mem_filter.mp hh).2 ⟨hl, hu, hb.le⟩

theorem tailValues_literal {N q : ℕ} [NeZero q]
    (chi : Character q) (positive : Bool) {rho : ℂ} :
    rho ∈ tailValues chi N positive ↔
      chi.LFunction rho = 0 ∧ 0 < rho.re ∧ rho.re < 1 ∧ |rho.im| ≤ sourceT N ∧
      3 / 4 < rho.re ∧ (omegaCutoff N q / 10000 < |rho.im| ∨ realCutoff N < rho.re) ∧
      wholeCutoff N < rho.re ∧
      ¬ (sourceL N ^ 4 ≤ |rho.im| ∧ |rho.im| ≤ sourceL N ^ 8 ∧
        rho.re ≤ alignedCutoff N ∧ if positive then 0 < rho.im else rho.im < 0) ∧
      ¬ (sourceL N ^ 4 ≤ |rho.im| ∧ |rho.im| ≤ sourceL N ^ 8 ∧
        rho.re ≤ squareCutoff N) := by
  simp only [tailValues, remainingValues, Finset.mem_filter, finalValues_literal]
  tauto

theorem selectedTail_eq_values {q : ℕ} [NeZero q] (N a : ℕ) (eta : ℝ) :
    selectedTail N a q eta =
      (q.totient : ℂ)⁻¹ * ∑ chi : Character q, CharacterExpansion.G a chi *
        ∑ rho ∈ tailValues chi N (if 0 ≤ eta then true else false),
          (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta := by
  by_cases he : 0 ≤ eta <;> simp [selectedTail, signedTail_eq, tailPacket, he]

theorem frontierShellCost_eq_values {q : ℕ} [NeZero q] (N a : ℕ) :
    frontierShellCost N a q =
      ∫ alpha in shell N a q,
        ‖(q.totient : ℂ)⁻¹ * ∑ chi : Character q, CharacterExpansion.G a chi *
          ∑ rho ∈ tailValues chi N (if 0 ≤ alpha - rationalCenter a q then true else false),
            (analyticOrderNatAt chi.LFunction rho : ℂ) *
              Jrho N rho (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2 := by
  unfold frontierShellCost
  simp only [selectedTail_eq_values]

theorem M2_eta_nonzero {N a q : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    (hq : (q : ℝ) ≤ sourceP N) (hi : sourceIndex a q)
    {alpha : ℝ} (ha : alpha ∈ shell N a q) :
    alpha - rationalCenter a q ≠ 0 :=
  abs_pos.mp ((deltaRadius_pos hN (sourceIndex_den_pos hi)).trans (shell_same_eta hq hi ha).1)

theorem opposite_phase_can_cancel :
    (-2 * Real.pi) + 2 * Real.pi * (1 : ℝ) * 1 = 0 := by ring

theorem finalCost_le_two_paid_shared_energy {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    finalCost N ≤ (0.0002 * (N : ℝ) / sourceL N) *
      ((∑ n ∈ windowFinset N, ArithmeticFunction.vonMangoldt n ^ 2) -
        (∫ alpha in M1 N, ‖S N alpha‖ ^ 2) -
        (∫ alpha in M3 N, ‖S N alpha‖ ^ 2) -
        (∫ alpha in M4 N, ‖S N alpha‖ ^ 2)) + frontierCost N := by
  have he := minor_energy_eq_source_sub_major (exp_2000_le_of_exp_3100_le hN)
  rw [source_energy_eq] at he
  have hh : (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) =
      (∑ n ∈ windowFinset N, ArithmeticFunction.vonMangoldt n ^ 2) -
        (∫ alpha in M1 N, ‖S N alpha‖ ^ 2) -
        (∫ alpha in M3 N, ‖S N alpha‖ ^ 2) -
        (∫ alpha in M4 N, ‖S N alpha‖ ^ 2) := by linarith
  rw [← hh]
  exact finalCost_le_two_paid_frontier hN

end LiuWang.Proof.NearArcPayment.Continuation.Frontier
