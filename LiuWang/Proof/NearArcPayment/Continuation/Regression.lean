import LiuWang.Proof.NearArcPayment.Continuation.Integral

/-! Exact support endpoints and the single shared energy account. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearArcPayment.Continuation

open Interfaces Parameters CompleteExpansion MajorArcApproximation MinorArcEnergy

theorem realCutoff_lt_one {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    realCutoff N < 1 := by
  have hl : 0 < Real.log (sourceL N) :=
    Real.log_pos (by linarith [sourceL_ge_2000 hN])
  have hw : 0 < Real.log (0.001 * (N : ℝ)) := Real.log_pos (sourceWindow_gt_one hN)
  unfold realCutoff
  have hh : 0 < 10 * Real.log (sourceL N) / Real.log (0.001 * (N : ℝ)) := by positivity
  linarith

theorem left_right_disjoint {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ) :
    Disjoint (leftValues chi N) (rightValues chi N) := by
  apply Finset.disjoint_left.mpr
  intro rho hl hr
  exact (not_lt_of_ge (Finset.mem_filter.mp hl).2) (Finset.mem_filter.mp hr).2

theorem far_unpaid_disjoint {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ) :
    Disjoint (farPaidValues chi N) (unpaidValues chi N) := by
  apply Finset.disjoint_left.mpr
  intro rho hl hr
  exact (Finset.mem_filter.mp hr).2 (Finset.mem_filter.mp hl).2

theorem full_values_partition {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ) :
    zeroValues chi (sourceT N) =
      leftValues chi N ∪ farPaidValues chi N ∪ unpaidValues chi N := by
  ext rho
  simp only [leftValues, farPaidValues, unpaidValues, rightValues,
    Finset.mem_union, Finset.mem_filter]
  by_cases hl : rho.re ≤ 3 / 4
  · have hb : ¬ 3 / 4 < rho.re := not_lt_of_ge hl
    simp [hl, hb]
  · have hb : 3 / 4 < rho.re := lt_of_not_ge hl
    by_cases hf : |rho.im| ≤ omegaCutoff N q / 10000 ∧ rho.re ≤ realCutoff N <;>
      simp [hl, hb, hf]

theorem three_quarters_paid {N q : ℕ} [NeZero q] (chi : Character q)
    {rho : ℂ} (hr : rho ∈ zeroValues chi (sourceT N)) (hb : rho.re = 3 / 4) :
    rho ∈ leftValues chi N ∧ rho ∉ rightValues chi N := by
  constructor
  · exact Finset.mem_filter.mpr ⟨hr, hb.le⟩
  · intro hh
    have hl := (Finset.mem_filter.mp hh).2
    linarith

theorem far_boundary_paid {N q : ℕ} [NeZero q] (chi : Character q)
    {rho : ℂ} (hr : rho ∈ rightValues chi N)
    (hh : |rho.im| = omegaCutoff N q / 10000) (hb : rho.re = realCutoff N) :
    rho ∈ farPaidValues chi N ∧ rho ∉ unpaidValues chi N := by
  constructor
  · exact Finset.mem_filter.mpr ⟨hr, hh.le, hb.le⟩
  · intro hu
    exact (Finset.mem_filter.mp hu).2 ⟨hh.le, hb.le⟩

theorem unpaidShellCost_eq_values {q : ℕ} [NeZero q] (N a : ℕ) :
    unpaidShellCost N a q =
      ∫ alpha in shell N a q,
        ‖(q.totient : ℂ)⁻¹ * ∑ chi : Character q, CharacterExpansion.G a chi *
          ∑ rho ∈ unpaidValues chi N, (analyticOrderNatAt chi.LFunction rho : ℂ) *
            Jrho N rho (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2 := by
  unfold unpaidShellCost
  simp only [unpaidPart_eq, unpaidPacket]

theorem unpaid_modulus_one (N a : ℕ) (eta : ℝ) :
    unpaidPart N a 1 eta =
      ∑ rho ∈ unpaidValues (1 : Character 1) N,
        (analyticOrderNatAt (1 : Character 1).LFunction rho : ℂ) * Jrho N rho eta := by
  rw [unpaidPart_eq]
  unfold unpaidPacket
  rw [Fintype.sum_subsingleton _ (1 : Character 1),
    NonprincipalPacket.G_one_eq_moebius (Nat.coprime_one_right a)]
  simp

theorem C_le_paid_shared_energy {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    weightedPacketCost N ≤ (0.0002 * (N : ℝ) / sourceL N) *
      ((∑ n ∈ windowFinset N, ArithmeticFunction.vonMangoldt n ^ 2) -
        (∫ alpha in M1 N, ‖S N alpha‖ ^ 2) -
        (∫ alpha in M3 N, ‖S N alpha‖ ^ 2) -
        (∫ alpha in M4 N, ‖S N alpha‖ ^ 2)) + unpaidCost N := by
  have he := minor_energy_eq_source_sub_major (exp_2000_le_of_exp_3100_le hN)
  rw [source_energy_eq] at he
  have hh : (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) =
      (∑ n ∈ windowFinset N, ArithmeticFunction.vonMangoldt n ^ 2) -
        (∫ alpha in M1 N, ‖S N alpha‖ ^ 2) -
        (∫ alpha in M3 N, ‖S N alpha‖ ^ 2) -
        (∫ alpha in M4 N, ‖S N alpha‖ ^ 2) := by linarith
  rw [← hh]
  exact C_le_paid_unpaid hN

end LiuWang.Proof.NearArcPayment.Continuation
