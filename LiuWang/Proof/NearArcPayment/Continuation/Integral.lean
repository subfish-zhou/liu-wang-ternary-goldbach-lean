import LiuWang.Proof.NearArcPayment.Continuation.FarBand

/-!
# The reduced actual C(N), after both independent payments

The real band is already included in the far-paid packet; only two payments
are charged: the fixed left strip, and the low-height right strip. All
remaining values retain the original Gauss signs and analytic multiplicity.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearArcPayment.Continuation

open Interfaces Parameters ArcGeometry CompleteExpansion
open MajorArcApproximation MinorArcEnergy
open AnalyticNumberTheory.LargeSieve

def unpaidPart (N a q : ℕ) (eta : ℝ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    unpaidPacket q N a eta

theorem unpaidPart_eq {q : ℕ} [NeZero q] (N a : ℕ) (eta : ℝ) :
    unpaidPart N a q eta = unpaidPacket q N a eta := by
  simp only [unpaidPart, dif_neg (NeZero.ne q)]

theorem continuous_unpaidPart {N : ℕ} (hN : 0 < N) (a q : ℕ) :
    Continuous (unpaidPart N a q) := by
  by_cases hq : q = 0
  · subst q
    change Continuous (fun _ : ℝ => (0 : ℂ))
    exact continuous_const
  · let : NeZero q := ⟨hq⟩
    simp only [funext (unpaidPart_eq N a)]
    unfold unpaidPacket
    exact continuous_const.mul (continuous_finsetSum _ (fun chi _ =>
      continuous_const.mul (continuous_finsetSum _ (fun rho _ =>
        continuous_const.mul (SingularIntegral.Jrho_continuous hN rho)))))

theorem norm_rightPart_le_paid_unpaid {N a q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hi : sourceIndex a q) {eta : ℝ} (he : deltaRadius N q < |eta|) :
    ‖rightPart N a q eta‖ ≤
      0.0001 * (N : ℝ) / sourceL N + ‖unpaidPart N a q eta‖ := by
  let : NeZero q := ⟨Nat.ne_of_gt (sourceIndex_den_pos hi)⟩
  rw [rightPart_eq, unpaidPart_eq, rightPacket_eq_far_add_unpaid]
  exact (norm_add_le _ _).trans (add_le_add (norm_farPaidPacket_le_paid hN hq he) le_rfl)

def unpaidShellCost (N a q : ℕ) : ℝ :=
  ∫ alpha in shell N a q,
    ‖unpaidPart N a q (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2

def unpaidCost (N : ℕ) : ℝ :=
  ∑ i ∈ coreIndices N, unpaidShellCost N i.2 i.1

theorem unpaidCost_nonneg (N : ℕ) : 0 ≤ unpaidCost N :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg
    (fun _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)))

theorem weighted_shell_transfer (N a q : ℕ) (F G : ℝ → ℂ) (hF : Continuous F)
    (hG : Continuous G) {B : ℝ}
    (hpoint : ∀ alpha ∈ shell N a q,
      ‖F (alpha - rationalCenter a q)‖ ≤ B + ‖G (alpha - rationalCenter a q)‖) :
    (∫ alpha in shell N a q, ‖F (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2) ≤
      B * (∫ alpha in shell N a q, ‖S N alpha‖ ^ 2) +
        ∫ alpha in shell N a q, ‖G (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2 := by
  have he : IntegrableOn (fun alpha : ℝ => ‖S N alpha‖ ^ 2) (shell N a q) :=
    (continuous_energy N).integrableOn_Icc.mono_set Set.sdiff_subset
  have hf : IntegrableOn (fun alpha : ℝ =>
      ‖F (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2) (shell N a q) :=
    ((hF.comp (continuous_id.sub continuous_const)).norm.mul
      (continuous_energy N)).integrableOn_Icc.mono_set Set.sdiff_subset
  have hg : IntegrableOn (fun alpha : ℝ =>
      ‖G (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2) (shell N a q) :=
    ((hG.comp (continuous_id.sub continuous_const)).norm.mul
      (continuous_energy N)).integrableOn_Icc.mono_set Set.sdiff_subset
  calc
    _ ≤ ∫ alpha in shell N a q,
        B * ‖S N alpha‖ ^ 2 + ‖G (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2 := by
      apply setIntegral_mono_on hf ((he.const_mul B).add hg) (measurableSet_shell N a q)
      intro alpha ha
      simpa only [add_mul, Pi.add_apply] using
        mul_le_mul_of_nonneg_right (hpoint alpha ha) (sq_nonneg ‖S N alpha‖)
    _ = _ := by rw [integral_add (he.const_mul B) hg, integral_const_mul]

theorem rightShellCost_le_paid_unpaid {N a q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hi : sourceIndex a q) :
    rightShellCost N a q ≤
      (0.0001 * (N : ℝ) / sourceL N) * (∫ alpha in shell N a q, ‖S N alpha‖ ^ 2) +
        unpaidShellCost N a q :=
  weighted_shell_transfer N a q _ _
    (continuous_rightPart (nat_pos_of_exp_le hN) a q)
    (continuous_unpaidPart (nat_pos_of_exp_le hN) a q)
    (fun _ ha => norm_rightPart_le_paid_unpaid hN hq hi (shell_same_eta hq hi ha).1)

theorem rightCost_le_paid_unpaid {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    rightCost N ≤
      (0.0001 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        unpaidCost N := by
  have hN0 := exp_2000_le_of_exp_3100_le hN
  unfold rightCost unpaidCost
  calc
    _ ≤ ∑ i ∈ coreIndices N,
        ((0.0001 * (N : ℝ) / sourceL N) * (∫ alpha in shell N i.2 i.1, ‖S N alpha‖ ^ 2) +
          unpaidShellCost N i.2 i.1) := by
      apply Finset.sum_le_sum
      intro i hi
      have hh := (mem_coreIndices hN0 i).mp hi
      exact rightShellCost_le_paid_unpaid hN hh.1 hh.2
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        ← integral_M2_eq_shell_sum hN0 _ (continuous_energy N)]

theorem C_le_paid_unpaid {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    weightedPacketCost N ≤
      (0.0002 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        unpaidCost N := by
  calc
    _ ≤ (0.0001 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        ((0.0001 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
          unpaidCost N) :=
      (weightedPacketCost_le_paid_right hN).trans
        (add_le_add le_rfl (rightCost_le_paid_unpaid hN))
    _ = _ := by ring

theorem M2_integral_le_paid_unpaid {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
      (0.0783 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        unpaidCost N := by
  calc
    _ ≤ (0.0781 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        ((0.0002 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
          unpaidCost N) :=
      (M2_integral_le_paid_weighted_packet hN).trans (add_le_add le_rfl (C_le_paid_unpaid hN))
    _ = _ := by ring

theorem unpaidValues_literal {N q : ℕ} [NeZero q] (chi : Character q) {rho : ℂ} :
    rho ∈ unpaidValues chi N ↔
      chi.LFunction rho = 0 ∧ 0 < rho.re ∧ rho.re < 1 ∧ |rho.im| ≤ sourceT N ∧
      3 / 4 < rho.re ∧
        (omegaCutoff N q / 10000 < |rho.im| ∨ realCutoff N < rho.re) := by
  simp only [unpaidValues, rightValues, Finset.mem_filter, mem_zeroValues]
  constructor
  · rintro ⟨⟨⟨hz, h0, h1, ht, _⟩, hb⟩, hu⟩
    refine ⟨hz, h0, h1, ht, hb, ?_⟩
    by_cases hh : |rho.im| ≤ omegaCutoff N q / 10000
    · exact Or.inr (lt_of_not_ge (fun hc => hu ⟨hh, hc⟩))
    · exact Or.inl (lt_of_not_ge hh)
  · rintro ⟨hz, h0, h1, ht, hb, hu⟩
    refine ⟨⟨⟨hz, h0, h1, ht, by linarith⟩, hb⟩, ?_⟩
    intro hh
    rcases hu with hu | hu
    · exact (not_lt_of_ge hh.1) hu
    · exact (not_lt_of_ge hh.2) hu

theorem M2_same_witness_reduced {N : ℕ} {alpha : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (ha : alpha ∈ M2 N) :
    ∃ (q a : ℕ) (eta : ℝ), (q : ℝ) ≤ sourceP N ∧ sourceIndex a q ∧
      alpha = rationalCenter a q + eta ∧ deltaRadius N q < |eta| ∧
      |eta| ≤ 1 / ((q : ℝ) * sourceQ N) ∧
      ‖S N alpha‖ ≤ 0.0783 * (N : ℝ) / sourceL N + ‖unpaidPart N a q eta‖ := by
  obtain ⟨q, a, eta, hq, hi, heq, hlo, hhi⟩ := M2_eta_range ha
  let : NeZero q := ⟨Nat.ne_of_gt (sourceIndex_den_pos hi)⟩
  refine ⟨q, a, eta, hq, hi, heq, hlo, hhi, ?_⟩
  have hs := S_le_paid_and_packet (exp_2000_le_of_exp_3100_le hN) hi hq hlo hhi
  have hp := paid_terms_le hN (sourceIndex_den_pos hi) hq
  have hl := norm_packet_le_paid_right hN hq hi eta
  have hr := norm_rightPart_le_paid_unpaid hN hq hi hlo
  rw [packet_eq] at hl
  rw [heq]
  calc
    _ ≤ 0.0781 * (N : ℝ) / sourceL N +
        (0.0001 * (N : ℝ) / sourceL N +
          (0.0001 * (N : ℝ) / sourceL N + ‖unpaidPart N a q eta‖)) :=
      hs.trans (add_le_add hp (hl.trans (add_le_add le_rfl hr)))
    _ = _ := by ring

theorem M2_integral_le_4012_of_unpaidCost {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hz : unpaidCost N ≤
      (0.3229 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2)) :
    ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
      (0.4012 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) := by
  calc
    _ ≤ (0.0783 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        (0.3229 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) :=
      (M2_integral_le_paid_unpaid hN).trans (add_le_add le_rfl hz)
    _ = _ := by ring

theorem lambdaTripleCount_ge_reduced {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∫ alpha in M1 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re +
      (∫ alpha in M3 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re +
      (∫ alpha in M4 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re -
      (0.0783 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) -
      unpaidCost N ≤ lambdaTripleCount N := by
  have hh := lambdaTripleCount_ge_M2_paid hN
  have hc := C_le_paid_unpaid hN
  have he : (0.0783 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) =
      (0.0781 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        (0.0002 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) := by ring
  linarith only [hh, hc, he]

end LiuWang.Proof.NearArcPayment.Continuation
