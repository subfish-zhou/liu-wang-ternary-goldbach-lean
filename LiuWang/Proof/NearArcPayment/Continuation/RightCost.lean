import LiuWang.Proof.NearArcPayment.Continuation.LeftStrip

/-!
# Payment into the frozen C(N)

The numerical left-strip payment is integrated against the actual shell
energy. No independent full-circle account is introduced. The remaining
right-strip cost keeps the signed Gauss sum inside its norm.
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

def rightPart (N a q : ℕ) (eta : ℝ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    rightPacket q N a eta

theorem rightPart_eq {q : ℕ} [NeZero q] (N a : ℕ) (eta : ℝ) :
    rightPart N a q eta = rightPacket q N a eta := by
  simp only [rightPart, dif_neg (NeZero.ne q)]

theorem continuous_rightPart {N : ℕ} (hN : 0 < N) (a q : ℕ) :
    Continuous (rightPart N a q) := by
  by_cases hq : q = 0
  · subst q
    change Continuous (fun _ : ℝ => (0 : ℂ))
    exact continuous_const
  · let : NeZero q := ⟨hq⟩
    simp only [funext (rightPart_eq N a)]
    unfold rightPacket
    exact continuous_const.mul (continuous_finsetSum _ (fun chi _ =>
      continuous_const.mul (continuous_finsetSum _ (fun rho _ =>
        continuous_const.mul (SingularIntegral.Jrho_continuous hN rho)))))

theorem packet_sub_rightPart {q : ℕ} [NeZero q] (N a : ℕ) (eta : ℝ)
    (hi : sourceIndex a q) :
    packet N a q eta - rightPart N a q eta = leftPacket q N a eta := by
  rw [packet_eq, rightPart_eq, zeroPacket_eq_left_add_right N a eta hi]
  abel

theorem norm_packet_le_paid_right {N a q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hi : sourceIndex a q) (eta : ℝ) :
    ‖packet N a q eta‖ ≤ 0.0001 * (N : ℝ) / sourceL N + ‖rightPart N a q eta‖ := by
  let : NeZero q := ⟨Nat.ne_of_gt (sourceIndex_den_pos hi)⟩
  have hb := norm_leftPacket_le_paid (a := a) hN hq eta
  rw [← packet_sub_rightPart N a eta hi] at hb
  exact (norm_le_norm_sub_add _ _).trans (add_le_add hb le_rfl)

def rightShellCost (N a q : ℕ) : ℝ :=
  ∫ alpha in shell N a q,
    ‖rightPart N a q (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2

def rightCost (N : ℕ) : ℝ :=
  ∑ i ∈ coreIndices N, rightShellCost N i.2 i.1

theorem rightShellCost_nonneg (N a q : ℕ) : 0 ≤ rightShellCost N a q :=
  integral_nonneg (fun _ => mul_nonneg (norm_nonneg _) (sq_nonneg _))

theorem rightCost_nonneg (N : ℕ) : 0 ≤ rightCost N :=
  Finset.sum_nonneg (fun i _ => rightShellCost_nonneg N i.2 i.1)

theorem shellZeroCost_le_paid_right {N a q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hi : sourceIndex a q) :
    shellZeroCost N a q ≤
      (0.0001 * (N : ℝ) / sourceL N) * (∫ alpha in shell N a q, ‖S N alpha‖ ^ 2) +
        rightShellCost N a q := by
  have hn := nat_pos_of_exp_le hN
  have he := (continuous_energy N).integrableOn_Icc
    (μ := volume) (a := rationalCenter a q - 1 / ((q : ℝ) * sourceQ N))
    (b := rationalCenter a q + 1 / ((q : ℝ) * sourceQ N))
  have he' := he.mono_set (show shell N a q ⊆ approximationArc N a q from Set.sdiff_subset)
  have hp' : IntegrableOn (fun alpha : ℝ =>
      ‖packet N a q (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2) (shell N a q) :=
    (((continuous_packet hn a q).comp
      (continuous_id.sub continuous_const)).norm.mul
        (continuous_energy N)).integrableOn_Icc.mono_set Set.sdiff_subset
  have hr' : IntegrableOn (fun alpha : ℝ =>
      ‖rightPart N a q (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2) (shell N a q) :=
    (((continuous_rightPart hn a q).comp
      (continuous_id.sub continuous_const)).norm.mul
        (continuous_energy N)).integrableOn_Icc.mono_set Set.sdiff_subset
  unfold shellZeroCost rightShellCost
  calc
    _ ≤ ∫ alpha in shell N a q,
        (0.0001 * (N : ℝ) / sourceL N) * ‖S N alpha‖ ^ 2 +
          ‖rightPart N a q (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2 := by
      apply setIntegral_mono_on hp' ((he'.const_mul _).add hr') (measurableSet_shell N a q)
      intro alpha _
      simpa only [add_mul, Pi.add_apply] using
        mul_le_mul_of_nonneg_right (norm_packet_le_paid_right hN hq hi
          (alpha - rationalCenter a q)) (sq_nonneg ‖S N alpha‖)
    _ = _ := by rw [integral_add (he'.const_mul _) hr', integral_const_mul]

theorem weightedPacketCost_le_paid_right {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    weightedPacketCost N ≤
      (0.0001 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        rightCost N := by
  have hN0 := exp_2000_le_of_exp_3100_le hN
  unfold weightedPacketCost rightCost
  calc
    _ ≤ ∑ i ∈ coreIndices N,
        ((0.0001 * (N : ℝ) / sourceL N) *
          (∫ alpha in shell N i.2 i.1, ‖S N alpha‖ ^ 2) + rightShellCost N i.2 i.1) := by
      apply Finset.sum_le_sum
      intro i hi
      have hh := (mem_coreIndices hN0 i).mp hi
      exact shellZeroCost_le_paid_right hN hh.1 hh.2
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        ← integral_M2_eq_shell_sum hN0 _ (continuous_energy N)]

theorem M2_integral_le_paid_right {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
      (0.0782 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        rightCost N := by
  have hb := M2_integral_le_paid_weighted_packet hN
  have hr := weightedPacketCost_le_paid_right hN
  calc
    _ ≤ (0.0781 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        ((0.0001 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
          rightCost N) := hb.trans (add_le_add le_rfl hr)
    _ = _ := by ring

theorem M2_integral_le_4012_of_rightCost {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hr : rightCost N ≤
      (0.3230 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2)) :
    ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
      (0.4012 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) := by
  calc
    _ ≤ (0.0782 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        (0.3230 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) :=
      (M2_integral_le_paid_right hN).trans (add_le_add le_rfl hr)
    _ = _ := by ring

end LiuWang.Proof.NearArcPayment.Continuation
