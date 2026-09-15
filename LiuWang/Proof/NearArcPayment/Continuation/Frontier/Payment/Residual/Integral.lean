import LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual.RealPacket

/-! 整实零余族接入原 lastCost，并在合账前保留旧高尾与实零的多项式母费用。 -/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual

open Interfaces Parameters ArcGeometry CompleteExpansion MajorArcApproximation MinorArcEnergy
open AnalyticNumberTheory.LargeSieve

def afterRealPart (N a q : ℕ) (positive : Bool) (eta : ℝ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    realPacketOn q a (fun chi => afterRealValues chi N positive) N eta

theorem afterRealPart_eq {q : ℕ} [NeZero q] (N a : ℕ) (positive : Bool) (eta : ℝ) :
    afterRealPart N a q positive eta =
      realPacketOn q a (fun chi => afterRealValues chi N positive) N eta := by
  simp only [afterRealPart, dif_neg (NeZero.ne q)]

def selectedAfterReal (N a q : ℕ) (eta : ℝ) : ℂ :=
  if 0 ≤ eta then afterRealPart N a q true eta else afterRealPart N a q false eta

theorem continuous_afterRealPart {N : ℕ} (hN : 0 < N) (a q : ℕ) (positive : Bool) :
    Continuous (afterRealPart N a q positive) := by
  by_cases hq : q = 0
  · subst q
    change Continuous (fun _ : ℝ => (0 : ℂ))
    exact continuous_const
  · let : NeZero q := ⟨hq⟩
    simp only [funext (afterRealPart_eq N a positive)]
    unfold realPacketOn
    exact continuous_const.mul (continuous_finsetSum _ (fun chi _ =>
      continuous_const.mul (continuous_finsetSum _ (fun rho _ =>
        continuous_const.mul (SingularIntegral.Jrho_continuous hN rho)))))

theorem norm_selectedLast_le_paid_afterReal {N a q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hi : sourceIndex a q) {eta : ℝ}
    (he : deltaRadius N q < |eta|) :
    ‖selectedLast N a q eta‖ ≤
      (423 / 8000 : ℝ) * (N : ℝ) / sourceL N + ‖selectedAfterReal N a q eta‖ := by
  let : NeZero q := ⟨Nat.ne_of_gt (sourceIndex_den_pos hi)⟩
  have hh (positive : Bool) :
      ‖lastPart N a q positive eta‖ ≤
        (423 / 8000 : ℝ) * (N : ℝ) / sourceL N + ‖afterRealPart N a q positive eta‖ := by
    rw [lastPart_eq, afterRealPart_eq, lastPacket_eq_real_add_after N a positive]
    exact (norm_add_le _ _).trans (add_le_add (norm_allRealPacket hN positive he) le_rfl)
  unfold selectedLast selectedAfterReal
  split_ifs
  · exact hh true
  · exact hh false

theorem norm_selectedResidual_le_polynomial_last {N a q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hi : sourceIndex a q) {eta : ℝ}
    (he : deltaRadius N q < |eta|) :
    ‖selectedResidual N a q eta‖ ≤
      21 * (N : ℝ) / sourceL N ^ 2 + ‖selectedLast N a q eta‖ := by
  let : NeZero q := ⟨Nat.ne_of_gt (sourceIndex_den_pos hi)⟩
  have hh (positive : Bool) :
      ‖residualPart N a q positive eta‖ ≤
        21 * (N : ℝ) / sourceL N ^ 2 + ‖lastPart N a q positive eta‖ := by
    rw [residualPart_eq, lastPart_eq, residualPacket_eq_real_add_last N a positive]
    exact (norm_add_le _ _).trans (add_le_add
      (norm_realPacket_le_polynomial (exp_2000_le_of_exp_3100_le hN) positive he) le_rfl)
  unfold selectedResidual selectedLast
  split_ifs
  · exact hh true
  · exact hh false

def afterRealShellCost (N a q : ℕ) : ℝ :=
  ∫ alpha in shell N a q,
    ‖selectedAfterReal N a q (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2

def afterRealCost (N : ℕ) : ℝ :=
  ∑ i ∈ coreIndices N, afterRealShellCost N i.2 i.1

theorem integrable_afterReal_weight {N : ℕ} (hN : 0 < N) (a q : ℕ) :
    IntegrableOn (fun alpha : ℝ =>
      ‖selectedAfterReal N a q (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2) (shell N a q) :=
  integrable_selected_weight a q _ _
    (continuous_afterRealPart hN a q true) (continuous_afterRealPart hN a q false)

theorem afterRealCost_nonneg (N : ℕ) : 0 ≤ afterRealCost N :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg
    (fun _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)))

theorem lastShellCost_le_paid_afterReal {N a q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) (hi : sourceIndex a q) :
    lastShellCost N a q ≤
      ((423 / 8000 : ℝ) * (N : ℝ) / sourceL N) *
        (∫ alpha in shell N a q, ‖S N alpha‖ ^ 2) + afterRealShellCost N a q := by
  have he : IntegrableOn (fun alpha : ℝ => ‖S N alpha‖ ^ 2) (shell N a q) :=
    (continuous_energy N).integrableOn_Icc.mono_set Set.sdiff_subset
  have hf := integrable_last_weight (nat_pos_of_exp_le hN) a q
  have hg := integrable_afterReal_weight (nat_pos_of_exp_le hN) a q
  unfold lastShellCost afterRealShellCost
  calc
    _ ≤ ∫ alpha in shell N a q,
        ((423 / 8000 : ℝ) * (N : ℝ) / sourceL N) * ‖S N alpha‖ ^ 2 +
          ‖selectedAfterReal N a q (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2 := by
      apply setIntegral_mono_on hf ((he.const_mul _).add hg) (measurableSet_shell N a q)
      intro alpha ha
      simpa only [add_mul, Pi.add_apply] using mul_le_mul_of_nonneg_right
        (norm_selectedLast_le_paid_afterReal hN hi (shell_same_eta hq hi ha).1)
        (sq_nonneg ‖S N alpha‖)
    _ = _ := by rw [integral_add (he.const_mul _) hg, integral_const_mul]

theorem lastCost_le_paid_afterReal {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    lastCost N ≤ ((423 / 8000 : ℝ) * (N : ℝ) / sourceL N) *
      (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) + afterRealCost N := by
  have hN0 := exp_2000_le_of_exp_3100_le hN
  unfold lastCost afterRealCost
  calc
    _ ≤ ∑ i ∈ coreIndices N,
        (((423 / 8000 : ℝ) * (N : ℝ) / sourceL N) *
          (∫ alpha in shell N i.2 i.1, ‖S N alpha‖ ^ 2) + afterRealShellCost N i.2 i.1) := by
      apply Finset.sum_le_sum
      intro i hi
      have hh := (mem_coreIndices hN0 i).mp hi
      exact lastShellCost_le_paid_afterReal hN hh.1 hh.2
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        ← integral_M2_eq_shell_sum hN0 _ (continuous_energy N)]

theorem residualShellCost_le_polynomial_last {N a q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) (hi : sourceIndex a q) :
    residualShellCost N a q ≤
      (21 * (N : ℝ) / sourceL N ^ 2) * (∫ alpha in shell N a q, ‖S N alpha‖ ^ 2) +
        lastShellCost N a q := by
  have he : IntegrableOn (fun alpha : ℝ => ‖S N alpha‖ ^ 2) (shell N a q) :=
    (continuous_energy N).integrableOn_Icc.mono_set Set.sdiff_subset
  have hf := integrable_residual_weight (nat_pos_of_exp_le hN) a q
  have hg := integrable_last_weight (nat_pos_of_exp_le hN) a q
  unfold residualShellCost lastShellCost
  calc
    _ ≤ ∫ alpha in shell N a q,
        (21 * (N : ℝ) / sourceL N ^ 2) * ‖S N alpha‖ ^ 2 +
          ‖selectedLast N a q (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2 := by
      apply setIntegral_mono_on hf ((he.const_mul _).add hg) (measurableSet_shell N a q)
      intro alpha ha
      simpa only [add_mul, Pi.add_apply] using mul_le_mul_of_nonneg_right
        (norm_selectedResidual_le_polynomial_last hN hi (shell_same_eta hq hi ha).1)
        (sq_nonneg ‖S N alpha‖)
    _ = _ := by rw [integral_add (he.const_mul _) hg, integral_const_mul]

theorem residualCost_le_polynomial_last {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    residualCost N ≤ (21 * (N : ℝ) / sourceL N ^ 2) *
      (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) + lastCost N := by
  have hN0 := exp_2000_le_of_exp_3100_le hN
  unfold residualCost lastCost
  calc
    _ ≤ ∑ i ∈ coreIndices N,
        ((21 * (N : ℝ) / sourceL N ^ 2) *
          (∫ alpha in shell N i.2 i.1, ‖S N alpha‖ ^ 2) + lastShellCost N i.2 i.1) := by
      apply Finset.sum_le_sum
      intro i hi
      have hh := (mem_coreIndices hN0 i).mp hi
      exact residualShellCost_le_polynomial_last hN hh.1 hh.2
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        ← integral_M2_eq_shell_sum hN0 _ (continuous_energy N)]

def frontierFee (N : ℕ) : ℝ :=
  280000 * (N : ℝ) / sourceL N ^ 3 + 21 * (N : ℝ) / sourceL N ^ 2 +
    (423 / 8000 : ℝ) * (N : ℝ) / sourceL N

def totalFee (N : ℕ) : ℝ := 0.0786 * (N : ℝ) / sourceL N + frontierFee N

theorem frontierCost_le_mothers_afterReal {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    frontierCost N ≤ frontierFee N * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) + afterRealCost N := by
  have hH := frontierCost_le_polynomial_residual (exp_2000_le_of_exp_3100_le hN)
  have hR := residualCost_le_polynomial_last hN
  have hA := lastCost_le_paid_afterReal hN
  unfold frontierFee
  nlinarith only [hH, hR, hA]

theorem C_le_mothers_afterReal {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    weightedPacketCost N ≤
      (0.0005 * (N : ℝ) / sourceL N + frontierFee N) *
        (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) + afterRealCost N := by
  have h := C_le_five_paid_frontier hN
  have hf := frontierCost_le_mothers_afterReal hN
  nlinarith only [h, hf]

theorem M2_integral_le_mothers_afterReal {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
      totalFee N * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) + afterRealCost N := by
  have h := M2_integral_le_five_paid_frontier hN
  have hf := frontierCost_le_mothers_afterReal hN
  unfold totalFee
  nlinarith only [h, hf]

theorem M2_same_witness_mothers_afterReal {N : ℕ} {alpha : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (ha : alpha ∈ M2 N) :
    ∃ (q a : ℕ) (eta : ℝ), (q : ℝ) ≤ sourceP N ∧ sourceIndex a q ∧
      alpha = rationalCenter a q + eta ∧ deltaRadius N q < |eta| ∧
      |eta| ≤ 1 / ((q : ℝ) * sourceQ N) ∧
      ‖S N alpha‖ ≤ totalFee N + ‖selectedAfterReal N a q eta‖ := by
  obtain ⟨q, a, eta, hq, hi, heq, hlo, hhi, hs⟩ := M2_same_witness_five_paid hN ha
  refine ⟨q, a, eta, hq, hi, heq, hlo, hhi, ?_⟩
  have hH := norm_selectedTail_le_polynomial_residual (exp_2000_le_of_exp_3100_le hN) hq hi eta
  have hR := norm_selectedResidual_le_polynomial_last hN hi hlo
  have hA := norm_selectedLast_le_paid_afterReal hN hi hlo
  unfold totalFee frontierFee
  linarith only [hs, hH, hR, hA]

theorem totalFee_factor {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    totalFee N = (0.131475 + 280000 / sourceL N ^ 2 + 21 / sourceL N) *
      ((N : ℝ) / sourceL N) := by
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  unfold totalFee frontierFee
  field_simp
  ring

theorem totalFee_le_1675 {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    totalFee N ≤ 0.1675 * (N : ℝ) / sourceL N := by
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  have h1 : (21 : ℝ) / sourceL N ≤ 21 / 3100 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (sourceL_ge_3100 hN)
  have h2 : (280000 : ℝ) / sourceL N ^ 2 ≤ 280000 / 3100 ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (pow_le_pow_left₀ (by norm_num) (sourceL_ge_3100 hN) 2)
  rw [totalFee_factor hN]
  have hc : 0.131475 + 280000 / sourceL N ^ 2 + 21 / sourceL N ≤ (0.1675 : ℝ) := by
    linarith only [h1, h2]
  simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_right hc (div_nonneg (Nat.cast_nonneg N) hL.le)

theorem M2_integral_le_1675_afterReal {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
      (0.1675 * (N : ℝ) / sourceL N) *
        (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) + afterRealCost N :=
  (M2_integral_le_mothers_afterReal hN).trans (add_le_add
    (mul_le_mul_of_nonneg_right (totalFee_le_1675 hN)
      (integral_nonneg (fun _ => sq_nonneg _))) le_rfl)

theorem lambdaTripleCount_ge_mothers_afterReal {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∫ alpha in M1 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re +
      (∫ alpha in M3 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re +
      (∫ alpha in M4 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re -
      totalFee N * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) - afterRealCost N ≤ lambdaTripleCount N := by
  have h := lambdaTripleCount_ge_five_paid hN
  have hf := frontierCost_le_mothers_afterReal hN
  unfold totalFee
  nlinarith only [h, hf]

end LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual
