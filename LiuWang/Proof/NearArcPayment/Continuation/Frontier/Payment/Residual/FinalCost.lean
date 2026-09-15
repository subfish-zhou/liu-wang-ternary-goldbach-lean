import LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual.LowWhole

/-! 两个不交余族的原 S² 加权费用；旧新多项式母费用先合账，最后才给小数回归。 -/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual

open Interfaces Parameters ArcGeometry CompleteExpansion MajorArcApproximation MinorArcEnergy
open AnalyticNumberTheory.LargeSieve

def restPart (N a q : ℕ) (positive : Bool) (eta : ℝ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    realPacketOn q a (fun chi => restValues chi N positive) N eta

theorem restPart_eq {q : ℕ} [NeZero q] (N a : ℕ) (positive : Bool) (eta : ℝ) :
    restPart N a q positive eta =
      realPacketOn q a (fun chi => restValues chi N positive) N eta := by
  simp only [restPart, dif_neg (NeZero.ne q)]

def selectedRest (N a q : ℕ) (eta : ℝ) : ℂ :=
  if 0 ≤ eta then restPart N a q true eta else restPart N a q false eta

theorem continuous_restPart {N : ℕ} (hN : 0 < N) (a q : ℕ) (positive : Bool) :
    Continuous (restPart N a q positive) := by
  by_cases hq : q = 0
  · subst q
    change Continuous (fun _ : ℝ => (0 : ℂ))
    exact continuous_const
  · let : NeZero q := ⟨hq⟩
    simp only [funext (restPart_eq N a positive)]
    unfold realPacketOn
    exact continuous_const.mul (continuous_finsetSum _ (fun chi _ =>
      continuous_const.mul (continuous_finsetSum _ (fun rho _ =>
        continuous_const.mul (SingularIntegral.Jrho_continuous hN rho)))))

theorem norm_afterReal_le_low_paid_rest {N a q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hi : sourceIndex a q) {eta : ℝ}
    (he : deltaRadius N q < |eta|) :
    ‖selectedAfterReal N a q eta‖ ≤ lowFee N + ‖selectedRest N a q eta‖ := by
  let : NeZero q := ⟨Nat.ne_of_gt (sourceIndex_den_pos hi)⟩
  have hh (positive : Bool) :
      ‖afterRealPart N a q positive eta‖ ≤ lowFee N + ‖restPart N a q positive eta‖ := by
    rw [afterRealPart_eq, restPart_eq, afterRealPacket_eq_low_add_rest N a positive]
    exact (norm_add_le _ _).trans (add_le_add (norm_lowPacket hN positive he) le_rfl)
  unfold selectedAfterReal selectedRest
  split_ifs
  · exact hh true
  · exact hh false

def restShellCost (N a q : ℕ) : ℝ :=
  ∫ alpha in shell N a q,
    ‖selectedRest N a q (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2

def restCost (N : ℕ) : ℝ := ∑ i ∈ coreIndices N, restShellCost N i.2 i.1

theorem integrable_rest_weight {N : ℕ} (hN : 0 < N) (a q : ℕ) :
    IntegrableOn (fun alpha : ℝ =>
      ‖selectedRest N a q (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2) (shell N a q) :=
  integrable_selected_weight a q _ _
    (continuous_restPart hN a q true) (continuous_restPart hN a q false)

theorem restCost_nonneg (N : ℕ) : 0 ≤ restCost N :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg
    (fun _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)))

theorem afterRealShellCost_le_low_paid_rest {N a q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) (hi : sourceIndex a q) :
    afterRealShellCost N a q ≤
      lowFee N * (∫ alpha in shell N a q, ‖S N alpha‖ ^ 2) + restShellCost N a q := by
  have he : IntegrableOn (fun alpha : ℝ => ‖S N alpha‖ ^ 2) (shell N a q) :=
    (continuous_energy N).integrableOn_Icc.mono_set Set.sdiff_subset
  have hf := integrable_afterReal_weight (nat_pos_of_exp_le hN) a q
  have hg := integrable_rest_weight (nat_pos_of_exp_le hN) a q
  unfold afterRealShellCost restShellCost
  calc
    _ ≤ ∫ alpha in shell N a q, lowFee N * ‖S N alpha‖ ^ 2 +
          ‖selectedRest N a q (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2 := by
      apply setIntegral_mono_on hf ((he.const_mul _).add hg) (measurableSet_shell N a q)
      intro alpha ha
      simpa only [add_mul, Pi.add_apply] using mul_le_mul_of_nonneg_right
        (norm_afterReal_le_low_paid_rest hN hi (shell_same_eta hq hi ha).1) (sq_nonneg ‖S N alpha‖)
    _ = _ := by rw [integral_add (he.const_mul _) hg, integral_const_mul]

theorem afterRealCost_le_low_paid_rest {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    afterRealCost N ≤ lowFee N * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) + restCost N := by
  have hN0 := exp_2000_le_of_exp_3100_le hN
  unfold afterRealCost restCost
  calc
    _ ≤ ∑ i ∈ coreIndices N,
        (lowFee N * (∫ alpha in shell N i.2 i.1, ‖S N alpha‖ ^ 2) + restShellCost N i.2 i.1) := by
      apply Finset.sum_le_sum
      intro i hi
      have hh := (mem_coreIndices hN0 i).mp hi
      exact afterRealShellCost_le_low_paid_rest hN hh.1 hh.2
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        ← integral_M2_eq_shell_sum hN0 _ (continuous_energy N)]

def newFee (N : ℕ) : ℝ := (423 / 8000 : ℝ) * (N : ℝ) / sourceL N + lowFee N

def fullFee (N : ℕ) : ℝ := totalFee N + lowFee N

theorem lastCost_le_full_paid_rest {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    lastCost N ≤ newFee N * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) + restCost N := by
  have hR := lastCost_le_paid_afterReal hN
  have hL := afterRealCost_le_low_paid_rest hN
  unfold newFee
  nlinarith only [hR, hL]

theorem frontierCost_le_full_mothers_rest {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    frontierCost N ≤ (frontierFee N + lowFee N) *
      (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) + restCost N := by
  have hF := frontierCost_le_mothers_afterReal hN
  have hL := afterRealCost_le_low_paid_rest hN
  nlinarith only [hF, hL]

theorem C_le_full_mothers_rest {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    weightedPacketCost N ≤
      (0.0005 * (N : ℝ) / sourceL N + frontierFee N + lowFee N) *
        (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) + restCost N := by
  have hC := C_le_mothers_afterReal hN
  have hL := afterRealCost_le_low_paid_rest hN
  nlinarith only [hC, hL]

theorem M2_integral_le_full_mothers_rest {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
      fullFee N * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) + restCost N := by
  have hM := M2_integral_le_mothers_afterReal hN
  have hL := afterRealCost_le_low_paid_rest hN
  unfold fullFee
  nlinarith only [hM, hL]

theorem M2_same_witness_full_mothers_rest {N : ℕ} {alpha : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (ha : alpha ∈ M2 N) :
    ∃ (q a : ℕ) (eta : ℝ), (q : ℝ) ≤ sourceP N ∧ sourceIndex a q ∧
      alpha = rationalCenter a q + eta ∧ deltaRadius N q < |eta| ∧
      |eta| ≤ 1 / ((q : ℝ) * sourceQ N) ∧
      ‖S N alpha‖ ≤ fullFee N + ‖selectedRest N a q eta‖ := by
  obtain ⟨q, a, eta, hq, hi, heq, hlo, hhi, hs⟩ := M2_same_witness_mothers_afterReal hN ha
  refine ⟨q, a, eta, hq, hi, heq, hlo, hhi, ?_⟩
  have hL := norm_afterReal_le_low_paid_rest hN hi hlo
  unfold fullFee
  linarith only [hs, hL]

theorem fullFee_factor {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    fullFee N =
      (0.288975 + 280000 / sourceL N ^ 2 + 21 / sourceL N +
        (27 / 200 : ℝ) * Real.log (sourceL N) / sourceL N) * ((N : ℝ) / sourceL N) := by
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  unfold fullFee lowFee
  rw [totalFee_factor hN]
  field_simp
  ring

theorem log_ratio_endpoint {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    Real.log (sourceL N) / sourceL N ≤ 9 / 3100 := by
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < sourceL N / 3100)
  rw [Real.log_div hL.ne' (by norm_num)] at hh
  apply (div_le_iff₀ hL).mpr
  linarith [log_3100_le_nine, sourceL_ge_3100 hN]

theorem fullFee_le_3253 {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    fullFee N ≤ 0.3253 * (N : ℝ) / sourceL N := by
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  have h1 : (21 : ℝ) / sourceL N ≤ 21 / 3100 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (sourceL_ge_3100 hN)
  have h2 : (280000 : ℝ) / sourceL N ^ 2 ≤ 280000 / 3100 ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (pow_le_pow_left₀ (by norm_num) (sourceL_ge_3100 hN) 2)
  have h3 := log_ratio_endpoint hN
  rw [fullFee_factor hN]
  have hc : 0.288975 + 280000 / sourceL N ^ 2 + 21 / sourceL N +
      (27 / 200 : ℝ) * Real.log (sourceL N) / sourceL N ≤ 0.3253 := by
    rw [mul_div_assoc]
    linarith only [h1, h2, h3]
  simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_right hc (div_nonneg (Nat.cast_nonneg N) hL.le)

theorem M2_integral_le_3253_rest {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
      (0.3253 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) + restCost N :=
  (M2_integral_le_full_mothers_rest hN).trans (add_le_add
    (mul_le_mul_of_nonneg_right (fullFee_le_3253 hN)
      (integral_nonneg (fun _ => sq_nonneg _))) le_rfl)

theorem lambdaTripleCount_ge_full_mothers_rest {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∫ alpha in M1 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re +
      (∫ alpha in M3 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re +
      (∫ alpha in M4 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re -
      fullFee N * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) - restCost N ≤ lambdaTripleCount N := by
  have h := lambdaTripleCount_ge_mothers_afterReal hN
  have hf := afterRealCost_le_low_paid_rest hN
  unfold fullFee
  nlinarith only [h, hf]

end LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual
