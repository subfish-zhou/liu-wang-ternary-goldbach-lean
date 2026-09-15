import LiuWang.Proof.NearArcPayment.Kernels
import LiuWang.Proof.MinorArcEnergy.Ledger

/-!
# Actual M2 consumers and the unpaid zero bill

The pointwise mother bound is unconditional. The decimal and local-energy
corollaries below are explicitly conditional on the displayed finite sum of
actual L zeros; no hypothesis bounds S itself.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LiuWang.Proof.NearArcPayment

open Interfaces Parameters ArcGeometry CompleteExpansion MinorArcEnergy
open AnalyticNumberTheory.LargeSieve

theorem S_le_paid_and_packet {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hi : sourceIndex a q)
    (hq : (q : ℝ) ≤ sourceP N) {eta : ℝ}
    (hlo : deltaRadius N q < |eta|)
    (hhi : |eta| ≤ 1 / ((q : ℝ) * sourceQ N)) :
    ‖S N (rationalCenter a q + eta)‖ ≤
      principalPayment N q + 3.025 * (N : ℝ) / sourceL N ^ 6 +
        ‖zeroPacket q N a eta‖ := by
  have hE := (complete_error_function hN hi (hq.trans (sourceP_le_sourceP1 hN)) eta).trans
    (perron_payment hN hi hq hhi)
  have hP := principal_payment hN (sourceIndex_den_pos hi) hlo
  have hid : S N (rationalCenter a q + eta) =
      (S N (rationalCenter a q + eta) - principalCoefficient q * J N eta +
        zeroPacket q N a eta) + principalCoefficient q * J N eta -
        zeroPacket q N a eta := by ring
  calc
    _ ≤ ‖S N (rationalCenter a q + eta) - principalCoefficient q * J N eta +
          zeroPacket q N a eta‖ + ‖principalCoefficient q * J N eta‖ +
          ‖zeroPacket q N a eta‖ := by
      conv_lhs => rw [hid]
      exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by linarith

theorem S_le_paid_and_bill {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hi : sourceIndex a q)
    (hq : (q : ℝ) ≤ sourceP N) {eta : ℝ}
    (hlo : deltaRadius N q < |eta|)
    (hhi : |eta| ≤ 1 / ((q : ℝ) * sourceQ N)) :
    ‖S N (rationalCenter a q + eta)‖ ≤
      principalPayment N q + 3.025 * (N : ℝ) / sourceL N ^ 6 +
        zeroBill q N a eta := by
  have he : eta ≠ 0 := abs_pos.mp ((deltaRadius_pos hN (sourceIndex_den_pos hi)).trans hlo)
  exact (S_le_paid_and_packet hN hi hq hlo hhi).trans
    (add_le_add le_rfl (norm_zeroPacket_le_bill (nat_pos_of_exp_le hN) hi he))

theorem M2_same_witness_bill {N : ℕ} {alpha : ℝ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (ha : alpha ∈ M2 N) :
    ∃ (q a : ℕ) (eta : ℝ) (hq0 : 0 < q),
      (q : ℝ) ≤ sourceP N ∧ sourceIndex a q ∧
      alpha = rationalCenter a q + eta ∧
      deltaRadius N q < |eta| ∧ |eta| ≤ 1 / ((q : ℝ) * sourceQ N) ∧
      (letI : NeZero q := ⟨Nat.ne_of_gt hq0⟩
       ‖S N alpha‖ ≤ principalPayment N q + 3.025 * (N : ℝ) / sourceL N ^ 6 +
         zeroBill q N a eta) := by
  obtain ⟨q, a, eta, hq, hi, halpha, hlo, hhi⟩ := M2_eta_range ha
  have hq0 := sourceIndex_den_pos hi
  let : NeZero q := ⟨Nat.ne_of_gt hq0⟩
  refine ⟨q, a, eta, hq0, hq, hi, halpha, hlo, hhi, ?_⟩
  rw [halpha]
  exact S_le_paid_and_bill hN hi hq hlo hhi

theorem S_le_decimal_and_bill {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hi : sourceIndex a q)
    (hq : (q : ℝ) ≤ sourceP N) {eta : ℝ}
    (hlo : deltaRadius N q < |eta|)
    (hhi : |eta| ≤ 1 / ((q : ℝ) * sourceQ N)) :
    ‖S N (rationalCenter a q + eta)‖ ≤
      0.0781 * (N : ℝ) / sourceL N + zeroBill q N a eta :=
  (S_le_paid_and_bill (exp_2000_le_of_exp_3100_le hN) hi hq hlo hhi).trans
    (add_le_add (paid_terms_le hN (sourceIndex_den_pos hi) hq) le_rfl)

def availableZeroBudget (N q : ℕ) : ℝ :=
  0.4012 * (N : ℝ) / sourceL N - principalPayment N q -
    3.025 * (N : ℝ) / sourceL N ^ 6

theorem availableZeroBudget_ge {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq0 : 0 < q)
    (hq : (q : ℝ) ≤ sourceP N) :
    0.3231 * (N : ℝ) / sourceL N ≤ availableZeroBudget N q := by
  have hh := paid_terms_le hN hq0 hq
  have he : 0.4012 * (N : ℝ) / sourceL N - 0.3231 * (N : ℝ) / sourceL N =
      0.0781 * (N : ℝ) / sourceL N := by ring
  unfold availableZeroBudget
  linarith only [hh, he]

theorem M2_le_4012_of_exact_zeroBill {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hz : ∀ (q a : ℕ) [NeZero q] (eta : ℝ),
      (q : ℝ) ≤ sourceP N → sourceIndex a q →
      deltaRadius N q < |eta| → |eta| ≤ 1 / ((q : ℝ) * sourceQ N) →
      zeroBill q N a eta ≤ availableZeroBudget N q) :
    ∀ alpha ∈ M2 N, ‖S N alpha‖ ≤ 0.4012 * (N : ℝ) / sourceL N := by
  intro alpha ha
  obtain ⟨q, a, eta, hq, hi, halpha, hlo, hhi⟩ := M2_eta_range ha
  let : NeZero q := ⟨Nat.ne_of_gt (sourceIndex_den_pos hi)⟩
  have hb := S_le_paid_and_bill (exp_2000_le_of_exp_3100_le hN) hi hq hlo hhi
  have hz' := hz q a eta hq hi hlo hhi
  unfold availableZeroBudget at hz'
  rw [halpha]
  linarith

theorem M2_le_of_zeroBill {N : ℕ} {B : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hz : ∀ (q a : ℕ) [NeZero q] (eta : ℝ),
      (q : ℝ) ≤ sourceP N → sourceIndex a q →
      deltaRadius N q < |eta| → |eta| ≤ 1 / ((q : ℝ) * sourceQ N) →
      zeroBill q N a eta ≤ B) :
    ∀ alpha ∈ M2 N, ‖S N alpha‖ ≤ 0.0781 * (N : ℝ) / sourceL N + B := by
  intro alpha ha
  obtain ⟨q, a, eta, hq, hi, halpha, hlo, hhi⟩ := M2_eta_range ha
  let : NeZero q := ⟨Nat.ne_of_gt (sourceIndex_den_pos hi)⟩
  rw [halpha]
  exact (S_le_decimal_and_bill hN hi hq hlo hhi).trans
    (add_le_add le_rfl (hz q a eta hq hi hlo hhi))

theorem M2_le_4012_of_zeroBill {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hz : ∀ (q a : ℕ) [NeZero q] (eta : ℝ),
      (q : ℝ) ≤ sourceP N → sourceIndex a q →
      deltaRadius N q < |eta| → |eta| ≤ 1 / ((q : ℝ) * sourceQ N) →
      zeroBill q N a eta ≤ 0.3231 * (N : ℝ) / sourceL N) :
    ∀ alpha ∈ M2 N, ‖S N alpha‖ ≤ 0.4012 * (N : ℝ) / sourceL N := by
  intro alpha ha
  convert M2_le_of_zeroBill hN hz alpha ha using 1
  ring

theorem M2_integral_le_local_of_zeroBill {N : ℕ} {B : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hz : ∀ (q a : ℕ) [NeZero q] (eta : ℝ),
      (q : ℝ) ≤ sourceP N → sourceIndex a q →
      deltaRadius N q < |eta| → |eta| ≤ 1 / ((q : ℝ) * sourceQ N) →
      zeroBill q N a eta ≤ B) :
    ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
      (0.0781 * (N : ℝ) / sourceL N + B) *
        ∫ alpha in M2 N, ‖S N alpha‖ ^ 2 :=
  norm_setIntegral_le_local_energy N (measurableSet_M2 N)
    (M2_subset_sourceDomain (exp_2000_le_of_exp_3100_le hN))
    (M2_le_of_zeroBill hN hz)

theorem M2_integral_le_4012_local_of_zeroBill {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hz : ∀ (q a : ℕ) [NeZero q] (eta : ℝ),
      (q : ℝ) ≤ sourceP N → sourceIndex a q →
      deltaRadius N q < |eta| → |eta| ≤ 1 / ((q : ℝ) * sourceQ N) →
      zeroBill q N a eta ≤ 0.3231 * (N : ℝ) / sourceL N) :
    ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
      (0.4012 * (N : ℝ) / sourceL N) * ∫ alpha in M2 N, ‖S N alpha‖ ^ 2 :=
  norm_setIntegral_le_local_energy N (measurableSet_M2 N)
    (M2_subset_sourceDomain (exp_2000_le_of_exp_3100_le hN))
    (M2_le_4012_of_zeroBill hN hz)

theorem M2_integral_le_remaining_energy_of_zeroBill {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hz : ∀ (q a : ℕ) [NeZero q] (eta : ℝ),
      (q : ℝ) ≤ sourceP N → sourceIndex a q →
      deltaRadius N q < |eta| → |eta| ≤ 1 / ((q : ℝ) * sourceQ N) →
      zeroBill q N a eta ≤ 0.3231 * (N : ℝ) / sourceL N) :
    ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
      (0.4012 * (N : ℝ) / sourceL N) *
        ((∑ n ∈ windowFinset N, ArithmeticFunction.vonMangoldt n ^ 2) -
          (∫ alpha in M1 N, ‖S N alpha‖ ^ 2) -
          (∫ alpha in M3 N, ‖S N alpha‖ ^ 2) -
          (∫ alpha in M4 N, ‖S N alpha‖ ^ 2)) := by
  have he := minor_energy_eq_source_sub_major (exp_2000_le_of_exp_3100_le hN)
  rw [source_energy_eq] at he
  have he2 : (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) =
      (∑ n ∈ windowFinset N, ArithmeticFunction.vonMangoldt n ^ 2) -
        (∫ alpha in M1 N, ‖S N alpha‖ ^ 2) -
        (∫ alpha in M3 N, ‖S N alpha‖ ^ 2) -
        (∫ alpha in M4 N, ‖S N alpha‖ ^ 2) := by linarith
  rw [← he2]
  exact M2_integral_le_4012_local_of_zeroBill hN hz

end LiuWang.Proof.NearArcPayment
