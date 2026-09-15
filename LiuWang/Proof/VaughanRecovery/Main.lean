import LiuWang.Proof.VaughanRecovery.Budget
import LiuWang.Proof.VaughanRecovery.Recovered

/-! 同一实际相位与逼近上的 Type I、恢复 Type II、完整 S 和 M4。 -/

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.VaughanRecovery

open Interfaces Parameters VaughanTypeII VaughanTypeIIBudget
open ArithmeticBounds LambdaMoment

def typeIMajorant (N q : ℕ) : ℝ :=
  0.0413 * termA N q + 0.8001 * termB N + 0.0011 * termC N q

theorem sourceS_le_typeI_add {N a q : ℕ} {α θ E : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) (hqU : (q : ℝ) ≤ sourceQ N)
    (hi : sourceIndex a q) (hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2)
    (hE : ‖VaughanTypeI.sourceS4 N α‖ ≤ E) :
    ‖S N α‖ ≤ typeIMajorant N q + E := by
  have hI : ‖S N α - VaughanTypeI.sourceS4 N α‖ ≤ typeIMajorant N q := by
    simpa only [typeIMajorant, termA, termB, termC, neg_div, mul_assoc] using
      VaughanTypeI.norm_sourceS_sub_actualS4_le hN hqL hqU hi hθ hα
  have htriangle : ‖S N α‖ ≤
      ‖S N α - VaughanTypeI.sourceS4 N α‖ + ‖VaughanTypeI.sourceS4 N α‖ := by
    simpa only [sub_add_cancel] using
      norm_add_le (S N α - VaughanTypeI.sourceS4 N α) (VaughanTypeI.sourceS4 N α)
  exact htriangle.trans (add_le_add hI hE)

theorem sourceS4_le_repaid {N a q : ℕ} {α θ : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) (hqU : (q : ℝ) ≤ sourceQ N)
    (hi : sourceIndex a q) (hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2) :
    ‖VaughanTypeI.sourceS4 N α‖ ≤
      0.1328355 * termA N q + 2.4353175 * termB N + 0.075906 * termC N q :=
  (sourceS4_le_recoveredDyadicBudget hN hqL hi hθ hα).trans
    (recoveredDyadicBudget_le_three_terms hN hqL hqU)

theorem sourceS_le_repaid {N a q : ℕ} {α θ : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) (hqU : (q : ℝ) ≤ sourceQ N)
    (hi : sourceIndex a q) (hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2) :
    ‖S N α‖ ≤ 0.1741355 * termA N q + 3.2354175 * termB N + 0.077006 * termC N q := by
  have hs := sourceS_le_typeI_add hN hqL hqU hi hθ hα
    (sourceS4_le_repaid hN hqL hqU hi hθ hα)
  unfold typeIMajorant at hs
  linarith

theorem M4_exists_repaid {N : ℕ} {α : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hα : α ∈ M4 N) :
    ∃ (q a : ℕ) (θ : ℝ), sourceP1 N < (q : ℝ) ∧ (q : ℝ) ≤ sourceQ N ∧
      sourceIndex a q ∧ |θ| ≤ 1 ∧
      α = rationalCenter a q + θ / (q : ℝ) ^ 2 ∧
      |α - rationalCenter a q| ≤ 1 / ((q : ℝ) * sourceQ N) ∧
      ‖S N α‖ ≤ typeIMajorant N q + energySum N (fun M => actualEnergy N M α) ∧
      ‖S N α‖ ≤ typeIMajorant N q + energySum N (fun M =>
        moebiusMass M * (((N : ℝ) / M) *
          (W1 N ((N : ℝ) / M) + W2 N ((N : ℝ) / M) + 2 * W3 N ((N : ℝ) / M))) *
            rowMax N M α) ∧
      ‖S N α‖ ≤ typeIMajorant N q + energySum N (fun M =>
        moebiusMass M * (((N : ℝ) / M) * primeBudget N ((N : ℝ) / M)) * rowMax N M α) ∧
      ‖S N α‖ ≤ typeIMajorant N q + energySum N (fun M =>
        ((30517 / 50000) * M + 272) *
          (((N : ℝ) / M) * primeBudget N ((N : ℝ) / M)) * rowMax N M α) ∧
      ‖S N α‖ ≤ typeIMajorant N q +
        recoveredKappa * Real.sqrt (N : ℝ) * Real.log ((N : ℝ) / sourceVaughanV N) *
          geometricRows N q ∧
      ‖S N α‖ ≤ 0.1741355 * termA N q + 3.2354175 * termB N + 0.077006 * termC N q := by
  obtain ⟨q, a, θ, hqL, hqU, hi, hθ, heq, harc⟩ := M4_approximation hN hα
  have hn := exp_2000_le_of_exp_3100_le hN
  refine ⟨q, a, θ, hqL, hqU, hi, hθ, heq, harc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sourceS_le_typeI_add hN hqL.le hqU hi hθ heq (sourceS4_le_actualEnergy hn α)
  · exact sourceS_le_typeI_add hN hqL.le hqU hi hθ heq (sourceS4_le_W123 hN α)
  · exact sourceS_le_typeI_add hN hqL.le hqU hi hθ heq (sourceS4_le_primeEnergy hN α)
  · exact sourceS_le_typeI_add hN hqL.le hqU hi hθ heq (sourceS4_le_linear_primeEnergy hN α)
  · exact sourceS_le_typeI_add hN hqL.le hqU hi hθ heq
      ((sourceS4_le_recoveredDyadicBudget hN hqL.le hi hθ heq).trans
        (recoveredDyadicBudget_le_geometric hN hqL.le hqU))
  · exact sourceS_le_repaid hN hqL.le hqU hi hθ heq

theorem M4_le_repaid_mother {N : ℕ} {α : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hα : α ∈ M4 N) :
    ‖S N α‖ ≤ mother N 0.1741355 3.2354175 0.077006 := by
  obtain ⟨q, _, _, hqL, hqU, _, _, _, _, _, _, _, _, _, hs⟩ := M4_exists_repaid hN hα
  exact hs.trans (three_terms_le_mother (exp_2000_le_of_exp_3100_le hN)
    hqL.le hqU (by norm_num) (by norm_num))

theorem M4_le_1743 {N : ℕ} {α : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hα : α ∈ M4 N) :
    ‖S N α‖ ≤ 0.1743 * (N : ℝ) / sourceL N :=
  (M4_le_repaid_mother hN hα).trans
    (mother_le_uniform hN (by norm_num) (by norm_num) (by norm_num))

end LiuWang.Proof.VaughanRecovery
