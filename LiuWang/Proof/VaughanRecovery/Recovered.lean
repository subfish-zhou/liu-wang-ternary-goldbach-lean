import LiuWang.Proof.VaughanRecovery.Range

/-! 同一个真实 M4 逼近见证，保留原三项强界和连续区间母界。 -/

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.VaughanRecovery

open Interfaces Parameters ArcGeometry VaughanTypeIIBudget

theorem M4_approximation {N : ℕ} {α : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hα : α ∈ M4 N) :
    ∃ (q a : ℕ) (θ : ℝ), sourceP1 N < (q : ℝ) ∧ (q : ℝ) ≤ sourceQ N ∧
      sourceIndex a q ∧ |θ| ≤ 1 ∧
      α = rationalCenter a q + θ / (q : ℝ) ^ 2 ∧
      |α - rationalCenter a q| ≤ 1 / ((q : ℝ) * sourceQ N) := by
  have hn := exp_2000_le_of_exp_3100_le hN
  obtain ⟨q, a, hqL, hqU, hi, ha⟩ := M4_rational_approximation hn hα
  have hq : (0 : ℝ) < q := by exact_mod_cast sourceIndex_den_pos hi
  have hq2 : (0 : ℝ) < (q : ℝ) ^ 2 := pow_pos hq _
  have harc := (mem_approximationArc_iff N a q α).mp ha
  have hr : 1 / ((q : ℝ) * sourceQ N) ≤ 1 / (q : ℝ) ^ 2 :=
    one_div_le_one_div_of_le hq2 (by nlinarith)
  let θ := (α - rationalCenter a q) * (q : ℝ) ^ 2
  have hθ : |θ| ≤ 1 := by
    dsimp [θ]
    rw [abs_mul, abs_of_pos hq2]
    exact (le_div_iff₀ hq2).mp (harc.trans hr)
  have heq : α = rationalCenter a q + θ / (q : ℝ) ^ 2 := by
    dsimp [θ]
    rw [mul_div_cancel_right₀ _ hq2.ne']
    ring
  exact ⟨q, a, θ, hqL, hqU, hi, hθ, heq, harc⟩

theorem M4_exists_strong {N : ℕ} {α : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hα : α ∈ M4 N) :
    ∃ (q a : ℕ) (θ : ℝ), sourceP1 N < (q : ℝ) ∧ (q : ℝ) ≤ sourceQ N ∧
      sourceIndex a q ∧ |θ| ≤ 1 ∧
      α = rationalCenter a q + θ / (q : ℝ) ^ 2 ∧
      |α - rationalCenter a q| ≤ 1 / ((q : ℝ) * sourceQ N) ∧
      ‖S N α‖ ≤ 0.1939 * termA N q + 3.318 * termB N + 0.0883 * termC N q := by
  obtain ⟨q, a, θ, hqL, hqU, hi, hθ, heq, harc⟩ := M4_approximation hN hα
  exact ⟨q, a, θ, hqL, hqU, hi, hθ, heq, harc,
    VaughanEstimate.norm_sourceS_le_strong hN hqL.le hqU hi hθ heq⟩

theorem M4_le_mother {N : ℕ} {α : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hα : α ∈ M4 N) :
    ‖S N α‖ ≤ mother N 0.1939 3.318 0.0883 := by
  obtain ⟨q, _, _, hqL, hqU, _, _, _, _, hs⟩ := M4_exists_strong hN hα
  exact hs.trans (three_terms_le_mother (exp_2000_le_of_exp_3100_le hN)
    hqL.le hqU (by norm_num) (by norm_num))

theorem M4_le_194 {N : ℕ} {α : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hα : α ∈ M4 N) :
    ‖S N α‖ ≤ 0.194 * (N : ℝ) / sourceL N :=
  (M4_le_mother hN hα).trans
    (mother_le_uniform hN (by norm_num) (by norm_num) (by norm_num))

end LiuWang.Proof.VaughanRecovery
