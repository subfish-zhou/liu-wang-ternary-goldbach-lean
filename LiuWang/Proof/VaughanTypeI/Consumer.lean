import LiuWang.Proof.VaughanTypeI.Main

/-! # 原大 N 域的实际消费者：分解、S1 零性及 S2/S3 原系数界。 -/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.VaughanTypeI

open Interfaces Parameters

example {N a q : ℕ} {α θ : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (_hqL : sourceP1 N ≤ (q : ℝ)) (_hqU : (q : ℝ) ≤ sourceQ N)
    (_hi : sourceIndex a q) (_hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2) :
    S N α = sourceS1 N α + sourceS2 N α + sourceS3 N α + sourceS4 N α ∧
      sourceS1 N α = 0 ∧
      S N α = sourceS2 N α + sourceS3 N α + sourceS4 N α := by
  subst α
  have h2000 := exp_2000_le_of_exp_3100_le hN
  exact ⟨sourceS_decomposition h2000 _, sourceS1_eq_zero h2000 _,
    sourceS_eq_actual_remainder hN _⟩

example : 1 ∈ windowFinset 1000 := by
  norm_num [mem_windowFinset_iff, mem_windowSet_iff]

example : 1 ∉ windowFinset 1001 := by
  norm_num [mem_windowFinset_iff, mem_windowSet_iff]

example {N a q : ℕ} {α θ : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (_hqL : sourceP1 N ≤ (q : ℝ)) (_hqU : (q : ℝ) ≤ sourceQ N)
    (_hi : sourceIndex a q) (_hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2) :
    ‖sourceS2 N α‖ ≤ sourceL N *
        ∑ t ∈ Finset.Icc 1 ⌊sourceVaughanV N⌋₊,
          truncatedKernel ((N : ℝ) / t) ((t : ℝ) * α) ∧
      ‖sourceS3 N α‖ ≤ Real.log (sourceVaughanU N * sourceVaughanV N) *
        ∑ d ∈ Finset.Icc 1 ⌊sourceVaughanU N * sourceVaughanV N⌋₊,
          truncatedKernel ((N : ℝ) / d) ((d : ℝ) * α) ∧
      ‖S N α - sourceS4 N α‖ ≤
        sourceL N * ∑ t ∈ Finset.Icc 1 ⌊sourceVaughanV N⌋₊,
          truncatedKernel ((N : ℝ) / t) ((t : ℝ) * α) +
        Real.log (sourceVaughanU N * sourceVaughanV N) *
          ∑ d ∈ Finset.Icc 1 ⌊sourceVaughanU N * sourceVaughanV N⌋₊,
            truncatedKernel ((N : ℝ) / d) ((d : ℝ) * α) := by
  subst α
  have h2000 := exp_2000_le_of_exp_3100_le hN
  exact ⟨norm_sourceS2_le_kernel h2000 _, norm_sourceS3_le_kernel h2000 _,
    norm_sourceS_sub_actualS4_le_kernel hN _⟩

example : 1 ∈ closedRow 1000 1 := by
  rw [mem_closedRow (by norm_num)]
  norm_num [mem_windowFinset_iff, mem_windowSet_iff]

example : 1 ∉ closedRow 1001 1 := by
  rw [mem_closedRow (by norm_num)]
  norm_num [mem_windowFinset_iff, mem_windowSet_iff]

example (Y : ℝ) (a q : ℕ) (hq : 0 < q) :
    truncatedKernel Y ((q : ℝ) * ((a : ℝ) / q)) = Y := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [mul_div_cancel₀ _ hq0]
  exact truncatedKernel_int Y (a : ℤ)

theorem source_typeI_large_consumer {N a q : ℕ} {α θ : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) (hqU : (q : ℝ) ≤ sourceQ N)
    (hi : sourceIndex a q) (hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2) :
    S N α = sourceS1 N α + sourceS2 N α + sourceS3 N α + sourceS4 N α ∧
    sourceS1 N α = 0 ∧
    ‖sourceS2 N α‖ ≤
      0.0282 * (N : ℝ) * (q : ℝ) ^ (-(1 / 2 : ℝ)) * sourceL N ^ 2 +
      0.0001 * (N : ℝ) ^ (4 / 5 : ℝ) * sourceL N ^ (7 / 5 : ℝ) +
      0.0006 * (N : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) *
        sourceL N ^ (5 / 2 : ℝ) ∧
    ‖sourceS3 N α‖ ≤
      0.0131 * (N : ℝ) * (q : ℝ) ^ (-(1 / 2 : ℝ)) * sourceL N ^ 2 +
      0.8 * (N : ℝ) ^ (4 / 5 : ℝ) * sourceL N ^ (7 / 5 : ℝ) +
      0.0005 * (N : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) *
        sourceL N ^ (5 / 2 : ℝ) ∧
    ‖S N α‖ ≤
      0.0413 * (N : ℝ) * (q : ℝ) ^ (-(1 / 2 : ℝ)) * sourceL N ^ 2 +
      0.8001 * (N : ℝ) ^ (4 / 5 : ℝ) * sourceL N ^ (7 / 5 : ℝ) +
      0.0011 * (N : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) *
        sourceL N ^ (5 / 2 : ℝ) + ‖sourceS4 N α‖ := by
  obtain ⟨hdec, h1, h2, h3, hrem⟩ := source_typeI_large hN hqL hqU hi hθ hα
  refine ⟨hdec, h1, h2, h3, ?_⟩
  calc
    ‖S N α‖ = ‖(S N α - sourceS4 N α) + sourceS4 N α‖ := by rw [sub_add_cancel]
    _ ≤ ‖S N α - sourceS4 N α‖ + ‖sourceS4 N α‖ := norm_add_le _ _
    _ ≤ _ := add_le_add_left hrem _

end LiuWang.Proof.VaughanTypeI
