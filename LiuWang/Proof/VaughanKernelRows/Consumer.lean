import LiuWang.Proof.VaughanKernelRows.Main

/-! # 原域实际有限行消费者与共振、空区间、跨零边界例。 -/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.VaughanKernelRows

open Finset VaughanTypeI Interfaces Parameters

theorem source_kernel_row_consumer {N a q : ℕ} {α θ M : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) (hqU : (q : ℝ) ≤ sourceQ N)
    (hi : sourceIndex a q) (hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2)
    (hVM : sourceVaughanV N ≤ M) (hMU : M ≤ (N : ℝ) / sourceVaughanU N)
    (m : ℕ) :
    (∑ m' ∈ Ioc ⌊sourceVaughanU N⌋₊ ⌊(N : ℝ) / M⌋₊,
      truncatedKernel (M + 1 / 2) (α * ((m : ℝ) - (m' : ℝ)))) ≤
      (((N : ℝ) / M - sourceVaughanU N + 1) / q + 1) *
        (3 * (M + 1 / 2) + (q : ℝ) * (1 + Real.log q)) ∧
    (∑ m' ∈ Ioc ⌊sourceVaughanU N⌋₊ ⌊(N : ℝ) / M⌋₊,
      truncatedKernel (M + 1 / 2) (α * ((m : ℝ) - (m' : ℝ)))) ≤
      3 * (N : ℝ) / q + 3 * M + ((N : ℝ) / M) * (1 + Real.log q) +
        (q : ℝ) * (1 + Real.log q) ∧
    (∑ m' ∈ Ioc ⌊sourceVaughanU N⌋₊ ⌊(N : ℝ) / M⌋₊,
      truncatedKernel (M + 1 / 2) (α * ((m : ℝ) - (m' : ℝ)))) ≤
      3 * (N : ℝ) / q + 3 * M + ((N : ℝ) / M) * sourceL N +
        (q : ℝ) * sourceL N :=
  ⟨source_row_bound hN hqL hi.2.2 hθ hα hVM hMU m,
    source_row_le hN hqL hi.2.2 hθ hα hVM hMU m,
    source_row_le_logN hN hqL hqU hi.2.2 hθ hα hVM hMU m⟩

example (T α : ℝ) (m : ℕ) :
    truncatedKernel T (α * ((m : ℝ) - (m : ℝ))) = T := by
  simpa using truncatedKernel_int T (0 : ℤ)

example (T α U : ℝ) (m : ℕ) :
    (∑ m' ∈ Ioc ⌊U⌋₊ ⌊U⌋₊,
      truncatedKernel T (α * ((m : ℝ) - (m' : ℝ)))) = 0 := by
  simp

example (T α : ℝ) :
    (∑ m' ∈ Ioc (0 : ℕ) 3, truncatedKernel T (α * ((2 : ℝ) - (m' : ℝ)))) =
      2 * truncatedKernel T α + T := by
  have hz : truncatedKernel T 0 = T := by simpa using truncatedKernel_int T (0 : ℤ)
  rw [show Ioc (0 : ℕ) 3 = {1, 2, 3} by decide]
  norm_num [hz, truncatedKernel_neg]
  ring

example {a q : ℕ} {α β θ : ℝ}
    (hq : 0 < q) (hcop : Nat.Coprime a q) (hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2) :
    (∑ k ∈ range q, truncatedKernel 0 (α * k + β)) ≤
      (q : ℝ) * (1 + Real.log q) := by
  simpa using rational_phase_kernel_le (β := β) hq hcop hθ hα (le_refl (0 : ℝ))

example (β T : ℝ) (hT : 0 ≤ T) :
    (∑ k ∈ range 1, truncatedKernel T ((0 : ℝ) * k + β)) ≤ 3 * T + 1 := by
  simpa using rational_phase_kernel_le (a := 0) (q := 1) (α := 0) (β := β)
    (θ := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hT

end LiuWang.Proof.VaughanKernelRows
