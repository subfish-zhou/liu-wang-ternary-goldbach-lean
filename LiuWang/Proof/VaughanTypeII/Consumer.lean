import LiuWang.Proof.VaughanTypeII.Main
import LiuWang.Proof.VaughanTypeI.Main

/-! 直接消费冻结分解中的 sourceS4，以及实际 Interfaces.S 去掉第二、三项后的余项。 -/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.VaughanTypeII

open Finset Interfaces Parameters
open AnalyticNumberTheory.LargeSieve
open scoped BigOperators

theorem actual_remainder_typeII_bound {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (α : ℝ) :
    ‖S N α - VaughanTypeI.sourceS2 N α - VaughanTypeI.sourceS3 N α‖ ≤
      Real.sqrt ((6111 / 10000) * (31 / 100)) * Real.sqrt (N : ℝ) *
        Real.log ((N : ℝ) / sourceVaughanV N) *
          ∑ j ∈ range (dyadicCount N), Real.sqrt (rowMax N (dyadicScale N j) α) := by
  have he : S N α - VaughanTypeI.sourceS2 N α - VaughanTypeI.sourceS3 N α =
      VaughanTypeI.sourceS4 N α := by
    rw [VaughanTypeI.sourceS_eq_actual_remainder hN]
    ring
  rw [he]
  exact actual_typeII_bound hN α

example (M : ℝ) (k : ℤ) : kernel M (k : ℝ) = M + 1 / 2 := by
  simp [kernel, distToInt]

example {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) (α : ℝ) :
    VaughanTypeI.sourceS4 N α =
      ∑ j ∈ range (dyadicCount N), block N (dyadicScale N j) α :=
  sourceS4_eq_dyadic_blocks (exp_2000_le_of_exp_3100_le hN) α

example {N : ℕ} {M : ℝ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hM : sourceVaughanV N ≤ M) (hM' : M ≤ (N : ℝ) / sourceVaughanU N) (α : ℝ) :
    ‖block N M α‖ ^ 2 ≤
      ((6111 / 10000) * (31 / 100)) * (N : ℝ) *
        Real.log ((N : ℝ) / sourceVaughanV N) ^ 2 * rowMax N M α :=
  block_sq_le_paid_moment_rowMax hN hM hM' α

end LiuWang.Proof.VaughanTypeII
