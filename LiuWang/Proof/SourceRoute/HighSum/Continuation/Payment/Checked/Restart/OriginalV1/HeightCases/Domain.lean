import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.Source26Reduction

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.HeightCases

theorem log_le_height_linear {L : ℝ} (hL : 3100 ≤ L) :
    360 * Real.log L ≤ L := by
  have hL0 : 0 < L := by linarith
  have ht := Real.log_le_sub_one_of_pos (div_pos hL0 (by norm_num : (0 : ℝ) < 3100))
  rw [Real.log_div hL0.ne' (by norm_num : (3100 : ℝ) ≠ 0)] at ht
  have hb := Continuation.log_3100_bounds.2
  linarith

theorem actual_ratio_ge_twenty {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y : ℝ} (hy : y ∈ Set.Icc (omegaCutoff N q) (sourceT N)) :
    20 ≤ sourceL N / Real.log ((q : ℝ) * y) := by
  have hy0 : 0 < y := by linarith [Parameters.omegaCutoff_ge (NeZero.pos q) hq, hy.1]
  have hs : 0 < Real.log ((q : ℝ) * y) := by
    linarith [original_log_product_ge_ten hN hy.1]
  apply (le_div_iff₀ hs).mpr
  have hu := original_log_product_upper hN hq hy0 hy.2
  have hl := log_le_height_linear (Parameters.sourceL_ge_3100 hN)
  linarith

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.HeightCases
