import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536.Counts

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.MultiZeroRepulsion LiuWang.Proof.MultiZeroRepulsion.Continuation

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536

theorem actual_T2_strict_count {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y : ℝ} (hy : omegaCutoff N q ≤ y) :
    strictFamilyCount q (1 - 0.2067 / Real.log ((q : ℝ) * y)) y ≤ 2 := by
  have hd := original_table_domain hN hq hy
  have hqx : (q : ℝ) ≤ (q : ℝ) * y := by
    simpa using mul_le_mul_of_nonneg_left hd.1 (Nat.cast_nonneg q)
  have hh := general_theorem_two
    (show (8000000000 : ℝ) ≤ (q : ℝ) * y by linarith [hd.2.1]) hqx
  have he : (q : ℝ) * y / q = y :=
    mul_div_cancel_left₀ y (Nat.cast_ne_zero.mpr (NeZero.ne q))
  simpa only [he, show (2067 / 10000 : ℝ) = 0.2067 by norm_num] using hh

theorem actual_T2_strict_slots {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y : ℝ} (hy : omegaCutoff N q ≤ y) :
    Fintype.card (ZeroSlots q (1 - 0.2067 / Real.log ((q : ℝ) * y)) y) ≤ 2 := by
  rw [card_zeroSlots]
  exact actual_T2_strict_count hN hq hy

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536
