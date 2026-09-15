import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic.Counting

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic

theorem positiveBelow_one : positiveBelow 1 = ∅ := by
  norm_num [positiveBelow]

theorem squarefreeCount_one : squarefreeCount 1 = 0 := by
  simp [squarefreeCount, positiveBelow_one]

theorem strict_square_endpoint (k : ℕ) :
    k ∉ positiveBelow (Real.sqrt ((k : ℝ) ^ 2)) := by
  simp [mem_positiveBelow, Real.sqrt_sq (Nat.cast_nonneg k)]

theorem strict_multiple_endpoint {d k : ℕ} (hd : 0 < d) :
    ((positiveBelow ((d * k : ℕ) : ℝ)).filter (fun n => d ∣ n)).card = k - 1 := by
  rw [strict_multiples_card hd, Nat.cast_mul, mul_div_cancel_left₀ _ (by positivity)]
  simp [positiveBelow]

theorem strict_four_multiples :
    ((positiveBelow 4).filter (fun n => 2 ∣ n)).card = 1 := by
  simpa using strict_multiple_endpoint (d := 2) (k := 2) (by decide)

end LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic
