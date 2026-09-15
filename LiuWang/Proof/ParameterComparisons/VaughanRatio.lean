import LiuWang.Proof.Parameters.Main

/-! Source-sign audit for the ratio on page 173. This identifies the direction
of one intermediate comparison, not the truth of the paper's final theorem. -/
set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.ParameterComparisons
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

theorem log_sourceVaughanU_lt_two_thirds_log_quotient {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) :
    Real.log (sourceVaughanU N) < (2 / 3 : ℝ) *
      Real.log ((N : ℝ) / sourceVaughanV N) := by
  rw [log_sourceVaughanU hN, Real.log_div (natCast_pos_of_exp_le hN).ne'
    (sourceVaughanV_pos hN).ne', log_sourceVaughanV hN]
  change (2 * sourceL N - 4 * Real.log (sourceL N)) / 5 <
    (2 / 3 : ℝ) * (sourceL N - (2 * sourceL N + Real.log (sourceL N)) / 5)
  have hlog : 0 < Real.log (sourceL N) :=
    Real.log_pos (by linarith [sourceL_ge_2000 hN])
  linarith

theorem sourceVaughan_log_ratio_lt_two_thirds {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) :
    Real.log (sourceVaughanU N) /
      Real.log ((N : ℝ) / sourceVaughanV N) < (2 / 3 : ℝ) := by
  have hp : 0 < Real.log ((N : ℝ) / sourceVaughanV N) := by
    apply Real.log_pos
    exact (one_lt_div (sourceVaughanV_pos hN)).mpr (sourceVaughanV_lt_natCast hN)
  exact (div_lt_iff₀ hp).mpr (log_sourceVaughanU_lt_two_thirds_log_quotient hN)

end LiuWang.Proof.ParameterComparisons
