import LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1.OriginalWindows

/-! The strip restriction is redundant for nonprincipal zeros in the original L2.1 window. -/

set_option autoImplicit false
noncomputable section

open Complex

namespace LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1

theorem originalCutoff_pos {x : ℝ} (hx : 10 ≤ x) : 0 < originalCutoff x := by
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (show 2 ≤ x by linarith)
  have hlog := Real.log_two_gt_d9
  have hd : 1 < 9.645908801 * Real.log x := by linarith
  have hi := (one_div_lt_one_div_of_lt zero_lt_one hd)
  norm_num only [div_one] at hi
  unfold originalCutoff
  linarith

theorem mem_original_window {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) {x : ℝ} (hx : 10 ≤ x) {rho : ℂ} :
    rho ∈ windowValues chi (originalCutoff x) (x / q) ↔
      chi.LFunction rho = 0 ∧
        1 - 1 / (9.645908801 * Real.log x) < rho.re ∧ |rho.im| ≤ x / q := by
  rw [mem_windowValues]
  constructor
  · exact fun h => ⟨h.1, h.2.2⟩
  · rintro ⟨hz, hr, ht⟩
    have hr0 : 0 < rho.re := (originalCutoff_pos hx).trans hr
    have hr1 : rho.re < 1 := by
      by_contra hh
      exact chi.LFunction_ne_zero_of_one_le_re (Or.inl hc) (le_of_not_gt hh) hz
    exact ⟨hz, ⟨hr0, hr1⟩, hr, ht⟩

end LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1
