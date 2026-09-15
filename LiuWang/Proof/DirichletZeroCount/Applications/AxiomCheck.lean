import LiuWang.Proof.DirichletZeroCount.Applications.RightLimit

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.DirichletZeroCount.Applications

example : (familyCount 1 (1 / 2) 10000 : ℝ) ≤ sourceSevenBound 1 (1 / 2) 10000 :=
  familyCount_le_sourceSeven_low 1 (by norm_num) le_rfl (by norm_num)

example : (familyCount 1 (2 / 3) 10000 : ℝ) ≤ sourceSevenBound 1 (2 / 3) 10000 :=
  familyCount_le_sourceSeven_low 1 (by norm_num) (by norm_num) le_rfl

example {alpha y : ℝ} (hy : 100000 ≤ y) (ha : 1 / 2 ≤ alpha)
    (ha' : alpha ≤ 1 / 2 + 2 * sourceDelta y) :
    (familyCount 1 alpha y : ℝ) ≤ sourceSevenBound 1 alpha y := by
  exact familyCount_le_sourceSeven_original_low 1 (by simpa using hy) ha ha'

example {q : ℕ} [NeZero q] (chi : Character q) :
    zeroValues chi (1 / 2) 0 = LiuWang.Proof.CompleteExpansion.zeroValues chi 0 :=
  half_values_eq_complete chi 0

#print axioms familyCount_le_ten
#print axioms familyCount_le_sourceSeven_low
#print axioms familyCount_le_sourceSeven_original_low
#print axioms half_values_eq_complete
#print axioms familyCount_eq_complete_filter
#print axioms complete_family_le_sourceSeven_original_low
#print axioms zeroPacket_eq_count_values
#print axioms normalized_complete_inverse_sourceSeven_original_low
#print axioms normalized_complete_inverse_sqrt_sourceSeven_original_low
#print axioms exists_common_count_plateau
#print axioms familyCount_continuousWithinAt_right
#print axioms zeroValueSum_continuousWithinAt_right
