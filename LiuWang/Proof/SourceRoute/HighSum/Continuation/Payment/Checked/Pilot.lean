import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Bounds

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem pilot_exp_upper : expNegUpper (46948577783733940881 / 676601617795489000 : ℝ) ≤ (733261561190919419785343723617 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (859807 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
