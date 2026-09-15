import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Row0
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Row1
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Row2
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Row3
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Row4
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Row5
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Row6
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Row7

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem checked_fixedUpper : fixedUpper ≤ (3576563023348683473612337603734234941773 / 10000000000000000000000000000000000000000000000000000 : ℝ) := by
  have h0 := checked_row_0
  have h1 := checked_row_1
  have h2 := checked_row_2
  have h3 := checked_row_3
  have h4 := checked_row_4
  have h5 := checked_row_5
  have h6 := checked_row_6
  have h7 := checked_row_7
  norm_num only [div_one] at h0 h1 h2 h3 h4 h5 h6 h7
  unfold fixedUpper
  nlinarith only [h0,h1,h2,h3,h4,h5,h6,h7]

theorem fixed_arithmetic_certificate :
    fixedUpper + 1 / 1000000000000000000000000000 ≤ 368 / 1000000000000000 := by
  have h := checked_fixedUpper
  linarith only [h]

#print axioms checked_fixedUpper
#print axioms fixed_arithmetic_certificate

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
