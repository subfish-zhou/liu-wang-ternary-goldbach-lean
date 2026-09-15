import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536.FiniteIntegral
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536.Signed

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536

theorem scalar35_uniform {L : ℝ} (hL : 3100 ≤ L) : scalar35 L ≤ 0.0102654 := by
  have hr := source35_all_real_reduction hL
  have hc := signed_core_upper profile35_continuousOn (fun _ _ => profile35_nonneg)
    firstA (fun _ => integrand35_signed_upper)
  have hp := primary35_paid
  have hn : 2 * (fee35 + 1 / 10000000) + 1 / 100000000 -
      20 * ((3100 : ℝ) ^ 4 / 3 ^ 69) + 1 / 10000000000 ≤ 0.0102654 := by norm_num [fee35]
  linarith

theorem scalar36_uniform {L : ℝ} (hL : 3100 ≤ L) : scalar36 L ≤ 0.0016 := by
  have hr := source36_all_real_reduction hL
  have hc := signed_core_upper profile36_continuousOn (fun _ _ => profile36_nonneg)
    secondA (fun _ => integrand36_signed_upper)
  have hp := primary36_paid
  have hn : 2 * (fee36 + 1 / 10000000) + 1 / 100000000 -
      20 * ((3100 : ℝ) ^ 4 / 3 ^ 69) + 1 / 10000000000 ≤ 0.0016 := by norm_num [fee36]
  linarith

theorem original_source35_scalar {L : ℝ} (hL : 3100 ≤ L) :
    (∫ s in Real.log (3.36 * L ^ 3)..Real.log (L ^ 3 * L ^ 15),
      L ^ 4 * Real.exp (-s) *
        (2 * Real.exp (-L / (9.645908801 * s)) +
          11 * Real.exp (-0.3221 * L / s) + 7 * Real.exp (-0.33 * L / s) -
            20 * Real.exp (-0.36 * L / s))) ≤ 0.0102654 :=
  scalar35_uniform hL

theorem original_source36_scalar {L : ℝ} (hL : 3100 ≤ L) :
    (∫ s in Real.log (3.36 * L ^ 3)..Real.log (L ^ 3 * L ^ 15),
      L ^ 4 * Real.exp (-s) *
        (2 * Real.exp (-0.12 * L / s) + 6 * Real.exp (-0.2743 * L / s) +
          Real.exp (-0.28 * L / s) + Real.exp (-0.3 * L / s) +
          Real.exp (-0.31 * L / s) + 2 * Real.exp (-0.32 * L / s) +
          7 * Real.exp (-0.33 * L / s) - 20 * Real.exp (-0.36 * L / s))) ≤ 0.0016 :=
  scalar36_uniform hL

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536
