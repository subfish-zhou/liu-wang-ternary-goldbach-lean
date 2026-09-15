import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountCap.Parameters

set_option autoImplicit false
noncomputable section
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountCap

theorem window_denominator_pos {x beta : ℝ} (hx : 8000000000 ≤ x) (hb : beta < 1) :
    0 < lwdSourceSigma x - beta := by
  linarith [(lwd_source_parameters hx).2.2.1]

theorem window_reciprocal_lower {x beta : ℝ} (hx : 8000000000 ≤ x)
    (hb : beta < 1) (hwindow : 1 - 0.26213 / Real.log x ≤ beta) :
    Real.log x / (lwdSourceA x + 0.26213) ≤ 1 / (lwdSourceSigma x - beta) := by
  have hL : 0 < Real.log x := by linarith [original_log_lower hx]
  have ha := (lwd_source_parameters hx).1
  have hac : 0 < lwdSourceA x + 0.26213 := by linarith
  have hd := window_denominator_pos hx hb
  have hden : lwdSourceSigma x - beta ≤ (lwdSourceA x + 0.26213) / Real.log x := by
    unfold lwdSourceSigma
    rw [add_div]
    linarith only [hwindow]
  have hh := one_div_le_one_div_of_le hd hden
  simpa only [one_div_div] using hh

theorem original_2_28_negative {x beta eta theta : ℝ} (hx : 8000000000 ≤ x)
    (hb : beta < 1) (he : eta < 1) (ht : theta < 1)
    (hwb : 1 - 0.26213 / Real.log x ≤ beta)
    (hwe : 1 - 0.26213 / Real.log x ≤ eta)
    (hwt : 1 - 0.26213 / Real.log x ≤ theta) :
    1 / (lwdSourceSigma x - 1) -
      (1 / (lwdSourceSigma x - beta) + 1 / (lwdSourceSigma x - eta) +
        1 / (lwdSourceSigma x - theta)) +
      7 * stechkinConductorCoeff * Real.log x + 2.4998 < 0 := by
  have hL : 0 < Real.log x := by linarith [original_log_lower hx]
  have ha := (lwd_source_parameters hx).1
  have hac : 0 < lwdSourceA x + 0.26213 := by linarith
  have hb' := window_reciprocal_lower hx hb hwb
  have he' := window_reciprocal_lower hx he hwe
  have ht' := window_reciprocal_lower hx ht hwt
  have hn := mul_neg_of_pos_of_neg hL (original_normalized_negative hx)
  have hid : Real.log x *
      (1 / lwdSourceA x - 3 / (lwdSourceA x + 0.26213) +
        (7 * stechkinConductorCoeff + 2.4998 / Real.log x)) =
      1 / (lwdSourceSigma x - 1) - 3 * (Real.log x / (lwdSourceA x + 0.26213)) +
        7 * stechkinConductorCoeff * Real.log x + 2.4998 := by
    unfold lwdSourceSigma
    rw [add_sub_cancel_left, one_div_div]
    field_simp
    ring
  rw [hid] at hn
  linarith only [hn, hb', he', ht']

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountCap
