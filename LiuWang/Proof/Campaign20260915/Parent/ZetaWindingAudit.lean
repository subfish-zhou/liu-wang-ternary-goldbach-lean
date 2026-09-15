import LiuWang.Proof.Campaign20260915.ZetaWinding.EndpointBridge

/-! Parent audit of the actual multiplicity-counting bridge.
No endpoint enclosures or sign records are supplied by this module.
In particular the original-height M04 input is not discharged.
-/
set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.Campaign20260915.Parent.ZetaWindingAudit
open LiuWang.Proof.Campaign20260915.ZetaWinding
open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem actual_count_from_segments {H : ℝ} (hH : 0 < H)
    (x : ℕ → ℝ) (c : ℕ → ℂ) (n : ℕ)
    (hx0 : x 0 = 1 / 2) (hxn : x n = 2)
    (hs : ∀ j < n, ∀ t ∈ Set.uIcc (x j) (x (j + 1)), 1 / 2 ≤ t)
    (hr : ∀ j < n, ∀ t ∈ Set.uIcc (x j) (x (j + 1)),
      0 < (c j * riemannZeta (horizontalAt H t)).re) :
    (zetaClosedCount H : ℝ) =
      2 * (xiCountingPrimitive (horizontalAt H 2) -
        xiCountingPrimitive 2 - horizontalPrimitiveSum H x c n).im / Real.pi :=
  zetaClosedCount_eq_segment_sum hH x c n hx0 hxn hs hr

#print axioms actual_count_from_segments
end LiuWang.Proof.Campaign20260915.Parent.ZetaWindingAudit

#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.rotated_re_pos_of_ball
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.rotated_log_increment_integer
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.localXiPrimitive_increment_integer
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.localXiPrimitive_hasDerivAt
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.xi_line_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.localXiPrimitive_line_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.horizontal_ball_of_endpoint_deriv
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.horizontal_rotated_pos_of_endpoint_deriv
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.partition_covers
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.horizontalPrimitiveSum_integer
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.horizontal_integral_eq_sum
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.zeta_height_nonzero_of_rotated_segments
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.xi_right_vertical_primitive_all
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.zetaClosedCount_eq_segment_sum
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.zetaClosedCount_eq_winding
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.winding_integer_unique
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.zetaClosedCount_eq_of_winding_window
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.zetaClosedCount_le_of_endpoint_upper
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.zeta_values_and_orders_of_matching_witnesses
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.zeta_all_simple_of_segment_upper_and_witnesses
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.witnesses_above_sixteen
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.zeta_all_simple_of_segments_and_signs
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.zeta_all_simple_of_endpoint_data
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.original_strict_height_of_endpoint_data
