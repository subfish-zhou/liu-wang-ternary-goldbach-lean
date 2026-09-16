import LiuWang.Proof.Campaign20260915.RosserCount.BacklundWeightedVariation

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open Complex

namespace LiuWang.Proof.Campaign20260915.RosserCount

open LiuWang.Proof.Campaign20260915.Totient
open LiuWang.Proof.Campaign20260915.ZetaWinding

theorem positiveCount_backlund_integral_bound {T : ℝ} (hT : rsA ≤ T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0) :
    |(positiveCount T : ℝ) - rosserMain T| <
      (Real.circleAverage (backlundCircleEnvelope T) 0 (33 / 25 : ℝ) -
        Real.log ‖riemannZeta (backlundCenterPoint T)‖) /
          (2 * Real.log (44 / 25 : ℝ)) +
      |(backlundLog T (5 / 4)).im| / Real.pi +
      4 / (Real.pi * T) + |rosserGammaRemainder T| / Real.pi := by
  have hpos : 0 < T := by linarith [rsA_ge_thousand]
  let D := (positiveCount T : ℝ) - rosserMain T
  let S := rosserGammaRemainder T
  let P := (backlundLog T (5 / 4)).im
  let K := (Real.circleAverage (backlundCircleEnvelope T) 0 (33 / 25 : ℝ) -
    Real.log ‖riemannZeta (backlundCenterPoint T)‖) / (2 * Real.log (44 / 25 : ℝ))
  have hb : |Real.pi * D - S - P| ≤ K * Real.pi + 2 / T :=
    positiveCount_centered_weighted_envelope_bound hT hr
  have ht : Real.pi * |D| ≤ |Real.pi * D - S - P| + |P| + |S| := by
    calc
      _ = |Real.pi * D| := by rw [abs_mul, abs_of_pos Real.pi_pos]
      _ = |(Real.pi * D - S - P) + P + S| := by congr 1; ring
      _ ≤ |(Real.pi * D - S - P) + P| + |S| := abs_add_le _ _
      _ ≤ _ := add_le_add (abs_add_le _ _) le_rfl
  have he : (2 : ℝ) / T < 4 / T :=
    (div_lt_div_iff_of_pos_right hpos).mpr (by norm_num)
  have hn :
      Real.pi * (K + |P| / Real.pi + 4 / (Real.pi * T) + |S| / Real.pi) =
        K * Real.pi + 4 / T + |P| + |S| := by
    field_simp
    ring
  change |D| < K + |P| / Real.pi + 4 / (Real.pi * T) + |S| / Real.pi
  apply (mul_lt_mul_iff_right₀ Real.pi_pos).mp
  rw [hn]
  nlinarith only [hb, ht, he]

#print axioms positiveCount_backlund_integral_bound

end LiuWang.Proof.Campaign20260915.RosserCount
