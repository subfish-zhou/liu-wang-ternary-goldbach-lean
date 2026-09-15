import LiuWang.Proof.Campaign20260915.Density.SharpRecovery
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.Campaign20260915.Density

theorem cosh_sixth_lower (u : ℝ) :
    1 + u ^ 2 / 2 + u ^ 4 / 24 + u ^ 6 / 720 ≤ Real.cosh u := by
  have h := (Real.hasSum_cosh u).summable.sum_le_tsum (Finset.range 4)
    (fun n _ => by rw [pow_mul]; positivity)
  rw [(Real.hasSum_cosh u).tsum_eq] at h
  norm_num [Finset.sum_range_succ] at h
  nlinarith only [h]

theorem logistic_point_polynomial {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ 0.9 - u + 0.225 * u ^ 2 + 0.01875 * u ^ 4 + 0.000625 * u ^ 6 := by
  by_cases hle : u ≤ 1.5
  · have h4 := mul_nonneg (sq_nonneg (u - 1.5))
      (show 0 ≤ u ^ 2 + 3 * u + 6.75 by positivity)
    have h6 := mul_nonneg (sq_nonneg (u - 1.5))
      (show 0 ≤ u ^ 4 + 3 * u ^ 3 + 6.75 * u ^ 2 + 13.5 * u + 25.3125 by positivity)
    nlinarith only [hle, sq_nonneg (u - 1.5), h4, h6]
  · let v : ℝ := u - 1.5
    have hv : 0 ≤ v := by dsimp [v]; linarith
    have he : u = v + 1.5 := by dsimp [v]; ring
    rw [he]
    have h : 0 ≤ 0.9 - (v + 1.5) + 0.225 * (v + 1.5) ^ 2 +
        0.01875 * (v + 1.5) ^ 4 + 0.000625 * (v + 1.5) ^ 6 -
          (1 / 2) * (v - 0.05) ^ 2 := by
      ring_nf
      positivity
    nlinarith only [h, sq_nonneg (v - 0.05)]

theorem logistic_point_kernel {u : ℝ} (hu : 0 ≤ u) :
    u / (Real.exp u + Real.exp (-u) + 2) ≤ 0.225 := by
  apply (div_le_iff₀ (by positivity)).mpr
  have hc := cosh_sixth_lower u
  rw [Real.cosh_eq] at hc
  nlinarith only [hc, logistic_point_polynomial hu]

end LiuWang.Proof.Campaign20260915.Density
