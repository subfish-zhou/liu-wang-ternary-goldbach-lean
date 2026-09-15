import LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel.UnweightedIntegral

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open MeasureTheory Set
open LiuWang.Proof.Campaign20260915.Totient
open LiuWang.Proof.ChebyshevBound.HighHeight

namespace LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel

/-- The scalar payment in RS1962 (8.2), not a certificate for the zero sum.
The expanded remainder is Rosser 1941, p. 223, with coefficient 0.443. -/
theorem original_boundary_integral_budget :
    2 * (0.137 * Real.log rsA + 0.443 * Real.log (Real.log rsA) + 1.588) / rsA ^ 2 +
      0.1592 * (∫ t in Ioi rsA, rsPhi 1 0 t * Real.log (t / (2 * Real.pi))) <
        Real.exp (-9.61) := by
  rw [(unweighted_phi_integral (le_refl rsA)).2]
  have hA : 2916 ≤ rsA := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 54)
      exp_four_ge_fifty_four 2
    rw [← Real.exp_nat_mul] at h
    norm_num at h
    exact h.trans (Real.exp_le_exp.mpr (by norm_num))
  have hA0 : 0 < rsA := lt_of_lt_of_le (by norm_num) hA
  have hlog : Real.log rsA = 999 / 100 := Real.log_exp _
  have hll : Real.log (Real.log rsA) ≤ 3 := by
    rw [hlog]
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 999 / 100)
      (by norm_num : (999 / 100 : ℝ) ≤ 2 ^ 4)
    rw [Real.log_pow] at h
    linarith [Real.log_two_lt_d9]
  have hR : 0.137 * Real.log rsA + 0.443 * Real.log (Real.log rsA) + 1.588 ≤ 4.3 := by
    rw [hlog] at hll ⊢
    linarith
  have hboundary :
      2 * (0.137 * Real.log rsA + 0.443 * Real.log (Real.log rsA) + 1.588) / rsA ≤
        (8.6 : ℝ) / 2916 := by
    exact (div_le_div_of_nonneg_right (by linarith : 2 *
      (0.137 * Real.log rsA + 0.443 * Real.log (Real.log rsA) + 1.588) ≤ 8.6)
      hA0.le).trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hA)
  have hmain : 0.1592 * (1 + Real.log (rsA / (2 * Real.pi))) ≤ 1.458 := by
    rw [Real.log_div hA0.ne' (by positivity), hlog]
    linarith [rs_log_two_pi_interval.1]
  have hex := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 19 / 50) 4
  norm_num [Finset.sum_range_succ] at hex
  have hnormalized :
      2 * (0.137 * Real.log rsA + 0.443 * Real.log (Real.log rsA) + 1.588) / rsA +
        0.1592 * (1 + Real.log (rsA / (2 * Real.pi))) < Real.exp (19 / 50) := by
    linarith
  have he : Real.exp (-9.61) * rsA = Real.exp (19 / 50) := by
    rw [rsA, ← Real.exp_add]
    norm_num
  calc
    _ = (2 * (0.137 * Real.log rsA + 0.443 * Real.log (Real.log rsA) + 1.588) / rsA +
        0.1592 * (1 + Real.log (rsA / (2 * Real.pi)))) / rsA := by ring
    _ < _ := (div_lt_iff₀ hA0).mpr (by rw [he]; exact hnormalized)

#print axioms original_boundary_integral_budget

end LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel
