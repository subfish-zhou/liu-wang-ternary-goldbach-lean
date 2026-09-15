import LiuWang.Proof.Campaign20260915.Totient.RSTheorem27Coefficient

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
open LiuWang.Proof.Campaign20260915.Totient

namespace LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel

theorem unweighted_laplace_integral {b v : ℝ} (hv : 0 < v) (hb : b < v) :
    IntegrableOn (rsLaplace 1 0 b) (Ioi v) ∧
      (∫ u in Ioi v, rsLaplace 1 0 b u) = Real.exp (-v) * (1 + v - b) := by
  have hd (u : ℝ) (hu : u ∈ Ici v) :
      HasDerivAt (fun t => -rsLaplacePrimitive 1 0 b t) (rsLaplace 1 0 b u) u := by
    simpa [rsLaplaceCorrection, Pi.neg_apply] using!
      (rsLaplacePrimitive_deriv (c := 0) (by norm_num : (0 : ℝ) < 1)
        (hv.trans_le hu) (hb.trans_le hu)).neg
  have hn (u : ℝ) (hu : u ∈ Ioi v) : 0 ≤ rsLaplace 1 0 b u := by
    exact mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (hb.le.trans hu.le))
  have ht : Tendsto (fun t => -rsLaplacePrimitive 1 0 b t) atTop (𝓝 0) := by
    simpa using (rsLaplacePrimitive_tendsto (c := 0) (b := b)
      (by norm_num : (0 : ℝ) < 1)).neg
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hn ht, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hd hn ht]
  simp only [rsLaplacePrimitive, one_pow, div_one, zero_div, sub_zero,
    neg_one_mul, sub_neg_eq_add, zero_add]
  ring

/-- The integral in RS1962 (8.1), with no fixed cutoff or upper bound on log x. -/
theorem unweighted_phi_integral {K : ℝ} (hK : rsA ≤ K) :
    IntegrableOn (fun t => rsPhi 1 0 t * Real.log (t / (2 * Real.pi))) (Ioi K) ∧
      (∫ t in Ioi K, rsPhi 1 0 t * Real.log (t / (2 * Real.pi))) =
        (1 + Real.log (K / (2 * Real.pi))) / K := by
  have hK0 : 0 < K := lt_of_lt_of_le (by norm_num) (rsA_ge_thousand.trans hK)
  have hv : 999 / 100 ≤ Real.log K := (Real.le_log_iff_exp_le hK0).mpr hK
  have hb : Real.log (2 * Real.pi) < Real.log K := by
    linarith [rs_log_two_pi_interval.2]
  have hi := unweighted_laplace_integral (by linarith : 0 < Real.log K) hb
  have hf : (fun u => Real.exp u •
      (rsPhi 1 0 (Real.exp u) * Real.log (Real.exp u / (2 * Real.pi)))) =
      rsLaplace 1 0 (Real.log (2 * Real.pi)) := by
    funext u
    simpa using rs_phi_exp_change 1 0 u
  have hc := integral_comp_exp_Ioi
    (fun t => rsPhi 1 0 t * Real.log (t / (2 * Real.pi))) (Real.log K)
  have he := integrableOn_comp_exp_Ioi
    (fun t => rsPhi 1 0 t * Real.log (t / (2 * Real.pi))) (Real.log K)
  rw [hf, Real.exp_log hK0] at hc he
  refine ⟨he.mp hi.1, ?_⟩
  rw [← hc, hi.2, Real.exp_neg, Real.exp_log hK0,
    Real.log_div hK0.ne' (by positivity)]
  ring

theorem unweighted_phi_coefficient {K : ℝ} (hK : rsA ≤ K) :
    rsQ K * (∫ t in Ioi K, rsPhi 1 0 t * Real.log (t / (2 * Real.pi))) ≤
      0.1592 * (1 + Real.log (K / (2 * Real.pi))) / K := by
  rw [(unweighted_phi_integral hK).2]
  have hK0 : 0 < K := lt_of_lt_of_le (by norm_num) (rsA_ge_thousand.trans hK)
  have hl : 0 ≤ Real.log (K / (2 * Real.pi)) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ (by positivity)).mpr
    linarith [rsA_ge_thousand.trans hK, Real.pi_lt_four]
  exact (mul_le_mul_of_nonneg_right (rsQ_le_original hK)
    (div_nonneg (by linarith) hK0.le)).trans_eq (by ring)

#print axioms unweighted_phi_integral
#print axioms unweighted_phi_coefficient

end LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel
