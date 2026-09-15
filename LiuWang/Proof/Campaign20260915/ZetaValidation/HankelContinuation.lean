import LiuWang.Proof.Campaign20260915.ZetaValidation.HankelArcAnalytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Analytic.Uniqueness

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory Filter
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def rsHankelPrefactor (s : ℂ) : ℂ :=
  exp (log (2 * Real.pi : ℂ) * s + Real.pi * I * s / 2) *
    (Gamma s)⁻¹ / (exp (2 * Real.pi * I * s) - 1)

theorem rsHankelPrefactor_eq (s : ℂ) :
    rsHankelPrefactor s = (2 * Real.pi : ℂ) ^ s * exp (Real.pi * I * s / 2) /
      (Gamma s * (exp (2 * Real.pi * I * s) - 1)) := by
  rw [rsHankelPrefactor, cpow_def_of_ne_zero
    (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)), exp_add]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem rsHankelPrefactor_differentiableAt {s : ℂ} (hs : 0 < s.im) :
    DifferentiableAt ℂ rsHankelPrefactor s := by
  exact ((show DifferentiableAt ℂ
    (fun q : ℂ => exp (log (2 * Real.pi : ℂ) * q + Real.pi * I * q / 2)) s by
      fun_prop).mul (differentiable_one_div_Gamma s)).div
        (by fun_prop) (rsHankel_jump_ne_zero hs)

theorem rsFiniteDirichletSum_differentiable (m : ℕ) :
    Differentiable ℂ (fun s : ℂ => ∑ n ∈ Finset.range m, 1 / (n + 1 : ℂ) ^ s) := by
  apply Differentiable.fun_sum
  intro n _
  have hn : (n + 1 : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero n)
  simp_rw [cpow_def_of_ne_zero hn, one_div]
  exact (show Differentiable ℂ (fun s : ℂ => exp (log (n + 1 : ℂ) * s)) by
    fun_prop).inv (fun _ => exp_ne_zero _)

theorem zeta_eq_fixed_hankel_upper {m : ℕ} (hm : 0 < m) {u : ℝ} (hu : u < 0)
    {s : ℂ} (hs : 0 < s.im) :
    riemannZeta s = (∑ n ∈ Finset.range m, 1 / (n + 1 : ℂ) ^ s) +
      rsHankelPrefactor s * rsHankelC1 s m u := by
  let U : Set ℂ := {z | 0 < z.im}
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_im
  have hUc : IsPreconnected U := ((convex_Ioi (0 : ℝ)).linear_preimage imLm).isPreconnected
  have hz : AnalyticOnNhd ℂ riemannZeta U := by
    apply DifferentiableOn.analyticOnNhd _ hUo
    intro z hz
    apply (differentiableAt_riemannZeta ?_).differentiableWithinAt
    intro he
    simp [U, he] at hz
  have hf : AnalyticOnNhd ℂ (fun z : ℂ =>
      (∑ n ∈ Finset.range m, 1 / (n + 1 : ℂ) ^ z) +
        rsHankelPrefactor z * rsHankelC1 z m u) U := by
    apply DifferentiableOn.analyticOnNhd _ hUo
    intro z hz
    exact ((rsFiniteDirichletSum_differentiable m z).add
      ((rsHankelPrefactor_differentiableAt hz).mul
        (rsHankelC1_differentiable hm hu z))).differentiableWithinAt
  have he : riemannZeta =ᶠ[𝓝 (2 + I)] (fun z : ℂ =>
      (∑ n ∈ Finset.range m, 1 / (n + 1 : ℂ) ^ z) +
        rsHankelPrefactor z * rsHankelC1 z m u) := by
    have hR : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 + I) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
    have hI : U ∈ 𝓝 (2 + I) := hUo.mem_nhds (by norm_num [U])
    filter_upwards [hR, hI] with z hzR hzI
    rw [rsHankelPrefactor_eq]
    exact zeta_eq_sum_add_fixed_hankel hm hzR hzI hu
  exact hz.eqOn_of_preconnected_of_eventuallyEq hf hUc (by norm_num [U] : 2 + I ∈ U) he hs

theorem zeta_eq_sum_add_fixed_hankel_critical_strip {m : ℕ} (hm : 0 < m)
    {s : ℂ} (ht : 0 < s.im) {u : ℝ} (hu : u < 0) :
    riemannZeta s = (∑ n ∈ Finset.range m, 1 / (n + 1 : ℂ) ^ s) +
      ((2 * Real.pi : ℂ) ^ s * exp (Real.pi * I * s / 2) /
        (Gamma s * (exp (2 * Real.pi * I * s) - 1))) * rsHankelC1 s m u := by
  rw [← rsHankelPrefactor_eq]
  exact zeta_eq_fixed_hankel_upper hm hu ht

theorem rsHankelC1_radius_independent {m : ℕ} (hm : 0 < m) {u v : ℝ}
    (hu : u < 0) (hv : v < 0) (s : ℂ) :
    rsHankelC1 s m u = rsHankelC1 s m v := by
  have he : (fun z : ℂ => rsHankelC1 z m u) =ᶠ[𝓝 (2 : ℂ)] (fun z => rsHankelC1 z m v) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (2 : ℂ) ∈ {z : ℂ | 1 < z.re})] with z hz
    exact rsHankelC1_initial_independent hm hz hu hv
  exact ((rsHankelC1_differentiable hm hu).differentiableOn.analyticOnNhd isOpen_univ
    ).eqOn_of_preconnected_of_eventuallyEq
    ((rsHankelC1_differentiable hm hv).differentiableOn.analyticOnNhd isOpen_univ)
    isPreconnected_univ (mem_univ _) he (mem_univ s)

end LiuWang.Proof.Campaign20260915.ZetaValidation
