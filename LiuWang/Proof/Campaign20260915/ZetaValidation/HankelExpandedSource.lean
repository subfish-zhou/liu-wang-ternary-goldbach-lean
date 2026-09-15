import LiuWang.Proof.Campaign20260915.ZetaValidation.SourceC2Connectors

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

theorem rsHankelExpanded_arc_integrable (s : ℂ) (m : ℕ) {M : ℕ} {R : ℝ}
    (hR : (M : ℝ) < R) (hR' : R < M + 1) :
    IntervalIntegrable (fun θ : ℝ => I * exp ((Real.log R : ℂ) + θ * I) *
      rsHankelKernel s m (exp ((Real.log R : ℂ) + θ * I))) volume
        (-(Real.pi / 4)) (5 * Real.pi / 4) := by
  have hR0 : 0 < R := lt_of_le_of_lt (Nat.cast_nonneg M) hR
  have hc : ContinuousOn (fun θ : ℝ => rsHankelLift s m ((Real.log R : ℂ) + θ * I))
      (uIcc (-(Real.pi / 4)) (5 * Real.pi / 4)) := by
    intro θ hθ
    rw [uIcc_of_le (by linarith [Real.pi_pos] : -(Real.pi / 4) ≤ 5 * Real.pi / 4)] at hθ
    have hlo : -(Real.pi / 2) < ((Real.log R : ℂ) + θ * I).im := by
      simp; linarith [hθ.1, Real.pi_pos]
    have hhi : ((Real.log R : ℂ) + θ * I).im < 3 * Real.pi / 2 := by
      simp; linarith [hθ.2, Real.pi_pos]
    have hn : rsLiftDenominator ((Real.log R : ℂ) + θ * I) ≠ 0 := by
      intro hd
      obtain ⟨n, hn, hw⟩ := (rsLiftDenominator_zero_iff hlo hhi).mp hd
      have hr := congrArg Complex.re hw
      rw [rsHankelLog_int_re] at hr
      have he := congrArg Real.exp hr
      have hn0 : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
        zero_mul, sub_zero, add_zero, Real.exp_log hR0, Real.exp_log hn0] at he
      have hz : (M : ℤ) < |n| ∧ |n| < (M : ℤ) + 1 := by
        have hh : (M : ℝ) < |(n : ℝ)| ∧ |(n : ℝ)| < M + 1 := he ▸ ⟨hR, hR'⟩
        exact_mod_cast hh
      omega
    exact (ContinuousAt.comp (f := fun θ : ℝ => (Real.log R : ℂ) + θ * I)
      (rsHankelLift_analytic_off s m hn).continuousAt (by fun_prop)).continuousWithinAt
  apply (hc.intervalIntegrable.const_mul I).congr
  intro θ hθ
  have hh := uIoc_subset_uIcc hθ
  rw [uIcc_of_le (by linarith [Real.pi_pos] : -(Real.pi / 4) ≤ 5 * Real.pi / 4)] at hh
  dsimp only
  rw [rsHankelLift_actual s m (by simp; linarith [hh.1, Real.pi_pos])
    (by simp; linarith [hh.2, Real.pi_pos])]
  ring

theorem rsHankel_second_prefactor {s : ℂ} (ht : 0 < s.im) :
    rsHankelPrefactor s * (exp (Real.pi * I * s) - 1) =
      (2 * Real.pi : ℂ) ^ s / (2 * Gamma s * cos (Real.pi * s / 2)) := by
  let E : ℂ := exp (Real.pi * I * s / 2)
  have hE : E ≠ 0 := exp_ne_zero _
  have hsq : exp (Real.pi * I * s) = E ^ 2 := by
    dsimp only [E]
    rw [sq, ← exp_add]
    congr 1
    ring
  have hfour : exp (2 * Real.pi * I * s) = E ^ 4 := by
    rw [show 2 * Real.pi * I * s = Real.pi * I * s + Real.pi * I * s by ring,
      exp_add, hsq]
    ring
  have hcos : 2 * cos (Real.pi * s / 2) * E = E ^ 2 + 1 := by
    rw [two_cos]
    have ha : Real.pi * s / 2 * I = Real.pi * I * s / 2 := by ring
    have hb : -(Real.pi * s / 2) * I = -(Real.pi * I * s / 2) := by ring
    rw [ha, hb, exp_neg]
    change (E + E⁻¹) * E = E ^ 2 + 1
    field_simp
  have hd := rsHankel_jump_ne_zero ht
  rw [hfour] at hd
  have hprod : (E ^ 2 - 1) * (E ^ 2 + 1) ≠ 0 := by
    convert hd using 1
    ring
  have hminus := (mul_ne_zero_iff.mp hprod).1
  have hplus := (mul_ne_zero_iff.mp hprod).2
  have hc : cos (Real.pi * s / 2) ≠ 0 := by
    intro hc
    rw [hc, mul_zero, zero_mul] at hcos
    exact hplus hcos.symm
  rw [rsHankelPrefactor_eq, hsq, hfour]
  change ((2 * Real.pi : ℂ) ^ s * E / (Gamma s * (E ^ 4 - 1))) *
    (E ^ 2 - 1) = _
  by_cases hg : Gamma s = 0
  · simp [hg]
  · field_simp
    linear_combination (E ^ 2 - 1) * hcos

theorem zeta_eq_source_sums_add_expanded_hankel {m : ℕ} (hm : 0 < m)
    {s : ℂ} (ht : 0 < s.im) {R : ℝ} (hR : (m : ℝ) < R) (hR' : R < m + 1) :
    riemannZeta s = (∑ n ∈ Finset.range m, 1 / (n + 1 : ℂ) ^ s) +
      (2 * Real.pi : ℂ) ^ s / (2 * Gamma s * cos (Real.pi * s / 2)) *
        (∑ k ∈ Finset.range m, (k + 1 : ℂ) ^ (s - 1)) +
      rsHankelPrefactor s * rsHankelTiltedC1 s m (Real.log R) := by
  rw [zeta_eq_sum_add_expanded_hankel hm ht hR hR' hm, rsHankel_second_prefactor ht]

end LiuWang.Proof.Campaign20260915.ZetaValidation
