import LiuWang.Proof.Campaign20260915.ZetaWinding.DigammaQuadrature

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Finset Filter
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaWinding

theorem reciprocalProfile_tendsto_zero {a : ℝ} (ha : 0 < a) (y : ℝ) :
    Tendsto (fun n : ℕ => reciprocalProfile a y n) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (a + n)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop a
      (tendsto_natCast_atTop_atTop (R := ℝ)))
  apply squeeze_zero (fun n => by unfold reciprocalProfile; positivity) ?_ ht
  intro n
  have hn : 0 < a + n := by positivity
  change (a + n) / ((a + n)^2 + y^2) ≤ _
  rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) hn]
  nlinarith [sq_nonneg y]

theorem reciprocalPrimitive_log_boundary {a : ℝ} (ha : 0 < a) (y : ℝ) :
    Tendsto (fun n : ℕ => Real.log n - reciprocalPrimitive a y n) atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have harg : Tendsto (fun n : ℕ => (1 + a / n)^2 + (y / n)^2) atTop (𝓝 (1 : ℝ)) := by
    simpa only [mul_zero, add_zero, one_pow, zero_pow (by decide : 2 ≠ 0), div_eq_mul_inv] using
      (((hi.const_mul a).const_add 1).pow 2).add ((hi.const_mul y).pow 2)
  have hl : Tendsto (fun n : ℕ => -Real.log ((1 + a / n)^2 + (y / n)^2) / 2)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Real.log_one, neg_zero, zero_div, Function.comp_def] using!
      ((Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp harg).neg.div_const 2
  apply hl.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have har : 0 < (1 + a / n)^2 + (y / n)^2 := by positivity
  have he : (a + n)^2 + y^2 = (n : ℝ)^2 * ((1 + a / n)^2 + (y / n)^2) := by
    field_simp
    ring
  rw [reciprocalPrimitive, he, Real.log_mul (pow_ne_zero 2 hnp.ne') har.ne', Real.log_pow]
  norm_num
  ring

theorem digamma_reciprocal_partial_sums {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun N : ℕ => (harmonic N : ℝ) -
      ∑ n ∈ range N, reciprocalProfile z.re z.im n) atTop
      (𝓝 ((digamma z).re + Real.eulerMascheroniConstant)) := by
  have hp : ∀ n : ℕ, z ≠ -(n : ℂ) := by
    intro n he
    have h := hz
    rw [he] at h
    simp at h
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hh := (Complex.hasSum_re (Complex.hasSum_digamma hp)).tendsto_sum_nat
  have he (n : ℕ) :
      (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + z)).re =
        ((n : ℝ) + 1)⁻¹ - reciprocalProfile z.re z.im n := by
    simp [one_div, inv_re, normSq_apply, reciprocalProfile, add_comm]
    field_simp
  simp_rw [he] at hh
  simpa only [Finset.sum_sub_distrib, Complex.sum_inv_natCast_add_one_real, add_re, ofReal_re] using hh

theorem digamma_re_stirling_error {z : ℂ} (hz : 0 < z.re) :
    |(digamma z).re - Real.log ‖z‖ + (1 / z).re / 2| ≤ 3 / (8 * normSq z) := by
  have ht := (((Real.tendsto_harmonic_sub_log.sub (digamma_reciprocal_partial_sums hz)).add
    (reciprocalPrimitive_log_boundary hz z.im)).add
      ((reciprocalProfile_tendsto_zero hz z.im).div_const 2)).add_const
        (reciprocalPrimitive z.re z.im 0 - reciprocalProfile z.re z.im 0 / 2)
  have hlim : Tendsto
      (fun N : ℕ => (∑ n ∈ range N, reciprocalProfile z.re z.im n) +
        (reciprocalProfile z.re z.im N - reciprocalProfile z.re z.im 0) / 2 -
        (reciprocalPrimitive z.re z.im N - reciprocalPrimitive z.re z.im 0))
      atTop (𝓝 (reciprocalPrimitive z.re z.im 0 -
        reciprocalProfile z.re z.im 0 / 2 - (digamma z).re)) := by
    convert! ht using 1 <;> (try funext N) <;> ring
  have hb := le_of_tendsto hlim.abs
    (Eventually.of_forall (reciprocal_quadrature_bound hz z.im))
  have hf : reciprocalProfile z.re z.im 0 = (1 / z).re := by
    simp [reciprocalProfile, one_div, inv_re, normSq_apply, pow_two]
  have hF : reciprocalPrimitive z.re z.im 0 = Real.log ‖z‖ := by
    rw [reciprocalPrimitive, add_zero, show z.re^2 + z.im^2 = normSq z by simp [normSq_apply, pow_two],
      normSq_eq_norm_sq, Real.log_pow]
    norm_num
  rw [hf, hF] at hb
  have he : Real.log ‖z‖ - (1 / z).re / 2 - (digamma z).re =
      -((digamma z).re - Real.log ‖z‖ + (1 / z).re / 2) := by ring
  simpa only [he, abs_neg, normSq_apply, pow_two] using hb

#print axioms reciprocalPrimitive_log_boundary
#print axioms digamma_reciprocal_partial_sums
#print axioms digamma_re_stirling_error

end LiuWang.Proof.Campaign20260915.ZetaWinding
