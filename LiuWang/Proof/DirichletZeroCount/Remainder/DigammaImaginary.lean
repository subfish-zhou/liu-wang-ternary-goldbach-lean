import LiuWang.Proof.DirichletZeroCount.Remainder.GammaUpper
import Mathlib.Analysis.SumIntegralComparisons

/-! # Height-uniform imaginary digamma bounds from its actual convergent series -/

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory
open scoped Classical

namespace LiuWang.Proof.DirichletZeroCount.Remainder

theorem digamma_im_hasSum {z : ℂ} (hz : 0 < z.re) :
    HasSum (fun n : ℕ => z.im / ((z.re + n) ^ 2 + z.im ^ 2)) (digamma z).im := by
  have hh := Complex.hasSum_im (hasSum_digamma_of_re_pos hz)
  simpa [sub_im, inv_im, normSq_apply, pow_two, neg_div] using hh

theorem poisson_tail_integral {a t : ℝ} (ht : 0 < t) (b : ℝ) :
    ∫ u in (0 : ℝ)..b, t / ((a + u) ^ 2 + t ^ 2) =
      Real.arctan ((a + b) / t) - Real.arctan (a / t) := by
  have hd (u : ℝ) : HasDerivAt (fun x : ℝ => Real.arctan ((a + x) / t))
      (t / ((a + u) ^ 2 + t ^ 2)) u := by
    convert! (((hasDerivAt_id u).const_add a).div_const t).arctan using 1
    dsimp only [id_eq]
    field_simp
    ring
  have hc : Continuous (fun u : ℝ => t / ((a + u) ^ 2 + t ^ 2)) :=
    continuous_const.div (by fun_prop) (fun u => ne_of_gt (by positivity))
  simpa only [add_zero] using intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hd u) (hc.intervalIntegrable 0 b)

theorem poisson_sum_le {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    ∑' n : ℕ, t / ((a + n) ^ 2 + t ^ 2) ≤
      t / (a ^ 2 + t ^ 2) + Real.pi / 2 := by
  rcases eq_or_lt_of_le ht with ht0 | ht
  · subst t
    simp only [zero_div, tsum_zero, zero_add]
    positivity
  let f (u : ℝ) := t / ((a + u) ^ 2 + t ^ 2)
  have hanti {n : ℕ} : AntitoneOn f (Set.Icc 0 (0 + n)) := by
    intro u hu v hv huv
    dsimp [f]
    gcongr
    linarith [hu.1]
  have hp (n : ℕ) : ∑ i ∈ Finset.range n, f ((i + 1 : ℕ) : ℝ) ≤ Real.pi / 2 := by
    have hi := (hanti (n := n)).sum_le_integral
    simp only [zero_add] at hi
    have hfull := poisson_tail_integral (a := a) ht (n : ℝ)
    have hnon := Real.arctan_nonneg.mpr (div_nonneg ha.le ht.le)
    have hupper := Real.arctan_lt_pi_div_two ((a + n) / t)
    apply hi.trans
    change (∫ u in (0 : ℝ)..(n : ℝ), t / ((a + u) ^ 2 + t ^ 2)) ≤ _
    rw [hfull]
    linarith
  have htail := Real.tsum_le_of_sum_range_le
    (f := fun n : ℕ => f ((n + 1 : ℕ) : ℝ)) (fun n => by dsimp [f]; positivity) hp
  have hs : Summable (fun n : ℕ => f (n : ℝ)) := by
    have hh := (digamma_im_hasSum (z := (a : ℂ) + (t : ℂ) * I) (by simpa using ha)).summable
    simpa [f] using hh
  rw [hs.tsum_eq_zero_add]
  simpa [f] using add_le_add_right htail (f 0)

theorem poisson_sum_le_uniform {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    ∑' n : ℕ, t / ((a + n) ^ 2 + t ^ 2) ≤ 1 / (2 * a) + Real.pi / 2 := by
  apply (poisson_sum_le ha ht).trans
  apply add_le_add_left
  apply (div_le_div_iff₀ (by positivity : 0 < a ^ 2 + t ^ 2) (by positivity : 0 < 2 * a)).mpr
  nlinarith [sq_nonneg (a - t)]

theorem digamma_im_abs_le {z : ℂ} (hz : 0 < z.re) :
    |(digamma z).im| ≤ 1 / (2 * z.re) + Real.pi / 2 := by
  have hs := digamma_im_hasSum hz
  rw [← hs.tsum_eq]
  have hh := norm_tsum_le_tsum_norm hs.summable.norm
  simp only [Real.norm_eq_abs] at hh
  apply hh.trans
  simp_rw [abs_div, abs_of_nonneg (by positivity : 0 ≤ (z.re + (_ : ℕ)) ^ 2 + z.im ^ 2)]
  simpa only [sq_abs] using poisson_sum_le_uniform hz (abs_nonneg z.im)

theorem digamma_im_abs_le_quarter {z : ℂ} (hz : 1 / 4 ≤ z.re) :
    |(digamma z).im| ≤ 2 + Real.pi / 2 := by
  apply (digamma_im_abs_le (by linarith : 0 < z.re)).trans
  have hi : 1 / (2 * z.re) ≤ 2 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  linarith

end LiuWang.Proof.DirichletZeroCount.Remainder
