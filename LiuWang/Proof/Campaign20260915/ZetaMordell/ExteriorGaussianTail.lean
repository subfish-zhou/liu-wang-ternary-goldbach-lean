import LiuWang.Proof.Campaign20260915.ZetaMordell.ExteriorKernel
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Filter Set
open scoped Real Topology

namespace LiuWang.Proof.Campaign20260915.ZetaMordell
open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem exterior_gaussian_Ioi {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    (∫ y : ℝ in Ioi d, Real.exp (-c * y ^ 2)) ≤ Real.exp (-c * d ^ 2) / (2 * c * d) := by
  have ht := intervalIntegral_tendsto_integral_Ioi d
    (integrable_exp_neg_mul_sq hc).integrableOn (tendsto_id : Tendsto (fun A : ℝ => A) atTop atTop)
  exact le_of_tendsto ht (by
    filter_upwards [eventually_ge_atTop d] with A hA
    exact rsGaussian_tail_interval hc hd hA)

theorem exterior_gaussian_complement {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    (∫ y : ℝ in (Ioc (-d) d)ᶜ, Real.exp (-c * y ^ 2)) ≤
      Real.exp (-c * d ^ 2) / (c * d) := by
  have hu : (Ioc (-d) d)ᶜ = Iic (-d) ∪ Ioi d := by ext y; simp only [mem_compl_iff,
    mem_Ioc, not_and_or, not_lt, not_le, mem_union, mem_Iic, mem_Ioi]
  have hdis : Disjoint (Iic (-d)) (Ioi d) := by
    apply Set.disjoint_left.mpr
    intro y hy hz
    have hy' : y ≤ -d := hy
    have hz' : d < y := hz
    linarith
  rw [hu, setIntegral_union hdis measurableSet_Ioi
    (integrable_exp_neg_mul_sq hc).integrableOn (integrable_exp_neg_mul_sq hc).integrableOn]
  have he : (∫ y : ℝ in Iic (-d), Real.exp (-c * y ^ 2)) =
      ∫ y : ℝ in Ioi d, Real.exp (-c * y ^ 2) := by
    have h := integral_comp_neg_Iic (-d) (fun y : ℝ => Real.exp (-c * y ^ 2))
    simpa only [neg_neg, neg_sq] using h
  rw [he]
  have h := exterior_gaussian_Ioi hc hd
  have heq : Real.exp (-c * d ^ 2) / (c * d) = 2 * (Real.exp (-c * d ^ 2) / (2 * c * d)) := by ring
  rw [heq]
  linarith

theorem exterior_mem_abs {d y : ℝ} (hy : y ∈ (Ioc (-d) d)ᶜ) : d ≤ |y| := by
  simp only [mem_compl_iff, mem_Ioc, not_and_or, not_lt, not_le] at hy
  rcases hy with hy | hy
  · exact le_abs.mpr (Or.inr (by linarith))
  · exact le_abs.mpr (Or.inl hy.le)

theorem exterior_integrable_of_gaussian {f : ℝ → ℂ} {B c d : ℝ}
    (hf : Measurable f) (hc : 0 < c)
    (hb : ∀ y : ℝ, d ≤ |y| → ‖f y‖ ≤ B * Real.exp (-c * y ^ 2)) :
    IntegrableOn f (Ioc (-d) d)ᶜ := by
  apply (((integrable_exp_neg_mul_sq hc).const_mul B).integrableOn).mono'
    hf.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.compl)] with y hy
  exact hb y (exterior_mem_abs hy)

theorem exterior_norm_integral_bound {f : ℝ → ℂ} {B c d : ℝ}
    (hf : Measurable f) (hB : 0 ≤ B) (hc : 0 < c) (hd : 0 < d)
    (hb : ∀ y : ℝ, d ≤ |y| → ‖f y‖ ≤ B * Real.exp (-c * y ^ 2)) :
    (∫ y : ℝ in (Ioc (-d) d)ᶜ, ‖f y‖) ≤ B * Real.exp (-c * d ^ 2) / (c * d) := by
  have hi := exterior_integrable_of_gaussian hf hc hb
  calc
    _ ≤ ∫ y : ℝ in (Ioc (-d) d)ᶜ, B * Real.exp (-c * y ^ 2) := by
      apply integral_mono_ae hi.norm (((integrable_exp_neg_mul_sq hc).const_mul B).integrableOn)
      filter_upwards [ae_restrict_mem (measurableSet_Ioc.compl)] with y hy
      exact hb y (exterior_mem_abs hy)
    _ = B * ∫ y : ℝ in (Ioc (-d) d)ᶜ, Real.exp (-c * y ^ 2) := integral_const_mul _ _
    _ ≤ B * (Real.exp (-c * d ^ 2) / (c * d)) :=
      mul_le_mul_of_nonneg_left (exterior_gaussian_complement hc hd) hB
    _ = _ := by ring

theorem exterior_integral_bound {f : ℝ → ℂ} {B c d : ℝ}
    (hf : Measurable f) (hB : 0 ≤ B) (hc : 0 < c) (hd : 0 < d)
    (hb : ∀ y : ℝ, d ≤ |y| → ‖f y‖ ≤ B * Real.exp (-c * y ^ 2)) :
    ‖∫ y : ℝ in (Ioc (-d) d)ᶜ, f y‖ ≤ B * Real.exp (-c * d ^ 2) / (c * d) :=
  (norm_integral_le_integral_norm _).trans (exterior_norm_integral_bound hf hB hc hd hb)

theorem exterior_polynomial_integrable (sigma : ℝ) {eta : ℝ} (he : 1 ≤ eta)
    {m : ℕ} (h0 : 0 ≤ eta - m) (h1 : eta - m ≤ 1) (N : ℕ) :
    IntegrableOn (rsLocalPolynomialIntegrand sigma eta m N) (Ioc (-eta / 2) (eta / 2))ᶜ := by
  have hb y (hy : eta / 2 ≤ |y|) := exterior_polynomial_bound sigma eta m N
    (by linarith : 1 / 2 ≤ |y|) h0 h1
  simpa only [neg_div] using exterior_integrable_of_gaussian
    (exterior_polynomial_measurable sigma eta m N)
    (by positivity : 0 < Real.pi / 2) (by simpa only [neg_div] using hb)

theorem exterior_polynomial_general_budget (sigma : ℝ) {eta : ℝ} (he : 1 ≤ eta)
    {m : ℕ} (h0 : 0 ≤ eta - m) (h1 : eta - m ≤ 1) (N : ℕ) :
    (∫ y : ℝ in (Ioc (-eta / 2) (eta / 2))ᶜ, ‖rsLocalPolynomialIntegrand sigma eta m N y‖) ≤
      (24 * ∑ n ∈ Finset.range N,
        ‖rsSaddleCoefficient sigma (rsSaddleScale * eta) n * (rsSaddleScale : ℂ) ^ n‖ *
          (n.factorial : ℝ)) / (Real.pi * eta) * Real.exp (-Real.pi * eta ^ 2 / 8) := by
  have hb y (hy : eta / 2 ≤ |y|) := exterior_polynomial_bound sigma eta m N
    (by linarith : 1 / 2 ≤ |y|) h0 h1
  have h := exterior_norm_integral_bound (exterior_polynomial_measurable sigma eta m N)
    (by positivity : 0 ≤ 6 * ∑ n ∈ Finset.range N,
      ‖rsSaddleCoefficient sigma (rsSaddleScale * eta) n * (rsSaddleScale : ℂ) ^ n‖ *
        (n.factorial : ℝ))
    (by positivity : 0 < Real.pi / 2) (by linarith : 0 < eta / 2)
    (by simpa only [neg_div] using hb)
  rw [show -(Real.pi / 2) * (eta / 2) ^ 2 = -Real.pi * eta ^ 2 / 8 by ring] at h
  convert h using 1
  · rw [neg_div]
  · ring

end LiuWang.Proof.Campaign20260915.ZetaMordell
