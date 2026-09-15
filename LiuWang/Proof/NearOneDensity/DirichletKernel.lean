import LiuWang.Proof.NearOneDensity.Series
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLFoundation

set_option autoImplicit false
noncomputable section

open scoped BigOperators ComplexConjugate
open Classical

namespace LiuWang.Proof.NearOneDensity

def mangoldtWeight (σ : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ

def phase {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else χ n / (n : ℂ) ^ ((t : ℂ) * Complex.I)

def dampedWeight (σ τ c : ℝ) (n : ℕ) : ℝ :=
  mangoldtWeight σ n - c * mangoldtWeight τ n

def logKernel {q : ℕ} [NeZero q] (σ τ c : ℝ) (χ : DirichletCharacter ℂ q) (t : ℝ) : ℝ :=
  (-deriv χ.LFunction (σ + (t : ℂ) * Complex.I) /
      χ.LFunction (σ + (t : ℂ) * Complex.I)).re -
    c * (-deriv χ.LFunction (τ + (t : ℂ) * Complex.I) /
      χ.LFunction (τ + (t : ℂ) * Complex.I)).re

theorem mangoldtWeight_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ mangoldtWeight σ n := by
  unfold mangoldtWeight
  split_ifs
  · exact le_rfl
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (by positivity) _)

theorem mangoldtWeight_antitone {σ τ : ℝ} (hστ : σ ≤ τ) (n : ℕ) :
    mangoldtWeight τ n ≤ mangoldtWeight σ n := by
  by_cases hn : n = 0
  · simp [mangoldtWeight, hn]
  · simp only [mangoldtWeight, if_neg hn]
    apply div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) _)
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn) hστ

theorem dampedWeight_nonneg {σ τ c : ℝ} (hστ : σ ≤ τ) (hc : c ≤ 1) (n : ℕ) :
    0 ≤ dampedWeight σ τ c n := by
  have h := mul_le_mul_of_nonneg_right hc (mangoldtWeight_nonneg τ n)
  have hh := mangoldtWeight_antitone hστ n
  unfold dampedWeight
  linarith

theorem ofReal_mangoldtWeight (σ : ℝ) (n : ℕ) :
    (mangoldtWeight σ n : ℂ) =
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) σ n := by
  by_cases hn : n = 0
  · simp [mangoldtWeight, hn]
  · simp only [mangoldtWeight, if_neg hn, LSeries.term_of_ne_zero hn, Complex.ofReal_div]
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]

theorem summable_mangoldtWeight {σ : ℝ} (hσ : 1 < σ) : Summable (mangoldtWeight σ) := by
  have h := Complex.hasSum_re
    (ArithmeticFunction.LSeriesSummable_vonMangoldt
      (show 1 < (σ : ℂ).re by simpa using hσ)).hasSum
  simpa only [← ofReal_mangoldtWeight, Complex.ofReal_re] using h.summable

theorem summable_dampedWeight {σ τ c : ℝ} (hσ : 1 < σ) (hτ : 1 < τ) :
    Summable (dampedWeight σ τ c) :=
  (summable_mangoldtWeight hσ).sub ((summable_mangoldtWeight hτ).mul_left c)

theorem norm_phase_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (n : ℕ) :
    ‖phase χ t n‖ ≤ 1 := by
  by_cases hn : n = 0
  · simp [phase, hn]
  · simp only [phase, if_neg hn, norm_div,
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), Complex.mul_re,
      Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
      zero_mul, sub_self, Real.rpow_zero, div_one]
    exact χ.norm_le_one _

theorem twist_term_eq_weight_phase {q : ℕ} (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) (n : ℕ) :
    LSeries.term (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ))
        (σ + (t : ℂ) * Complex.I) n =
      (mangoldtWeight σ n : ℂ) * phase χ t n := by
  by_cases hn : n = 0
  · simp [phase, mangoldtWeight, hn]
  · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [ofReal_mangoldtWeight, LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
      Complex.cpow_add _ _ hnC]
    simp only [phase, if_neg hn]
    ring

theorem summable_weight_phase_re {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ)
    {σ τ c : ℝ} (hσ : 1 < σ) (hτ : 1 < τ) :
    Summable (fun n => dampedWeight σ τ c n * (phase χ t n).re) := by
  have hs (a : ℝ) (ha : 1 < a) :
      Summable (fun n => mangoldtWeight a n * (phase χ t n).re) := by
    have h := Complex.hasSum_re
      (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ
        (show 1 < (a + (t : ℂ) * Complex.I).re by simpa using ha)).hasSum
    simpa only [Pi.mul_def, twist_term_eq_weight_phase, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using h.summable
  simpa only [dampedWeight, sub_mul, mul_assoc] using
    (hs σ hσ).sub ((hs τ hτ).mul_left c)

theorem logKernel_eq_series {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ)
    {σ τ c : ℝ} (hσ : 1 < σ) (hτ : 1 < τ) :
    logKernel σ τ c χ t = ∑' n, dampedWeight σ τ c n * (phase χ t n).re := by
  have heq (a : ℝ) (ha : 1 < a) :
      (-deriv χ.LFunction (a + (t : ℂ) * Complex.I) /
          χ.LFunction (a + (t : ℂ) * Complex.I)).re =
        ∑' n, mangoldtWeight a n * (phase χ t n).re := by
    rw [← DirichletCharacter.LSeries_twist_vonMangoldt_eq_neg_logDeriv_LFunction χ
      (show 1 < (a + (t : ℂ) * Complex.I).re by simpa using ha)]
    rw [LSeries, Complex.re_tsum (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ
      (show 1 < (a + (t : ℂ) * Complex.I).re by simpa using ha))]
    apply tsum_congr
    intro n
    simp only [Pi.mul_def, twist_term_eq_weight_phase, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  have hs (a : ℝ) (ha : 1 < a) :
      Summable (fun n => mangoldtWeight a n * (phase χ t n).re) := by
    simpa only [dampedWeight, zero_mul, sub_zero] using
      (summable_weight_phase_re χ t (c := 0) ha ha)
  simp only [logKernel, heq σ hσ, heq τ hτ, dampedWeight, sub_mul, mul_assoc]
  rw [(hs σ hσ).tsum_sub ((hs τ hτ).mul_left c), tsum_mul_left]

theorem summable_weight_correlation {ι : Type*} {q : ℕ}
    (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    {σ τ c : ℝ} (hσ : 1 < σ) (hτ : 1 < τ) (hστ : σ ≤ τ) (hc : c ≤ 1)
    (i j : ι) :
    Summable (fun n => dampedWeight σ τ c n *
      (phase (χ i) (t i) n * conj (phase (χ j) (t j) n)).re) := by
  apply (summable_dampedWeight (c := c) hσ hτ).of_norm_bounded
  intro n
  have hnorm : ‖phase (χ i) (t i) n * conj (phase (χ j) (t j) n)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_one₀ (norm_phase_le_one _ _ _) (norm_nonneg _) (norm_phase_le_one _ _ _)
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (dampedWeight_nonneg hστ hc n)]
  exact mul_le_of_le_one_right (dampedWeight_nonneg hστ hc n)
    ((Complex.abs_re_le_norm _).trans hnorm)

theorem dirichlet_quadratic {ι : Type*} {q : ℕ} [NeZero q] (s : Finset ι)
    (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    {σ τ c : ℝ} (hσ : 1 < σ) (hτ : 1 < τ) (hστ : σ ≤ τ) (hc : c ≤ 1) :
    (∑ i ∈ s, logKernel σ τ c (χ i) (t i)) ^ 2 ≤
      (∑' n, dampedWeight σ τ c n) *
        ∑ i ∈ s, ∑ j ∈ s, ∑' n, dampedWeight σ τ c n *
          (phase (χ i) (t i) n * conj (phase (χ j) (t j) n)).re := by
  simp only [logKernel_eq_series _ _ hσ hτ]
  exact series_quadratic s _ _ (dampedWeight_nonneg hστ hc)
    (summable_dampedWeight hσ hτ) (fun i _ => summable_weight_phase_re (χ i) (t i) hσ hτ)
    (fun i _ j _ => summable_weight_correlation χ t hσ hτ hστ hc i j)

end LiuWang.Proof.NearOneDensity
