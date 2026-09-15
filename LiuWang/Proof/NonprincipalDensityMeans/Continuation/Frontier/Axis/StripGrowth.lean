import LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.CosineWeight
import LiuWang.Proof.GlobalZeroDensity.Strip.FullAxis

/-! Paid strip growth and whole-axis integrability for every nonprincipal cosine detector. -/

set_option autoImplicit false
noncomputable section

open Finset MeasureTheory Set Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.NonprincipalDensityAdvance
open Complex.HadamardThreeLines

namespace LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis

def growthConstant (q : ℕ) (X : ℝ) : ℝ := (⌈X⌉₊ : ℝ) * (1 + 2 * prefixBudget q) + 1
def growthSlope (q : ℕ) (X : ℝ) : ℝ := 2 * (⌈X⌉₊ : ℝ) * prefixBudget q

theorem Q_norm_strip {q : ℕ} (chi : Character q) (X : ℝ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖NonprincipalDensityAdvance.Q chi X s‖ ≤ (⌈X⌉₊ : ℝ) := by
  unfold NonprincipalDensityAdvance.Q
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _n ∈ range ⌈X⌉₊, (1 : ℝ) := by
      apply sum_le_sum
      intro n _
      by_cases hn : n = 0
      · subst n
        simp [twistedMu]
      have hmu : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
        rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> simp [h]
      have htw : ‖twistedMu chi n‖ ≤ 1 := by
        rw [twistedMu, norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (chi.norm_le_one _)).trans hmu
      rw [norm_div, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      have hp := Real.one_le_rpow (Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn)) hs
      exact (div_le_one (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hp)).mpr (htw.trans hp)
    _ = _ := by simp

theorem partialL_two {q : ℕ} (chi : Character q) (s : ℂ) : partialL chi 2 s = 1 := by
  simp [partialL, dirichletPolynomial, Finset.sum_range_succ]

theorem f_strip_growth {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (X : ℝ) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖NonprincipalDensityAdvance.f chi X s‖ ≤ growthConstant q X + growthSlope q X * |s.im| := by
  have hp := prefixBudget_nonneg q
  have he : (s.re : ℂ) + s.im * Complex.I = s := Complex.re_add_im s
  have hL := LFunction_truncation_PV hchi (by norm_num : 1 ≤ 2) hs (le_refl |s.im|)
  rw [he, partialL_two] at hL
  have hpow : (2 : ℝ) ^ (-s.re) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have herr := mul_le_mul_of_nonneg_left hpow
    (by positivity : 0 ≤ 2 * prefixBudget q * (1 + |s.im|))
  have hb : ‖chi.LFunction s‖ ≤ 1 + 2 * prefixBudget q * (1 + |s.im|) := by
    have hn := norm_add_le (chi.LFunction s - 1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at hn
    unfold pvError at hL
    norm_num only [Nat.cast_ofNat] at hL
    nlinarith only [hn, hL, herr]
  have hq := Q_norm_strip chi X (by linarith : 0 ≤ s.re)
  have hf := norm_sub_le (chi.LFunction s * NonprincipalDensityAdvance.Q chi X s) 1
  rw [norm_mul, norm_one] at hf
  have hm := mul_le_mul hb hq (norm_nonneg _) (by positivity)
  unfold NonprincipalDensityAdvance.f growthConstant growthSlope
  nlinarith only [hf, hm]

theorem exponential_strip_integrable {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (X : ℝ) {y sigma : ℝ} (hy : 0 < y) (hs : 1 / 2 ≤ sigma) :
    Integrable (fun t : ℝ =>
      ‖NonprincipalDensityAdvance.f chi X ((sigma : ℂ) + t * Complex.I)‖ ^ 2 *
        Real.exp (-|t| / y)) := by
  have hm := GlobalZeroDensity.Strip.polynomial_exponential_abs_integrable hy
    (growthConstant q X) (growthSlope q X)
  have hv : Continuous (fun t : ℝ => (sigma : ℂ) + t * Complex.I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hc := (((differentiable_f hchi X).continuous.comp hv).norm.pow 2).mul
    (Real.continuous_exp.comp (continuous_id.abs.neg.div_const y))
  apply hm.mono' hc.aestronglyMeasurable
  filter_upwards with t
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Function.comp_apply, id_eq]
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  apply pow_le_pow_left₀ (norm_nonneg _)
  simpa using f_strip_growth hchi X (s := (sigma : ℂ) + t * Complex.I) (by simpa using hs)

theorem cosine_strip_integrable {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (X : ℝ) {y sigma : ℝ} (hy : 2 ≤ y)
    (hs : sigma ∈ Set.Icc (1 / 2) 1) :
    Integrable (fun t : ℝ => ‖cosineDetector chi X y ((sigma : ℂ) + t * Complex.I)‖ ^ 2) :=
  cosine_integrable_of_exponential hchi X hy (abs_le.mpr ⟨by linarith [hs.1], hs.2⟩)
    (exponential_strip_integrable hchi X (by linarith) hs.1)

theorem cosine_strip_bounded {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (X : ℝ) {y : ℝ} (hy : 2 ≤ y) :
    BddAbove ((norm ∘ cosineDetector chi X y) '' verticalClosedStrip (1 / 2) 1) := by
  have hp := prefixBudget_nonneg q
  have ha : 0 ≤ growthConstant q X := by unfold growthConstant; positivity
  have hb : 0 ≤ growthSlope q X := by unfold growthSlope; positivity
  refine ⟨4 * (growthConstant q X + 2 * y * growthSlope q X), ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  change 1 / 2 ≤ s.re ∧ s.re ≤ 1 at hs
  have hd := cosineDetector_decay chi X hy (abs_le.mpr ⟨by linarith [hs.1], hs.2⟩)
  have hf := mul_le_mul_of_nonneg_right (f_strip_growth hchi X hs.1)
    (Real.exp_pos (-|s.im| / (2 * y))).le
  have hex : Real.exp (-|s.im| / (2 * y)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (abs_nonneg _)) (by positivity))
  have ht := (Real.mul_exp_neg_le_exp_neg_one (|s.im| / (2 * y))).trans
    (Real.exp_le_one_iff.mpr (by norm_num : (-1 : ℝ) ≤ 0))
  have ht' := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 2 * y)
  have he : 2 * y * (|s.im| / (2 * y) * Real.exp (-(|s.im| / (2 * y)))) =
      |s.im| * Real.exp (-|s.im| / (2 * y)) := by rw [neg_div]; field_simp
  rw [he] at ht'
  have h1 := mul_le_mul_of_nonneg_left hex ha
  have h2 := mul_le_mul_of_nonneg_left ht' hb
  change ‖cosineDetector chi X y s‖ ≤ _
  nlinarith only [hd, hf, h1, h2]

end LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis
