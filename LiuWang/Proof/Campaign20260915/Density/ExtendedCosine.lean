import LiuWang.Proof.Campaign20260915.Density.FamilyWeightedCritical

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set Filter
open LiuWang.Proof.Interfaces (Character)
open LiuWang.Proof.NonprincipalDensityAdvance
open LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier
open LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis
open Complex.HadamardThreeLines

namespace LiuWang.Proof.Campaign20260915.Density

theorem cosine_argument_extended {y : ℝ} (hy : 2 ≤ y) {s : ℂ} (hs : |s.re| ≤ 2) :
    |(s / (2 * (y : ℂ))).re| ≤ 1 / 2 := by
  rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.div_ofReal_re,
    abs_div, abs_of_pos (by positivity : 0 < 2 * y)]
  apply (div_le_iff₀ (by positivity : 0 < 2 * y)).mpr
  linarith

theorem cosine_denominator_extended {y : ℝ} (hy : 2 ≤ y) {s : ℂ} (hs : |s.re| ≤ 2) :
    Complex.cos (s / (2 * (y : ℂ))) ≠ 0 :=
  norm_pos_iff.mp ((by positivity : (0 : ℝ) < (1 / 4) * Real.exp |(s / (2 * (y : ℂ))).im|).trans_le
    (cosine_lower (cosine_argument_extended hy hs)))

theorem cosine_decay_extended {q : ℕ} [NeZero q] (chi : Character q) (X : ℝ)
    {y : ℝ} (hy : 2 ≤ y) {s : ℂ} (hs : |s.re| ≤ 2) :
    ‖cosineDetector chi X y s‖ ≤
      4 * ‖NonprincipalDensityAdvance.f chi X s‖ * Real.exp (-|s.im| / (2 * y)) := by
  have hc := cosine_lower (cosine_argument_extended hy hs)
  have hi : |(s / (2 * (y : ℂ))).im| = |s.im| / (2 * y) := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.div_ofReal_im,
      abs_div, abs_of_pos (by positivity : 0 < 2 * y)]
  rw [hi] at hc
  have hinv := one_div_le_one_div_of_le (by positivity) hc
  have he : 1 / ((1 / 4 : ℝ) * Real.exp (|s.im| / (2 * y))) =
      4 * Real.exp (-|s.im| / (2 * y)) := by
    rw [neg_div, Real.exp_neg]
    field_simp
  rw [he] at hinv
  have h := mul_le_mul_of_nonneg_left hinv (norm_nonneg (NonprincipalDensityAdvance.f chi X s))
  unfold cosineDetector
  rw [norm_div]
  simpa only [div_eq_mul_inv, one_mul, mul_assoc, mul_comm, mul_left_comm] using h

theorem cosine_weight_extended {q : ℕ} [NeZero q] (chi : Character q) (X : ℝ)
    {y : ℝ} (hy : 2 ≤ y) {s : ℂ} (hs : |s.re| ≤ 2) :
    ‖cosineDetector chi X y s‖ ^ 2 ≤
      16 * ‖NonprincipalDensityAdvance.f chi X s‖ ^ 2 * Real.exp (-|s.im| / y) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (cosine_decay_extended chi X hy hs) 2
  rw [mul_pow, mul_pow, ← Real.exp_nat_mul] at h
  norm_num only [Nat.cast_ofNat] at h
  have he : 2 * (-|s.im| / (2 * y)) = -|s.im| / y := by ring
  simpa only [he, show (4 : ℝ) ^ 2 = 16 by norm_num] using h

theorem cosine_diffAt_extended {q : ℕ} [NeZero q] {chi : Character q}
    (hc : chi ≠ 1) (X : ℝ) {y : ℝ} (hy : 2 ≤ y) {s : ℂ} (hs : |s.re| ≤ 2) :
    DifferentiableAt ℂ (cosineDetector chi X y) s :=
  (differentiable_f hc X s).div ((differentiableAt_id.div_const _).ccos)
    (cosine_denominator_extended hy hs)

theorem cosine_analytic_extended {q : ℕ} [NeZero q] {chi : Character q}
    (hc : chi ≠ 1) (X : ℝ) {y : ℝ} (hy : 2 ≤ y) :
    AnalyticOnNhd ℂ (cosineDetector chi X y) (verticalStrip 0 2) := by
  apply (analyticOnNhd_iff_differentiableOn (isOpen_Ioo.preimage Complex.continuous_re)).mpr
  intro s hs
  exact (cosine_diffAt_extended hc X hy
    (abs_le.mpr ⟨by linarith [hs.1], hs.2.le⟩)).differentiableWithinAt

theorem cosine_vertical_continuous_extended {q : ℕ} [NeZero q] {chi : Character q}
    (hc : chi ≠ 1) (X : ℝ) {y sigma : ℝ} (hy : 2 ≤ y) (hs : |sigma| ≤ 2) :
    Continuous (fun t : ℝ => cosineDetector chi X y ((sigma : ℂ) + t * I)) := by
  have hv : Continuous (fun t : ℝ => (sigma : ℂ) + t * I) := by fun_prop
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (cosine_diffAt_extended hc X hy (by simpa using hs)).continuousAt.comp hv.continuousAt

theorem cosine_integrable_extended {q : ℕ} [NeZero q] {chi : Character q}
    (hc : chi ≠ 1) (X : ℝ) {y sigma : ℝ} (hy : 2 ≤ y) (hs : sigma ∈ Icc (1 / 2) 2) :
    Integrable (fun t : ℝ => ‖cosineDetector chi X y ((sigma : ℂ) + t * I)‖ ^ 2) := by
  have hsa : |sigma| ≤ 2 := abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
  have hi := (exponential_strip_integrable hc X (by linarith : 0 < y) hs.1).const_mul 16
  apply hi.mono' ((cosine_vertical_continuous_extended hc X hy hsa).norm.pow 2).aestronglyMeasurable
  filter_upwards with t
  simp only [Pi.pow_apply]
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have h := cosine_weight_extended chi X hy (s := (sigma : ℂ) + t * I) (by simpa using hsa)
  simpa only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re,
    mul_zero, add_zero, zero_add, mul_assoc] using h

theorem cosine_bounded_extended {q : ℕ} [NeZero q] {chi : Character q}
    (hc : chi ≠ 1) (X : ℝ) {y b : ℝ} (hy : 2 ≤ y) (hb : b ≤ 2) :
    BddAbove ((norm ∘ cosineDetector chi X y) '' verticalClosedStrip (1 / 2) b) := by
  have hp := prefixBudget_nonneg q
  have ha : 0 ≤ growthConstant q X := by unfold growthConstant; positivity
  have hbs : 0 ≤ growthSlope q X := by unfold growthSlope; positivity
  refine ⟨4 * (growthConstant q X + 2 * y * growthSlope q X), ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  change 1 / 2 ≤ s.re ∧ s.re ≤ b at hs
  have hd := cosine_decay_extended chi X hy (abs_le.mpr ⟨by linarith [hs.1], hs.2.trans hb⟩)
  have hf := mul_le_mul_of_nonneg_right (f_strip_growth hc X hs.1)
    (Real.exp_pos (-|s.im| / (2 * y))).le
  have he : Real.exp (-|s.im| / (2 * y)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (abs_nonneg _)) (by positivity))
  have ht := (Real.mul_exp_neg_le_exp_neg_one (|s.im| / (2 * y))).trans
    (Real.exp_le_one_iff.mpr (by norm_num : (-1 : ℝ) ≤ 0))
  have ht' := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 2 * y)
  have ht_eq : 2 * y * (|s.im| / (2 * y) * Real.exp (-(|s.im| / (2 * y)))) =
      |s.im| * Real.exp (-|s.im| / (2 * y)) := by rw [neg_div]; field_simp
  rw [ht_eq] at ht'
  have h1 := mul_le_mul_of_nonneg_left he ha
  have h2 := mul_le_mul_of_nonneg_left ht' hbs
  change ‖cosineDetector chi X y s‖ ≤ _
  nlinarith only [hd, hf, h1, h2]

end LiuWang.Proof.Campaign20260915.Density
