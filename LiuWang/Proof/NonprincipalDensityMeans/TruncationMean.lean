import LiuWang.Proof.NonprincipalDensityMeans.DetectorMean

/-!
# Summable critical truncation errors for the actual L and detector families

The explicit remainder, not a limit of the growing finite mother bound,
justifies the passage from finite truncations to the actual analytic functions.
The full fixed-modulus normalization is retained.
-/

set_option autoImplicit false
noncomputable section

open Finset MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.NonprincipalDensityAdvance

namespace LiuWang.Proof.NonprincipalDensityMeans

def finiteDetector {q : ℕ} (chi : Character q) (X : ℝ) (M : ℕ) (s : ℂ) : ℂ :=
  partialL chi M s * NonprincipalDensityAdvance.Q chi X s - 1

def LremainderMean (q : ℕ) [NeZero q] (M : ℕ) (y : ℝ) : ℝ :=
  (∑ chi ∈ nonprincipalCharacters q, ∫ t in -y..y,
    ‖chi.LFunction ((1 / 2 : ℂ) + t * Complex.I) -
      partialL chi M ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) / q.totient

def FremainderMean (q : ℕ) [NeZero q] (X : ℝ) (M : ℕ) (y : ℝ) : ℝ :=
  (∑ chi ∈ nonprincipalCharacters q, ∫ t in -y..y,
    ‖NonprincipalDensityAdvance.f chi X ((1 / 2 : ℂ) + t * Complex.I) -
      finiteDetector chi X M ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) / q.totient

theorem f_sub_finiteDetector {q : ℕ} [NeZero q] (chi : Character q) (X : ℝ) (M : ℕ) (s : ℂ) :
    NonprincipalDensityAdvance.f chi X s - finiteDetector chi X M s =
      (chi.LFunction s - partialL chi M s) * NonprincipalDensityAdvance.Q chi X s := by
  unfold NonprincipalDensityAdvance.f finiteDetector
  ring

theorem partialL_critical_continuous {q : ℕ} (chi : Character q) (M : ℕ) :
    Continuous (fun t : ℝ => partialL chi M ((1 / 2 : ℂ) + t * Complex.I)) := by
  have he (t : ℝ) : partialL chi M ((1 / 2 : ℂ) + t * Complex.I) =
      polynomial chi ((range M).erase 0) (verticalCoefficient (fun _ => 1) (1 / 2))
        (fun n => -Real.log n) t := by
    simpa only [partialL, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
      dirichletPolynomial_eq_wave chi ((range M).erase 0)
        (fun _ hn => Nat.pos_of_ne_zero (mem_erase.mp hn).1) (fun _ => 1) (1 / 2) t
  simp_rw [he]
  exact continuous_polynomial _ _ _ _

theorem Lremainder_critical_continuous {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (M : ℕ) :
    Continuous (fun t : ℝ => chi.LFunction ((1 / 2 : ℂ) + t * Complex.I) -
      partialL chi M ((1 / 2 : ℂ) + t * Complex.I)) :=
  ((DirichletCharacter.differentiable_LFunction hchi).continuous.comp
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))).sub
      (partialL_critical_continuous chi M)

theorem LremainderMean_nonneg (q : ℕ) [NeZero q] (M : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ LremainderMean q M y := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact sum_nonneg fun _ _ =>
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)

theorem FremainderMean_nonneg (q : ℕ) [NeZero q] (X : ℝ) (M : ℕ)
    {y : ℝ} (hy : 0 ≤ y) : 0 ≤ FremainderMean q X M y := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact sum_nonneg fun _ _ =>
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)

theorem LremainderMean_le (q : ℕ) [NeZero q] {M : ℕ} (hM : 1 ≤ M)
    {y : ℝ} (hy : 0 ≤ y) :
    LremainderMean q M y ≤
      (8 * y * (q : ℝ) ^ 2 * (1 + y) ^ 2 * nonprincipalRatio q) / M := by
  have hi (chi : Character q) (hchi : chi ≠ 1) :
      (∫ t in -y..y, ‖chi.LFunction ((1 / 2 : ℂ) + t * Complex.I) -
        partialL chi M ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) ≤
          2 * y * truncationError q M y ^ 2 := by
    have h := intervalIntegral.integral_mono_on (μ := volume) (by linarith : -y ≤ y)
      (((Lremainder_critical_continuous hchi M).norm.pow 2).intervalIntegrable _ _)
      intervalIntegrable_const
      (fun _ ht => pow_le_pow_left₀ (norm_nonneg _)
        (LFunction_truncation_critical hchi hM (abs_le.mpr ht)) 2)
    rw [intervalIntegral.integral_const] at h
    simpa only [Pi.pow_apply, smul_eq_mul, sub_neg_eq_add, ← two_mul] using h
  have h := sum_le_sum (s := nonprincipalCharacters q)
    (fun chi hchi => hi chi ((mem_nonprincipalCharacters chi).mp hchi))
  rw [sum_const, nsmul_eq_mul, card_nonprincipalCharacters] at h
  apply (div_le_div_of_nonneg_right h (Nat.cast_nonneg q.totient)).trans_eq
  unfold truncationError nonprincipalRatio
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg M)]
  ring

theorem FremainderMean_le_LremainderMean (q : ℕ) [NeZero q] (X : ℝ) (M : ℕ)
    {y : ℝ} (hy : 0 ≤ y) :
    FremainderMean q X M y ≤ 4 * (⌈X⌉₊ : ℝ) * LremainderMean q M y := by
  have hi (chi : Character q) (hchi : chi ≠ 1) :
      (∫ t in -y..y, ‖NonprincipalDensityAdvance.f chi X ((1 / 2 : ℂ) + t * Complex.I) -
        finiteDetector chi X M ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) ≤
          4 * (⌈X⌉₊ : ℝ) * (∫ t in -y..y,
            ‖chi.LFunction ((1 / 2 : ℂ) + t * Complex.I) -
              partialL chi M ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) := by
    have hQ : Continuous (fun t : ℝ =>
        NonprincipalDensityAdvance.Q chi X ((1 / 2 : ℂ) + t * Complex.I)) := by
      simp_rw [Q_critical_eq_wave]
      exact continuous_polynomial _ _ _ _
    have hR := Lremainder_critical_continuous hchi M
    simp_rw [f_sub_finiteDetector]
    have h := intervalIntegral.integral_mono_on (μ := volume) (by linarith : -y ≤ y)
      (((hR.mul hQ).norm.pow 2).intervalIntegrable _ _)
      ((((hR.norm.pow 2).intervalIntegrable (-y) y)).const_mul (4 * (⌈X⌉₊ : ℝ)))
      (fun t _ => by
        simp only [Pi.pow_apply, Pi.mul_apply]
        rw [norm_mul, mul_pow, mul_comm]
        exact mul_le_mul_of_nonneg_right (Q_critical_norm_sq_le chi X t) (sq_nonneg _))
    simp only [Pi.pow_apply, Pi.mul_apply] at h
    rwa [intervalIntegral.integral_const_mul] at h
  have h := sum_le_sum (s := nonprincipalCharacters q)
    (fun chi hchi => hi chi ((mem_nonprincipalCharacters chi).mp hchi))
  rw [← mul_sum] at h
  exact (div_le_div_of_nonneg_right h (Nat.cast_nonneg q.totient)).trans_eq (by
    unfold LremainderMean
    ring)

theorem FremainderMean_le (q : ℕ) [NeZero q] (X : ℝ) {M : ℕ} (hM : 1 ≤ M)
    {y : ℝ} (hy : 0 ≤ y) :
    FremainderMean q X M y ≤
      (32 * (⌈X⌉₊ : ℝ) * y * (q : ℝ) ^ 2 * (1 + y) ^ 2 * nonprincipalRatio q) / M := by
  exact (FremainderMean_le_LremainderMean q X M hy).trans
    ((mul_le_mul_of_nonneg_left (LremainderMean_le q hM hy)
      (by positivity : 0 ≤ 4 * (⌈X⌉₊ : ℝ))).trans_eq (by ring))

theorem dyadic_summable_of_reciprocal_bound (a : ℕ → ℝ) (C : ℝ)
    (ha : ∀ M, 0 ≤ a M) (hb : ∀ M, 1 ≤ M → a M ≤ C / M) :
    Summable (fun k : ℕ => a (2 ^ k)) ∧ (∑' k : ℕ, a (2 ^ k)) ≤ 2 * C := by
  have hgeo : Summable (fun k : ℕ => C * (1 / 2 : ℝ) ^ k) :=
    summable_geometric_two.mul_left C
  have hpoint (k : ℕ) : a (2 ^ k) ≤ C * (1 / 2 : ℝ) ^ k := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv, one_mul, inv_pow] using
      hb (2 ^ k) (Nat.one_le_pow k 2 (by norm_num))
  have hsum := Summable.of_nonneg_of_le (fun k => ha (2 ^ k)) hpoint hgeo
  refine ⟨hsum, (hsum.tsum_le_tsum hpoint hgeo).trans_eq ?_⟩
  rw [tsum_mul_left, tsum_geometric_two, mul_comm]

theorem LremainderMean_dyadic_summable (q : ℕ) [NeZero q] {y : ℝ} (hy : 0 ≤ y) :
    Summable (fun k : ℕ => LremainderMean q (2 ^ k) y) ∧
      (∑' k : ℕ, LremainderMean q (2 ^ k) y) ≤
        16 * y * (q : ℝ) ^ 2 * (1 + y) ^ 2 * nonprincipalRatio q := by
  have h := dyadic_summable_of_reciprocal_bound (fun M => LremainderMean q M y)
    (8 * y * (q : ℝ) ^ 2 * (1 + y) ^ 2 * nonprincipalRatio q)
    (fun M => LremainderMean_nonneg q M hy) (fun _ hM => LremainderMean_le q hM hy)
  exact ⟨h.1, h.2.trans_eq (by ring)⟩

theorem FremainderMean_dyadic_summable (q : ℕ) [NeZero q] (X : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    Summable (fun k : ℕ => FremainderMean q X (2 ^ k) y) ∧
      (∑' k : ℕ, FremainderMean q X (2 ^ k) y) ≤
        64 * (⌈X⌉₊ : ℝ) * y * (q : ℝ) ^ 2 * (1 + y) ^ 2 * nonprincipalRatio q := by
  have h := dyadic_summable_of_reciprocal_bound (fun M => FremainderMean q X M y)
    (32 * (⌈X⌉₊ : ℝ) * y * (q : ℝ) ^ 2 * (1 + y) ^ 2 * nonprincipalRatio q)
    (fun M => FremainderMean_nonneg q X M hy) (fun _ hM => FremainderMean_le q X hM hy)
  exact ⟨h.1, h.2.trans_eq (by ring)⟩

@[simp] theorem LremainderMean_one (M : ℕ) (y : ℝ) :
    LremainderMean 1 M y = 0 := by simp [LremainderMean]

@[simp] theorem LremainderMean_two (M : ℕ) (y : ℝ) :
    LremainderMean 2 M y = 0 := by simp [LremainderMean]

@[simp] theorem FremainderMean_one (X : ℝ) (M : ℕ) (y : ℝ) :
    FremainderMean 1 X M y = 0 := by simp [FremainderMean]

@[simp] theorem FremainderMean_two (X : ℝ) (M : ℕ) (y : ℝ) :
    FremainderMean 2 X M y = 0 := by simp [FremainderMean]

end LiuWang.Proof.NonprincipalDensityMeans
