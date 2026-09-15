import LiuWang.Proof.Campaign20260915.ZetaMordell.SourceSaddleCoefficients

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory
open scoped Real

namespace LiuWang.Proof.Campaign20260915.ZetaMordell
open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem sourceSaddle_time_scale {t : ℝ} (ht : 0 ≤ t) :
    rsSaddleScale * Real.sqrt (t / (2 * Real.pi)) = Real.sqrt t := by
  apply (sq_eq_sq₀ (mul_nonneg rsSaddleScale_pos.le (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg t)).mp
  rw [mul_pow, rsSaddleScale_sq, Real.sq_sqrt (by positivity), Real.sq_sqrt ht]
  field_simp

theorem sourcePhase_square (m : ℕ) : exp (-Real.pi * I * (m : ℂ) ^ 2) = (-1 : ℂ) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have he : exp (-Real.pi * I * ((m : ℂ) + 1) ^ 2) =
        exp (-Real.pi * I * (m : ℂ) ^ 2) / exp ((m : ℂ) * (2 * Real.pi * I)) *
          exp (-(Real.pi * I)) := by
      rw [← exp_sub, ← exp_add]
      congr 1
      ring
    push_cast
    rw [he, ih, exp_nat_mul_two_pi_mul_I, div_one, exp_neg, exp_pi_mul_I]
    simp [pow_succ]

theorem sourceGaussian_prefactor (sigma eta : ℝ) (m : ℕ) :
    rsLocalPrefactor sigma eta m * sourceGaussianPhase eta m =
      (-1 : ℂ) ^ m * exp (-Real.pi * I / 8) *
        (eta : ℂ) ^ (((sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) - 1) *
          exp (-Real.pi * I * (eta : ℂ) ^ 2) := by
  have he : exp (-2 * Real.pi * I * m * eta) * sourceGaussianPhase eta m =
      exp (-Real.pi * I * (m : ℂ) ^ 2) * exp (-Real.pi * I / 8) *
        exp (-Real.pi * I * (eta : ℂ) ^ 2) := by
    unfold sourceGaussianPhase
    simp only [← exp_add]
    congr 1
    push_cast
    ring
  unfold rsLocalPrefactor
  rw [mul_assoc, he, sourcePhase_square]
  ring

theorem correctionMoment_zero_phi {z : ℝ} (hz : |z| < 3 / 2) :
    correctionMoment 0 z = (rsPhi z : ℂ) := by
  simpa only [correctionMoment, pow_zero, one_mul, correctionIntegral] using
    correctionIntegral_eq_rsPhi hz

theorem correctionPolynomial_moment_sum (N : ℕ) (p : ℕ → ℂ) (z : ℂ) :
    (∫ t : ℝ, (∑ n ∈ Finset.range N, p n * (siegelLine t - (z + 1) / 2) ^ n) *
      correctionKernel z t) = ∑ n ∈ Finset.range N, p n * correctionMoment n z := by
  simp only [Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ (fun n _ => (correctionCenteredKernel_integrable n z).const_mul (p n))]
  simp only [integral_const_mul, correctionMoment]

theorem correctionMoment_one_three_phi {z : ℝ} (hz : |z| < 3 / 2) :
    correctionMoment 1 z / 2 - (2 / 3 : ℂ) * Real.pi * I * correctionMoment 3 z =
      (rsPhiOne z : ℂ) := by
  let p : ℕ → ℂ := fun n => if n = 1 then 1 / 2 else if n = 3 then -(2 / 3) * Real.pi * I else 0
  have hp (w : ℂ) : (∑ n ∈ Finset.range 4, p n * w ^ n) =
      w / 2 - (2 / 3 : ℂ) * Real.pi * I * w ^ 3 := by
    norm_num [p, Finset.sum_range_succ]
    ring
  have h := correctionPolynomial_moment_sum 4 p z
  simp_rw [hp] at h
  rw [correctionIntegral_phiOne hz] at h
  norm_num [p, Finset.sum_range_succ] at h
  linear_combination -h

theorem correctionMoment_two_four_six_phi {z : ℝ} (hz : |z| < 3 / 2) :
    -(2 / 9 : ℂ) * Real.pi ^ 2 * correctionMoment 6 z -
        (5 / 6 : ℂ) * Real.pi * I * correctionMoment 4 z +
        (3 / 8 : ℂ) * correctionMoment 2 z - I / (96 * Real.pi) * correctionMoment 0 z =
      (rsPhiTwo z : ℂ) := by
  let p : ℕ → ℂ := fun n =>
    if n = 0 then -I / (96 * Real.pi)
    else if n = 2 then 3 / 8
    else if n = 4 then -(5 / 6) * Real.pi * I
    else if n = 6 then -(2 / 9) * Real.pi ^ 2 else 0
  have hp (w : ℂ) : (∑ n ∈ Finset.range 7, p n * w ^ n) =
      -(2 / 9 : ℂ) * Real.pi ^ 2 * w ^ 6 - (5 / 6 : ℂ) * Real.pi * I * w ^ 4 +
        (3 / 8 : ℂ) * w ^ 2 - I / (96 * Real.pi) := by
    norm_num [p, Finset.sum_range_succ]
    ring
  have h := correctionPolynomial_moment_sum 7 p z
  simp_rw [hp] at h
  rw [correctionIntegral_phiTwo hz] at h
  norm_num [p, Finset.sum_range_succ] at h
  linear_combination -h

theorem sourceLocalPolynomial_one_phi (sigma : ℝ) {eta : ℝ} {m : ℕ}
    (h0 : 0 < eta - m) (h1 : eta - m < 1) :
    -(∫ y : ℝ, rsLocalPolynomialIntegrand sigma eta m 1 y) =
      sourceGaussianPhase eta m * (rsPhi (sourcePhiParameter eta m) : ℂ) := by
  rw [sourceLocalPolynomial_integral sigma h0 h1 1]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    sourceSaddle_scaled_zero, one_mul,
    correctionMoment_zero_phi (sourcePhiParameter_domain h0.le h1.le)]

theorem sourceLocalPolynomial_seven_phi {eta : ℝ} {m : ℕ}
    (h0 : 0 < eta - m) (h1 : eta - m < 1) :
    -(∫ y : ℝ, rsLocalPolynomialIntegrand (1 / 2) eta m 7 y) =
      sourceGaussianPhase eta m *
        ((rsPhi (sourcePhiParameter eta m) : ℂ) -
          (rsPhiOne (sourcePhiParameter eta m) : ℂ) / eta +
          ((rsPhiTwo (sourcePhiParameter eta m) : ℂ) +
            I / (96 * Real.pi) * (rsPhi (sourcePhiParameter eta m) : ℂ)) / (eta : ℂ) ^ 2 -
          5 / (16 * (eta : ℂ) ^ 3) * correctionMoment 3 (sourcePhiParameter eta m) +
          35 / (128 * (eta : ℂ) ^ 4) * correctionMoment 4 (sourcePhiParameter eta m) +
          (9 * Real.pi * I / (10 * (eta : ℂ) ^ 3) - 63 / (256 * (eta : ℂ) ^ 5)) *
            correctionMoment 5 (sourcePhiParameter eta m) +
          (-(223 * Real.pi * I) / (240 * (eta : ℂ) ^ 4) + 231 / (1024 * (eta : ℂ) ^ 6)) *
            correctionMoment 6 (sourcePhiParameter eta m)) := by
  have he : 0 < eta := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hz := sourcePhiParameter_domain h0.le h1.le
  rw [sourceLocalPolynomial_integral (1 / 2) h0 h1 7,
    ← correctionMoment_one_three_phi hz, ← correctionMoment_two_four_six_phi hz,
    ← correctionMoment_zero_phi hz]
  congr 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    sourceSaddle_scaled_zero, sourceSaddle_scaled_one he, sourceSaddle_scaled_two he,
    sourceSaddle_scaled_three he, sourceSaddle_scaled_four he,
    sourceSaddle_scaled_five he, sourceSaddle_scaled_six he]
  ring

theorem sourceLocalPolynomial_prefactored (sigma : ℝ) {eta : ℝ} {m : ℕ}
    (h0 : 0 < eta - m) (h1 : eta - m < 1) (N : ℕ) :
    rsLocalPrefactor sigma eta m * (-(∫ y : ℝ, rsLocalPolynomialIntegrand sigma eta m N y)) =
      ((-1 : ℂ) ^ m * exp (-Real.pi * I / 8) *
        (eta : ℂ) ^ (((sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) - 1) *
          exp (-Real.pi * I * (eta : ℂ) ^ 2)) *
        ∑ n ∈ Finset.range N, rsSaddleCoefficient sigma (rsSaddleScale * eta) n *
          (rsSaddleScale : ℂ) ^ n * correctionMoment n (sourcePhiParameter eta m) := by
  rw [sourceLocalPolynomial_integral sigma h0 h1 N, ← mul_assoc, sourceGaussian_prefactor]

end LiuWang.Proof.Campaign20260915.ZetaMordell
