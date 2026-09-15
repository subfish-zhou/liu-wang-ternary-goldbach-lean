import LiuWang.Proof.Campaign20260915.ZetaMordell.SourceGaussianBridge

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Set
open scoped Real

namespace LiuWang.Proof.Campaign20260915.ZetaMordell
open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem sourceGaussian_polynomial_integrable {eta : ℝ} {m : ℕ}
    (h0 : 0 < eta - m) (h1 : eta - m < 1) (N : ℕ) (p : ℕ → ℂ) :
    Integrable (fun y : ℝ => rsDescentDirection * rsGaussianKernel eta m (rsDescentPoint eta y) *
      ∑ n ∈ Finset.range N, p n * (rsDescentPoint eta y - eta) ^ n) := by
  simp_rw [Finset.mul_sum]
  have h := integrable_finsetSum (Finset.range N)
    (fun n _ => (sourceGaussian_moment_integrable h0 h1 n).const_mul (p n))
  simpa only [mul_assoc, mul_left_comm] using h

theorem sourceGaussian_polynomial_transfer {eta : ℝ} {m : ℕ}
    (h0 : 0 < eta - m) (h1 : eta - m < 1) (N : ℕ) (p : ℕ → ℂ) :
    -(∫ y : ℝ, rsDescentDirection * rsGaussianKernel eta m (rsDescentPoint eta y) *
      ∑ n ∈ Finset.range N, p n * (rsDescentPoint eta y - eta) ^ n) =
      sourceGaussianPhase eta m *
        ∫ t : ℝ, (∑ n ∈ Finset.range N,
          p n * (siegelLine t - ((sourcePhiParameter eta m : ℂ) + 1) / 2) ^ n) *
            correctionKernel (sourcePhiParameter eta m) t := by
  have he : ∀ y : ℝ, rsDescentDirection * rsGaussianKernel eta m (rsDescentPoint eta y) *
      (∑ n ∈ Finset.range N, p n * (rsDescentPoint eta y - eta) ^ n) =
      ∑ n ∈ Finset.range N, p n *
        (rsDescentDirection * rsGaussianKernel eta m (rsDescentPoint eta y) *
          (rsDescentPoint eta y - eta) ^ n) := by
    intro y
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  simp_rw [he, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ (fun n _ => by
    simpa only [mul_assoc] using (sourceGaussian_moment_integrable h0 h1 n).const_mul (p n)),
    integral_finsetSum _ (fun n _ =>
      (correctionCenteredKernel_integrable n (sourcePhiParameter eta m)).const_mul (p n))]
  have hs n : -(∫ y : ℝ, rsDescentDirection *
      (rsGaussianKernel eta m (rsDescentPoint eta y) * (rsDescentPoint eta y - eta) ^ n)) =
      sourceGaussianPhase eta m * correctionMoment n (sourcePhiParameter eta m) := by
    simpa only [mul_assoc] using sourceGaussian_moment_integral h0 h1 n
  rw [← Finset.sum_neg_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [integral_const_mul (p n), integral_const_mul (p n), ← mul_neg, hs]
  unfold correctionMoment
  ring

theorem sourceGaussian_phiZero {eta : ℝ} {m : ℕ}
    (h0 : 0 < eta - m) (h1 : eta - m < 1) :
    -(∫ y : ℝ, rsDescentDirection * rsGaussianKernel eta m (rsDescentPoint eta y)) =
      sourceGaussianPhase eta m * (rsPhi (sourcePhiParameter eta m) : ℂ) := by
  have h := sourceGaussian_moment_integral h0 h1 0
  simp only [pow_zero, mul_one, correctionMoment, one_mul] at h
  change -(∫ y : ℝ, rsDescentDirection * rsGaussianKernel eta m (rsDescentPoint eta y)) =
    sourceGaussianPhase eta m * correctionIntegral (sourcePhiParameter eta m) at h
  rw [correctionIntegral_eq_rsPhi (sourcePhiParameter_domain h0.le h1.le)] at h
  exact h

theorem sourceGaussian_phiOne {eta : ℝ} {m : ℕ}
    (h0 : 0 < eta - m) (h1 : eta - m < 1) :
    -(∫ y : ℝ, rsDescentDirection * rsGaussianKernel eta m (rsDescentPoint eta y) *
      ((rsDescentPoint eta y - eta) / 2 -
        (2 / 3 : ℂ) * Real.pi * I * (rsDescentPoint eta y - eta) ^ 3)) =
      sourceGaussianPhase eta m * (rsPhiOne (sourcePhiParameter eta m) : ℂ) := by
  let p : ℕ → ℂ := fun n => if n = 1 then 1 / 2 else if n = 3 then -(2 / 3) * Real.pi * I else 0
  have hp (w : ℂ) : (∑ n ∈ Finset.range 4, p n * w ^ n) =
      w / 2 - (2 / 3 : ℂ) * Real.pi * I * w ^ 3 := by
    norm_num [p, Finset.sum_range_succ]
    ring
  have h := sourceGaussian_polynomial_transfer h0 h1 4 p
  simp_rw [hp] at h
  rw [correctionIntegral_phiOne (sourcePhiParameter_domain h0.le h1.le)] at h
  exact h

theorem sourceGaussian_phiOne_integrable {eta : ℝ} {m : ℕ}
    (h0 : 0 < eta - m) (h1 : eta - m < 1) :
    Integrable (fun y : ℝ => rsDescentDirection * rsGaussianKernel eta m (rsDescentPoint eta y) *
      ((rsDescentPoint eta y - eta) / 2 -
        (2 / 3 : ℂ) * Real.pi * I * (rsDescentPoint eta y - eta) ^ 3)) := by
  have h := ((sourceGaussian_moment_integrable h0 h1 1).div_const (2 : ℂ)).sub
    ((sourceGaussian_moment_integrable h0 h1 3).const_mul ((2 / 3 : ℂ) * Real.pi * I))
  convert h using 1
  funext y
  simp only [pow_one, Pi.sub_apply]
  ring

theorem sourceGaussian_phiTwo {eta : ℝ} {m : ℕ}
    (h0 : 0 < eta - m) (h1 : eta - m < 1) :
    -(∫ y : ℝ, rsDescentDirection * rsGaussianKernel eta m (rsDescentPoint eta y) *
      (-(2 / 9 : ℂ) * Real.pi ^ 2 * (rsDescentPoint eta y - eta) ^ 6 -
        (5 / 6 : ℂ) * Real.pi * I * (rsDescentPoint eta y - eta) ^ 4 +
        (3 / 8 : ℂ) * (rsDescentPoint eta y - eta) ^ 2 - I / (96 * Real.pi))) =
      sourceGaussianPhase eta m * (rsPhiTwo (sourcePhiParameter eta m) : ℂ) := by
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
  have h := sourceGaussian_polynomial_transfer h0 h1 7 p
  simp_rw [hp] at h
  rw [correctionIntegral_phiTwo (sourcePhiParameter_domain h0.le h1.le)] at h
  exact h

theorem sourceGaussian_phiTwo_integrable {eta : ℝ} {m : ℕ}
    (h0 : 0 < eta - m) (h1 : eta - m < 1) :
    Integrable (fun y : ℝ => rsDescentDirection * rsGaussianKernel eta m (rsDescentPoint eta y) *
      (-(2 / 9 : ℂ) * Real.pi ^ 2 * (rsDescentPoint eta y - eta) ^ 6 -
        (5 / 6 : ℂ) * Real.pi * I * (rsDescentPoint eta y - eta) ^ 4 +
        (3 / 8 : ℂ) * (rsDescentPoint eta y - eta) ^ 2 - I / (96 * Real.pi))) := by
  have h := ((((sourceGaussian_moment_integrable h0 h1 6).const_mul (-(2 / 9 : ℂ) * Real.pi ^ 2)).sub
    ((sourceGaussian_moment_integrable h0 h1 4).const_mul ((5 / 6 : ℂ) * Real.pi * I))).add
    ((sourceGaussian_moment_integrable h0 h1 2).const_mul (3 / 8 : ℂ))).sub
      ((sourceGaussian_moment_integrable h0 h1 0).const_mul (I / (96 * Real.pi)))
  convert h using 1
  funext y
  simp only [pow_zero, mul_one, Pi.sub_apply, Pi.add_apply]
  ring

theorem sourceLocalPolynomial_phi_derivatives (sigma : ℝ) {eta : ℝ} {m : ℕ}
    (h0 : 0 < eta - m) (h1 : eta - m < 1) (N : ℕ) :
    -(∫ y : ℝ, rsLocalPolynomialIntegrand sigma eta m N y) =
      sourceGaussianPhase eta m *
        ∑ n ∈ Finset.range N, rsSaddleCoefficient sigma (rsSaddleScale * eta) n *
          (rsSaddleScale : ℂ) ^ n / (2 * Real.pi * I) ^ n *
          ∑ j ∈ Finset.range (n + 1), (n.choose j : ℂ) *
            ((iteratedDeriv j rsPhi (sourcePhiParameter eta m) : ℝ) : ℂ) *
              gaussianJet (Real.pi * I / 2) (n - j) := by
  rw [sourceLocalPolynomial_integral sigma h0 h1 N]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  have h := correctionMoment_phi_derivatives n (sourcePhiParameter_domain h0.le h1.le)
  have hq := pow_ne_zero n mordellFrequency_ne_zero
  rw [← h]
  field_simp

theorem sourceLocalPolynomial_phi_floor (sigma : ℝ) {eta : ℝ}
    (he : 0 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) (N : ℕ) :
    -(∫ y : ℝ, rsLocalPolynomialIntegrand sigma eta ⌊eta⌋₊ N y) =
      sourceGaussianPhase eta ⌊eta⌋₊ *
        ∑ n ∈ Finset.range N, rsSaddleCoefficient sigma (rsSaddleScale * eta) n *
          (rsSaddleScale : ℂ) ^ n / (2 * Real.pi * I) ^ n *
          ∑ j ∈ Finset.range (n + 1), (n.choose j : ℂ) *
            ((iteratedDeriv j rsPhi (sourcePhiParameter eta ⌊eta⌋₊) : ℝ) : ℂ) *
              gaussianJet (Real.pi * I / 2) (n - j) :=
  sourceLocalPolynomial_phi_derivatives sigma (sourceFraction_floor he hint).1
    (sourceFraction_floor he hint).2 N

theorem sourceLocalPolynomial_interval (sigma : ℝ) {eta : ℝ} {m : ℕ}
    (h0 : 0 < eta - m) (h1 : eta - m < 1) (N : ℕ) :
    (∫ y : ℝ in (eta / 2)..(-eta / 2), rsLocalPolynomialIntegrand sigma eta m N y) =
      sourceGaussianPhase eta m *
        ∑ n ∈ Finset.range N, rsSaddleCoefficient sigma (rsSaddleScale * eta) n *
          (rsSaddleScale : ℂ) ^ n * correctionMoment n (sourcePhiParameter eta m) +
      ∫ y : ℝ in (Ioc (-eta / 2) (eta / 2))ᶜ, rsLocalPolynomialIntegrand sigma eta m N y := by
  have hf := sourceLocalPolynomial_integrable sigma h0 h1 N
  have h := integral_add_compl (s := Ioc (-eta / 2) (eta / 2)) measurableSet_Ioc hf
  rw [intervalIntegral.integral_symm,
    intervalIntegral.integral_of_le (by linarith [Nat.cast_nonneg (α := ℝ) m] : -eta / 2 ≤ eta / 2)]
  rw [← sourceLocalPolynomial_integral sigma h0 h1 N]
  linear_combination -h

end LiuWang.Proof.Campaign20260915.ZetaMordell
