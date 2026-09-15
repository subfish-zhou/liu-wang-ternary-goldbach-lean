import LiuWang.Proof.Campaign20260915.ZetaMordell.PoleFreeTransport
import LiuWang.Proof.Campaign20260915.ZetaValidation.SaddleLocalIntegral

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Filter Set
open scoped Real Topology

namespace LiuWang.Proof.Campaign20260915.ZetaMordell
open LiuWang.Proof.Campaign20260915.ZetaValidation

def sourceGaussianPhase (eta : ℝ) (m : ℕ) : ℂ :=
  exp (-Real.pi * I * (((eta - m : ℝ) : ℂ) ^ 2 + 1 / 8))

def sourcePhiParameter (eta : ℝ) (m : ℕ) : ℝ := 2 * (eta - m) - 1

theorem sourceFraction_floor {eta : ℝ} (he : 0 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    0 < eta - (⌊eta⌋₊ : ℝ) ∧ eta - (⌊eta⌋₊ : ℝ) < 1 := by
  have hl := Nat.floor_le he
  have hu := Nat.lt_floor_add_one eta
  have hn : eta ≠ (⌊eta⌋₊ : ℝ) := by exact_mod_cast hint (⌊eta⌋₊ : ℤ)
  have hlt := lt_of_le_of_ne hl hn.symm
  constructor <;> linarith

theorem sourcePhiParameter_mem {eta : ℝ} {m : ℕ}
    (h0 : 0 ≤ eta - m) (h1 : eta - m ≤ 1) :
    |sourcePhiParameter eta m| ≤ 1 := by
  unfold sourcePhiParameter
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem sourcePhiParameter_domain {eta : ℝ} {m : ℕ}
    (h0 : 0 ≤ eta - m) (h1 : eta - m ≤ 1) :
    |sourcePhiParameter eta m| < 3 / 2 := by
  linarith [sourcePhiParameter_mem h0 h1]

theorem sourcePhiParameter_floor_domain {eta : ℝ} (he : 0 ≤ eta) :
    |sourcePhiParameter eta ⌊eta⌋₊| < 3 / 2 :=
  sourcePhiParameter_domain (Nat.zero_le_self_sub_floor he) (Nat.self_sub_floor_lt_one eta).le

theorem sourcePhiParameter_delta (eta : ℝ) (m : ℕ) :
    2 * (rsSaddleScale * (eta - m - 1 / 2)) / rsSaddleScale = sourcePhiParameter eta m := by
  unfold sourcePhiParameter
  field_simp [rsSaddleScale_pos.ne']

theorem sourceGaussian_integer_shift (eta : ℝ) (m : ℕ) (x : ℂ) :
    rsGaussianKernel eta m (x + m) =
      sourceGaussianPhase eta m *
        (exp (Real.pi * I * (x ^ 2 - 2 * (x - (eta - m : ℝ)) ^ 2 + 1 / 8)) /
          (exp (2 * Real.pi * I * x) - 1)) := by
  have hd : exp (2 * Real.pi * I * (x + m)) = exp (2 * Real.pi * I * x) := by
    rw [mul_add, exp_add]
    have hm : exp (2 * Real.pi * I * (m : ℂ)) = 1 := by
      simpa only [mul_comm] using exp_nat_mul_two_pi_mul_I m
    rw [hm, mul_one]
  unfold rsGaussianKernel rsHankelDenominator sourceGaussianPhase
  rw [hd, ← mul_div_assoc, ← exp_add]
  congr 2
  push_cast
  ring

theorem sourceGaussian_descent_coordinates (eta y : ℝ) (m : ℕ) :
    rsDescentPoint eta y =
      poleFreePoint (((-(4 / Real.sqrt 2) * y + (1 - 2 * (eta - m)) : ℝ) : ℂ) +
        ((1 - 2 * (eta - m) : ℝ) : ℂ) * I) + m := by
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
  unfold rsDescentPoint rsDescentDirection poleFreePoint poleFreeRotor
  push_cast
  field_simp
  ring_nf
  simp only [I_sq]
  ring

theorem sourceGaussian_moment_pointwise (eta y : ℝ) (m n : ℕ) :
    rsDescentDirection * rsGaussianKernel eta m (rsDescentPoint eta y) *
        (rsDescentPoint eta y - eta) ^ n =
      (-(4 / Real.sqrt 2 : ℝ) : ℂ) * sourceGaussianPhase eta m *
        poleFreeKernel n (eta - m : ℝ)
          (((-(4 / Real.sqrt 2) * y + (1 - 2 * (eta - m)) : ℝ) : ℂ) +
            ((1 - 2 * (eta - m) : ℝ) : ℂ) * I) := by
  rw [sourceGaussian_descent_coordinates, sourceGaussian_integer_shift]
  unfold poleFreeKernel rsDescentDirection poleFreeRotor
  push_cast
  have hc : ∀ x : ℂ, x + m - eta = x - ((eta : ℂ) - m) := by intro x; ring
  simp only [hc]
  ring

theorem sourceGaussian_moment_integrable {eta : ℝ} {m : ℕ}
    (h0 : 0 < eta - m) (h1 : eta - m < 1) (n : ℕ) :
    Integrable (fun y : ℝ => rsDescentDirection * rsGaussianKernel eta m (rsDescentPoint eta y) *
      (rsDescentPoint eta y - eta) ^ n) := by
  have hy : |1 - 2 * (eta - m)| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hk : -(4 / Real.sqrt 2) ≠ (0 : ℝ) :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (Real.sqrt_ne_zero'.mpr (by norm_num)))
  have h := ((poleFreeKernel_horizontal_integrable n (eta - m : ℝ) hy).comp_add_right
    (1 - 2 * (eta - m))).comp_mul_left' hk
  simp_rw [sourceGaussian_moment_pointwise]
  exact h.const_mul _

theorem sourceGaussian_moment_integral {eta : ℝ} {m : ℕ}
    (h0 : 0 < eta - m) (h1 : eta - m < 1) (n : ℕ) :
    -(∫ y : ℝ, rsDescentDirection * rsGaussianKernel eta m (rsDescentPoint eta y) *
        (rsDescentPoint eta y - eta) ^ n) =
      sourceGaussianPhase eta m * correctionMoment n (sourcePhiParameter eta m) := by
  let k : ℝ := -(4 / Real.sqrt 2)
  let v : ℝ := 1 - 2 * (eta - m)
  have hk : k < 0 := neg_neg_of_pos (by positivity : 0 < 4 / Real.sqrt 2)
  have hv : |v| < 1 := by dsimp [v]; exact abs_lt.mpr ⟨by linarith, by linarith⟩
  simp_rw [sourceGaussian_moment_pointwise]
  simp only [← ofReal_neg]
  change -(∫ y : ℝ, (k : ℂ) * sourceGaussianPhase eta m *
    poleFreeKernel n (eta - m : ℝ) ((k * y + v : ℝ) + (v : ℂ) * I)) = _
  rw [integral_const_mul, Measure.integral_comp_mul_left
    (fun t : ℝ => poleFreeKernel n (eta - m : ℝ) ((t + v : ℝ) + (v : ℂ) * I)) k,
    integral_add_right_eq_self (fun t : ℝ => poleFreeKernel n (eta - m : ℝ) ((t : ℂ) + v * I)) v,
    poleFreeKernel_integral_moment n (eta - m : ℝ) hv]
  simp only [abs_inv, abs_of_neg hk, real_smul, ofReal_inv, ofReal_neg]
  have hkC : (k : ℂ) ≠ 0 := ofReal_ne_zero.mpr hk.ne
  have hz : (2 * ((eta - m : ℝ) : ℂ) - 1) = (sourcePhiParameter eta m : ℂ) := by
    unfold sourcePhiParameter
    push_cast
    ring
  rw [hz]
  field_simp

theorem sourceGaussian_scaled_moment_integrable {eta : ℝ} {m : ℕ}
    (h0 : 0 < eta - m) (h1 : eta - m < 1) (n : ℕ) :
    Integrable (fun y : ℝ => rsDescentDirection * rsGaussianKernel eta m (rsDescentPoint eta y) *
      ((rsSaddleScale : ℂ) * (rsDescentPoint eta y - eta)) ^ n) := by
  simpa only [mul_pow, mul_left_comm, mul_assoc] using
    (sourceGaussian_moment_integrable h0 h1 n).const_mul ((rsSaddleScale : ℂ) ^ n)

theorem sourceGaussian_scaled_moment_integral {eta : ℝ} {m : ℕ}
    (h0 : 0 < eta - m) (h1 : eta - m < 1) (n : ℕ) :
    -(∫ y : ℝ, rsDescentDirection * rsGaussianKernel eta m (rsDescentPoint eta y) *
      ((rsSaddleScale : ℂ) * (rsDescentPoint eta y - eta)) ^ n) =
      sourceGaussianPhase eta m * (rsSaddleScale : ℂ) ^ n *
        correctionMoment n (sourcePhiParameter eta m) := by
  simp_rw [mul_pow, show ∀ y : ℝ,
    rsDescentDirection * rsGaussianKernel eta m (rsDescentPoint eta y) *
      ((rsSaddleScale : ℂ) ^ n * (rsDescentPoint eta y - eta) ^ n) =
    (rsSaddleScale : ℂ) ^ n *
      (rsDescentDirection * rsGaussianKernel eta m (rsDescentPoint eta y) *
        (rsDescentPoint eta y - eta) ^ n) from fun _ => by ring]
  rw [integral_const_mul, ← mul_neg, sourceGaussian_moment_integral h0 h1 n]
  ring

theorem sourceLocalPolynomial_integrable (sigma : ℝ) {eta : ℝ} {m : ℕ}
    (h0 : 0 < eta - m) (h1 : eta - m < 1) (N : ℕ) :
    Integrable (rsLocalPolynomialIntegrand sigma eta m N) := by
  unfold rsLocalPolynomialIntegrand
  simp_rw [Finset.mul_sum, ← mul_assoc,
    mul_comm (rsDescentDirection * rsGaussianKernel eta m (rsDescentPoint eta _))
      (rsSaddleCoefficient sigma (rsSaddleScale * eta) _), mul_assoc]
  apply integrable_finsetSum
  intro n _
  simpa only [mul_assoc] using (sourceGaussian_scaled_moment_integrable h0 h1 n).const_mul
    (rsSaddleCoefficient sigma (rsSaddleScale * eta) n)

theorem sourceLocalPolynomial_integral (sigma : ℝ) {eta : ℝ} {m : ℕ}
    (h0 : 0 < eta - m) (h1 : eta - m < 1) (N : ℕ) :
    -(∫ y : ℝ, rsLocalPolynomialIntegrand sigma eta m N y) =
      sourceGaussianPhase eta m *
        ∑ n ∈ Finset.range N, rsSaddleCoefficient sigma (rsSaddleScale * eta) n *
          (rsSaddleScale : ℂ) ^ n * correctionMoment n (sourcePhiParameter eta m) := by
  have he : ∀ y : ℝ, rsLocalPolynomialIntegrand sigma eta m N y =
      ∑ n ∈ Finset.range N, rsSaddleCoefficient sigma (rsSaddleScale * eta) n *
        (rsDescentDirection * rsGaussianKernel eta m (rsDescentPoint eta y) *
          ((rsSaddleScale : ℂ) * (rsDescentPoint eta y - eta)) ^ n) := by
    intro y
    simp only [rsLocalPolynomialIntegrand, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun n _ => (sourceGaussian_scaled_moment_integrable h0 h1 n).const_mul _)]
  simp_rw [integral_const_mul, ← Finset.sum_neg_distrib, ← mul_neg,
    sourceGaussian_scaled_moment_integral h0 h1]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

end LiuWang.Proof.Campaign20260915.ZetaMordell
