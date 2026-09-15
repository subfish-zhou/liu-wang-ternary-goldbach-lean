import LiuWang.Proof.Campaign20260915.ZetaMordell.ExteriorHeightBudget

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Set
open scoped Real

namespace LiuWang.Proof.Campaign20260915.ZetaMordell
open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem exterior_localPrefactor_norm (sigma : ℝ) {eta : ℝ} (he : 0 < eta) (m : ℕ) :
    ‖rsLocalPrefactor sigma eta m‖ = eta ^ (sigma - 1) := by
  unfold rsLocalPrefactor
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos he, norm_exp]
  simp [mul_re, mul_im, pow_two]

theorem exterior_localHankel_difference (sigma : ℝ) (N : ℕ) {eta : ℝ}
    (he : 0 < eta) (hint : ∀ k : ℤ, eta ≠ k) :
    (∫ y : ℝ in (eta / 2)..(-eta / 2), rsDescentDirection *
      rsHankelKernel ((sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2)
        ⌊eta⌋₊ (rsDescentPoint eta y)) -
      rsLocalPrefactor sigma eta ⌊eta⌋₊ *
        ((sourceGaussianPhase eta ⌊eta⌋₊ *
          ∑ n ∈ Finset.range N, rsSaddleCoefficient sigma (rsSaddleScale * eta) n *
            (rsSaddleScale : ℂ) ^ n * correctionMoment n (sourcePhiParameter eta ⌊eta⌋₊)) +
          ∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand sigma eta ⌊eta⌋₊ N y) =
      rsLocalPrefactor sigma eta ⌊eta⌋₊ *
        ∫ y : ℝ in (Ioc (-eta / 2) (eta / 2))ᶜ,
          rsLocalPolynomialIntegrand sigma eta ⌊eta⌋₊ N y := by
  have hf := sourceFraction_floor he.le hint
  rw [rsHankel_local_truncation sigma ⌊eta⌋₊ N he hint,
    sourceLocalPolynomial_interval sigma hf.1 hf.2 N]
  ring

theorem exterior_localHankel_budget (sigma : ℝ) (N : ℕ) {eta : ℝ}
    (he : 1 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    ‖(∫ y : ℝ in (eta / 2)..(-eta / 2), rsDescentDirection *
      rsHankelKernel ((sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2)
        ⌊eta⌋₊ (rsDescentPoint eta y)) -
      rsLocalPrefactor sigma eta ⌊eta⌋₊ *
        ((sourceGaussianPhase eta ⌊eta⌋₊ *
          ∑ n ∈ Finset.range N, rsSaddleCoefficient sigma (rsSaddleScale * eta) n *
            (rsSaddleScale : ℂ) ^ n * correctionMoment n (sourcePhiParameter eta ⌊eta⌋₊)) +
          ∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand sigma eta ⌊eta⌋₊ N y)‖ ≤
      eta ^ (sigma - 1) *
        ((24 * ∑ n ∈ Finset.range N,
          ‖rsSaddleCoefficient sigma (rsSaddleScale * eta) n * (rsSaddleScale : ℂ) ^ n‖ *
            (n.factorial : ℝ)) / (Real.pi * eta) * Real.exp (-Real.pi * eta ^ 2 / 8)) := by
  rw [exterior_localHankel_difference sigma N (by linarith) hint, norm_mul,
    exterior_localPrefactor_norm sigma (by linarith) ⌊eta⌋₊]
  exact mul_le_mul_of_nonneg_left
    ((norm_integral_le_integral_norm _).trans (exterior_polynomial_general_budget sigma he
      (Nat.zero_le_self_sub_floor (by linarith)) (Nat.self_sub_floor_lt_one eta).le N))
    (Real.rpow_nonneg (by linarith) _)

theorem exterior_localHankel_one (sigma : ℝ) {eta : ℝ}
    (he : 1 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    ‖(∫ y : ℝ in (eta / 2)..(-eta / 2), rsDescentDirection *
      rsHankelKernel ((sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2)
        ⌊eta⌋₊ (rsDescentPoint eta y)) -
      rsLocalPrefactor sigma eta ⌊eta⌋₊ *
        (sourceGaussianPhase eta ⌊eta⌋₊ * (rsPhi (sourcePhiParameter eta ⌊eta⌋₊) : ℂ) +
          ∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand sigma eta ⌊eta⌋₊ 1 y)‖ ≤
      eta ^ (sigma - 1) * (4 / (Real.pi * eta) * Real.exp (-Real.pi * eta ^ 2 / 4)) := by
  have hd := exterior_localHankel_difference sigma 1 (by linarith : 0 < eta) hint
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    sourceSaddle_scaled_zero, one_mul,
    correctionMoment_zero_phi (sourcePhiParameter_floor_domain (by linarith))] at hd
  rw [hd, norm_mul, exterior_localPrefactor_norm sigma (by linarith) ⌊eta⌋₊]
  exact mul_le_mul_of_nonneg_left
    ((norm_integral_le_integral_norm _).trans (exterior_floor_one sigma he))
    (Real.rpow_nonneg (by linarith) _)

theorem exterior_localHankel_seven {eta : ℝ}
    (he : 1 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    ‖(∫ y : ℝ in (eta / 2)..(-eta / 2), rsDescentDirection *
      rsHankelKernel ((1 / 2 : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2)
        ⌊eta⌋₊ (rsDescentPoint eta y)) -
      rsLocalPrefactor (1 / 2) eta ⌊eta⌋₊ *
        ((sourceGaussianPhase eta ⌊eta⌋₊ *
          ∑ n ∈ Finset.range 7, rsSaddleCoefficient (1 / 2) (rsSaddleScale * eta) n *
            (rsSaddleScale : ℂ) ^ n * correctionMoment n (sourcePhiParameter eta ⌊eta⌋₊)) +
          ∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta ⌊eta⌋₊ 7 y)‖ ≤
      eta ^ (-(1 / 2 : ℝ)) * (120000 / eta * Real.exp (-Real.pi * eta ^ 2 / 8)) := by
  have hd := exterior_localHankel_difference (1 / 2) 7 (by linarith : 0 < eta) hint
  norm_num only [ofReal_div, ofReal_one, ofReal_ofNat] at hd
  rw [hd, norm_mul, exterior_localPrefactor_norm (1 / 2) (by linarith) ⌊eta⌋₊]
  norm_num only [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num]
  exact mul_le_mul_of_nonneg_left
    ((norm_integral_le_integral_norm _).trans (exterior_floor_seven he))
    (Real.rpow_nonneg (by linarith) _)

theorem exterior_localHankel_seven_large {eta : ℝ}
    (he : 10 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    ‖(∫ y : ℝ in (eta / 2)..(-eta / 2), rsDescentDirection *
      rsHankelKernel ((1 / 2 : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2)
        ⌊eta⌋₊ (rsDescentPoint eta y)) -
      rsLocalPrefactor (1 / 2) eta ⌊eta⌋₊ *
        ((sourceGaussianPhase eta ⌊eta⌋₊ *
          ∑ n ∈ Finset.range 7, rsSaddleCoefficient (1 / 2) (rsSaddleScale * eta) n *
            (rsSaddleScale : ℂ) ^ n * correctionMoment n (sourcePhiParameter eta ⌊eta⌋₊)) +
          ∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta ⌊eta⌋₊ 7 y)‖ ≤
      eta ^ (-(1 / 2 : ℝ)) / (10 * eta ^ 4) := by
  apply (exterior_localHankel_seven (by linarith) hint).trans
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left (exterior_large_scalar he)
    (Real.rpow_nonneg (by linarith : 0 ≤ eta) (-(1 / 2 : ℝ)))

end LiuWang.Proof.Campaign20260915.ZetaMordell
