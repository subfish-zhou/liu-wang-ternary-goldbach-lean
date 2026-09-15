import LiuWang.Proof.Campaign20260915.ZetaJnCentral.FirstOrderIntegral
import LiuWang.Proof.Campaign20260915.ZetaMordell.ExteriorLocalHankel

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

theorem local_hankel_taylor_error (sigma : ℝ) {eta R d : ℝ}
    (he : 0 < eta) (hint : ∀ k : ℤ, eta ≠ k)
    (hR0 : 0 < R) (hR : R ≤ 3 / 5 * (rsSaddleScale * eta))
    (hd : 0 < d) (hdR : 21 / 20 * (rsSaddleScale * d) ≤ R) (hde : d ≤ eta / 2)
    (N : ℕ) :
    ‖(∫ y : ℝ in (eta / 2)..(-eta / 2), rsDescentDirection *
      rsHankelKernel ((sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2)
        ⌊eta⌋₊ (rsDescentPoint eta y)) -
      rsLocalPrefactor sigma eta ⌊eta⌋₊ *
        ∫ y : ℝ in (eta / 2)..(-eta / 2),
          rsLocalPolynomialIntegrand sigma eta ⌊eta⌋₊ (N + 1) y‖ ≤
      eta ^ (sigma - 1) * localJnBudget sigma eta R d N := by
  rw [rsHankel_local_truncation sigma ⌊eta⌋₊ (N + 1) he hint, mul_add,
    add_sub_cancel_left, norm_mul, exterior_localPrefactor_norm sigma he ⌊eta⌋₊]
  exact mul_le_mul_of_nonneg_left
    (jn_floor_local_budget sigma he hR0 hR hd hdR hde N).2
    (Real.rpow_nonneg he.le _)

theorem local_hankel_one_error (sigma : ℝ) {eta : ℝ}
    (he : 1 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    ‖(∫ y : ℝ in (eta / 2)..(-eta / 2), rsDescentDirection *
      rsHankelKernel ((sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2)
        ⌊eta⌋₊ (rsDescentPoint eta y)) -
      rsLocalPrefactor sigma eta ⌊eta⌋₊ *
        (sourceGaussianPhase eta ⌊eta⌋₊ * (rsPhi (sourcePhiParameter eta ⌊eta⌋₊) : ℂ))‖ ≤
      eta ^ (sigma - 1) *
        (firstOrderJnConstant sigma / eta +
          4 / (Real.pi * eta) * Real.exp (-Real.pi * eta ^ 2 / 4)) := by
  let H := ∫ y : ℝ in (eta / 2)..(-eta / 2), rsDescentDirection *
    rsHankelKernel ((sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2)
      ⌊eta⌋₊ (rsDescentPoint eta y)
  let F := rsLocalPrefactor sigma eta ⌊eta⌋₊
  let P := sourceGaussianPhase eta ⌊eta⌋₊ * (rsPhi (sourcePhiParameter eta ⌊eta⌋₊) : ℂ)
  let J := ∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand sigma eta ⌊eta⌋₊ 1 y
  have he0 : 0 < eta := by linarith
  have ho : ‖H - F * (P + J)‖ ≤ eta ^ (sigma - 1) *
      (4 / (Real.pi * eta) * Real.exp (-Real.pi * eta ^ 2 / 4)) :=
    exterior_localHankel_one sigma he hint
  have hj : ‖F * J‖ ≤ eta ^ (sigma - 1) * (firstOrderJnConstant sigma / eta) := by
    rw [norm_mul, show ‖F‖ = eta ^ (sigma - 1) from
      exterior_localPrefactor_norm sigma he0 ⌊eta⌋₊]
    exact mul_le_mul_of_nonneg_left
      (jn_one_source_order sigma he0 (Nat.zero_le_self_sub_floor he0.le)
        (Nat.self_sub_floor_lt_one eta).le) (Real.rpow_nonneg he0.le _)
  change ‖H - F * P‖ ≤ _
  calc
    _ = ‖(H - F * (P + J)) + F * J‖ := by congr 1; ring
    _ ≤ ‖H - F * (P + J)‖ + ‖F * J‖ := norm_add_le _ _
    _ ≤ _ := (add_le_add ho hj).trans_eq (by ring)

theorem local_hankel_seven_error {eta R d : ℝ}
    (he : 1 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k)
    (hR0 : 0 < R) (hR : R ≤ 3 / 5 * (rsSaddleScale * eta))
    (hd : 0 < d) (hdR : 21 / 20 * (rsSaddleScale * d) ≤ R) (hde : d ≤ eta / 2) :
    ‖(∫ y : ℝ in (eta / 2)..(-eta / 2), rsDescentDirection *
      rsHankelKernel ((1 / 2 : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2)
        ⌊eta⌋₊ (rsDescentPoint eta y)) -
      rsLocalPrefactor (1 / 2) eta ⌊eta⌋₊ *
        (sourceGaussianPhase eta ⌊eta⌋₊ *
          ∑ n ∈ Finset.range 7, rsSaddleCoefficient (1 / 2) (rsSaddleScale * eta) n *
            (rsSaddleScale : ℂ) ^ n * correctionMoment n (sourcePhiParameter eta ⌊eta⌋₊))‖ ≤
      eta ^ (-(1 / 2 : ℝ)) *
        (localJnBudget (1 / 2) eta R d 6 +
          120000 / eta * Real.exp (-Real.pi * eta ^ 2 / 8)) := by
  let H := ∫ y : ℝ in (eta / 2)..(-eta / 2), rsDescentDirection *
    rsHankelKernel ((1 / 2 : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2)
      ⌊eta⌋₊ (rsDescentPoint eta y)
  let F := rsLocalPrefactor (1 / 2) eta ⌊eta⌋₊
  let P := sourceGaussianPhase eta ⌊eta⌋₊ *
    ∑ n ∈ Finset.range 7, rsSaddleCoefficient (1 / 2) (rsSaddleScale * eta) n *
      (rsSaddleScale : ℂ) ^ n * correctionMoment n (sourcePhiParameter eta ⌊eta⌋₊)
  let J := ∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta ⌊eta⌋₊ 7 y
  have he0 : 0 < eta := by linarith
  have ho : ‖H - F * (P + J)‖ ≤ eta ^ (-(1 / 2 : ℝ)) *
      (120000 / eta * Real.exp (-Real.pi * eta ^ 2 / 8)) :=
    exterior_localHankel_seven he hint
  have hj : ‖F * J‖ ≤ eta ^ (-(1 / 2 : ℝ)) * localJnBudget (1 / 2) eta R d 6 := by
    rw [norm_mul, show ‖F‖ = eta ^ (-(1 / 2 : ℝ)) by
      simpa only [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num] using
        exterior_localPrefactor_norm (1 / 2) he0 ⌊eta⌋₊]
    exact mul_le_mul_of_nonneg_left
      (jn_floor_local_budget (1 / 2) he0 hR0 hR hd hdR hde 6).2
      (Real.rpow_nonneg he0.le _)
  change ‖H - F * P‖ ≤ _
  calc
    _ = ‖(H - F * (P + J)) + F * J‖ := by congr 1; ring
    _ ≤ ‖H - F * (P + J)‖ + ‖F * J‖ := norm_add_le _ _
    _ ≤ _ := (add_le_add ho hj).trans_eq (by ring)

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
