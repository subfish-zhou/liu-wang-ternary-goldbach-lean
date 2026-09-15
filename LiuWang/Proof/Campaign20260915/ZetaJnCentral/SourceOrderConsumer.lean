import LiuWang.Proof.Campaign20260915.ZetaJnCentral.SeventhIntegral
import LiuWang.Proof.Campaign20260915.ZetaJnCentral.FloorContour
import LiuWang.Proof.Campaign20260915.ZetaJnCentral.LocalHankelConsumer

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

theorem floorContour_source_orders {eta : ℝ}
    (he : 2 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    ‖jnFloorContour (1 / 2) eta 1‖ ≤ firstOrderJnConstant (1 / 2) / eta ∧
    ‖jnFloorContour (1 / 2) eta 7‖ ≤ seventhJnConstant / eta ^ 3 := by
  have he0 : 0 < eta := by linarith
  have h0 := Nat.zero_le_self_sub_floor he0.le
  have h1 := (Nat.self_sub_floor_lt_one eta).le
  constructor
  · rw [jn_floor_contour_eq (1 / 2) he hint 0]
    exact jn_one_source_order (1 / 2) he0 h0 h1
  · rw [jn_floor_contour_eq (1 / 2) he hint 6]
    exact jn_seven_source_order he h0 h1

theorem jn_R0_height (sigma : ℝ) {eta : ℝ}
    (he : 0 ≤ eta) (ht : 125 < eta ^ 2) :
    IntervalIntegrable (rsJnIntegrand sigma eta ⌊eta⌋₊ 1) volume (eta / 2) (-eta / 2) ∧
    ‖∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand sigma eta ⌊eta⌋₊ 1 y‖ ≤
      firstOrderJnConstant sigma / eta := by
  have he0 : 0 < eta := by nlinarith
  have h0 := Nat.zero_le_self_sub_floor he
  have h1 := (Nat.self_sub_floor_lt_one eta).le
  exact ⟨jn_local_integrable sigma he0 h0 h1 0, jn_one_source_order sigma he0 h0 h1⟩

theorem jn_R2_height {eta : ℝ} (he : 0 ≤ eta) (ht : 2000 < eta ^ 2) :
    IntervalIntegrable (rsJnIntegrand (1 / 2) eta ⌊eta⌋₊ 7) volume (eta / 2) (-eta / 2) ∧
    ‖∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta ⌊eta⌋₊ 7 y‖ ≤
      seventhJnConstant / eta ^ 3 := by
  have he2 : 2 ≤ eta := by nlinarith
  exact jn_floor_seven_source_order he2

theorem local_hankel_seven_source_error {eta : ℝ}
    (he : 2 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    ‖(∫ y : ℝ in (eta / 2)..(-eta / 2), rsDescentDirection *
      rsHankelKernel ((1 / 2 : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2)
        ⌊eta⌋₊ (rsDescentPoint eta y)) -
      rsLocalPrefactor (1 / 2) eta ⌊eta⌋₊ *
        (sourceGaussianPhase eta ⌊eta⌋₊ *
          ∑ n ∈ Finset.range 7, rsSaddleCoefficient (1 / 2) (rsSaddleScale * eta) n *
            (rsSaddleScale : ℂ) ^ n * correctionMoment n (sourcePhiParameter eta ⌊eta⌋₊))‖ ≤
      eta ^ (-(1 / 2 : ℝ)) *
        (seventhJnConstant / eta ^ 3 +
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
    exterior_localHankel_seven (by linarith) hint
  have hj : ‖F * J‖ ≤ eta ^ (-(1 / 2 : ℝ)) * (seventhJnConstant / eta ^ 3) := by
    rw [norm_mul, show ‖F‖ = eta ^ (-(1 / 2 : ℝ)) by
      simpa only [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num] using
        exterior_localPrefactor_norm (1 / 2) he0 ⌊eta⌋₊]
    exact mul_le_mul_of_nonneg_left (jn_floor_seven_source_order he).2
      (Real.rpow_nonneg he0.le _)
  change ‖H - F * P‖ ≤ _
  calc
    _ = ‖(H - F * (P + J)) + F * J‖ := by congr 1; ring
    _ ≤ ‖H - F * (P + J)‖ + ‖F * J‖ := norm_add_le _ _
    _ ≤ _ := (add_le_add ho hj).trans_eq (by ring)

theorem local_hankel_seven_R2_domain {eta : ℝ}
    (he : 0 ≤ eta) (ht : 2000 < eta ^ 2) (hint : ∀ k : ℤ, eta ≠ k) :
    ‖(∫ y : ℝ in (eta / 2)..(-eta / 2), rsDescentDirection *
      rsHankelKernel ((1 / 2 : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2)
        ⌊eta⌋₊ (rsDescentPoint eta y)) -
      rsLocalPrefactor (1 / 2) eta ⌊eta⌋₊ *
        (sourceGaussianPhase eta ⌊eta⌋₊ *
          ∑ n ∈ Finset.range 7, rsSaddleCoefficient (1 / 2) (rsSaddleScale * eta) n *
            (rsSaddleScale : ℂ) ^ n * correctionMoment n (sourcePhiParameter eta ⌊eta⌋₊))‖ ≤
      eta ^ (-(1 / 2 : ℝ)) * (seventhJnConstant / eta ^ 3 + 1 / (10 * eta ^ 4)) := by
  have he10 : 10 ≤ eta := by nlinarith
  have h := local_hankel_seven_source_error (by linarith : 2 ≤ eta) hint
  exact h.trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (exterior_large_scalar he10)) (Real.rpow_nonneg he _))

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
