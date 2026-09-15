import LiuWang.Proof.Campaign20260915.ZetaJnCentral.SharpSeventhIntegral
import LiuWang.Proof.Campaign20260915.ZetaJnCentral.SourceOrderConsumer

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

theorem floorContour_seven_sharp {eta : ℝ}
    (he : 44 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    ‖jnFloorContour (1 / 2) eta 7‖ ≤ (51 / 50) / eta ^ 3 := by
  rw [jn_floor_contour_eq (1 / 2) (by linarith : 2 ≤ eta) hint 6]
  exact (jn_floor_seven_sharp he).2

theorem local_hankel_seven_sharp_error {eta : ℝ}
    (he : 44 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    ‖(∫ y : ℝ in (eta / 2)..(-eta / 2), rsDescentDirection *
      rsHankelKernel ((1 / 2 : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2)
        ⌊eta⌋₊ (rsDescentPoint eta y)) -
      rsLocalPrefactor (1 / 2) eta ⌊eta⌋₊ *
        (sourceGaussianPhase eta ⌊eta⌋₊ *
          ∑ n ∈ Finset.range 7, rsSaddleCoefficient (1 / 2) (rsSaddleScale * eta) n *
            (rsSaddleScale : ℂ) ^ n * correctionMoment n (sourcePhiParameter eta ⌊eta⌋₊))‖ ≤
      eta ^ (-(1 / 2 : ℝ)) *
        ((51 / 50) / eta ^ 3 + 120000 / eta * Real.exp (-Real.pi * eta ^ 2 / 8)) := by
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
  have hj : ‖F * J‖ ≤ eta ^ (-(1 / 2 : ℝ)) * ((51 / 50) / eta ^ 3) := by
    rw [norm_mul, show ‖F‖ = eta ^ (-(1 / 2 : ℝ)) by
      simpa only [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num] using
        exterior_localPrefactor_norm (1 / 2) he0 ⌊eta⌋₊]
    exact mul_le_mul_of_nonneg_left (jn_floor_seven_sharp he).2 (Real.rpow_nonneg he0.le _)
  change ‖H - F * P‖ ≤ _
  calc
    _ = ‖(H - F * (P + J)) + F * J‖ := by congr 1; ring
    _ ≤ ‖H - F * (P + J)‖ + ‖F * J‖ := norm_add_le _ _
    _ ≤ _ := (add_le_add ho hj).trans_eq (by ring)

theorem local_hankel_seven_sharp_R2 {eta : ℝ}
    (he : 0 ≤ eta) (ht : 2000 < eta ^ 2) (hint : ∀ k : ℤ, eta ≠ k) :
    ‖(∫ y : ℝ in (eta / 2)..(-eta / 2), rsDescentDirection *
      rsHankelKernel ((1 / 2 : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2)
        ⌊eta⌋₊ (rsDescentPoint eta y)) -
      rsLocalPrefactor (1 / 2) eta ⌊eta⌋₊ *
        (sourceGaussianPhase eta ⌊eta⌋₊ *
          ∑ n ∈ Finset.range 7, rsSaddleCoefficient (1 / 2) (rsSaddleScale * eta) n *
            (rsSaddleScale : ℂ) ^ n * correctionMoment n (sourcePhiParameter eta ⌊eta⌋₊))‖ ≤
      eta ^ (-(1 / 2 : ℝ)) * ((103 / 100) / eta ^ 3) := by
  have he44 : 44 ≤ eta := by nlinarith
  have he0 : 0 < eta := by linarith
  have h := local_hankel_seven_sharp_error he44 hint
  apply h.trans
  apply mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg he _)
  apply (add_le_add le_rfl (exterior_large_scalar (by linarith : 10 ≤ eta))).trans
  have hs : eta ^ 4 = eta * eta ^ 3 := by ring
  rw [hs]
  field_simp
  nlinarith

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
