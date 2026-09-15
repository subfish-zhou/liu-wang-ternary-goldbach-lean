import LiuWang.Proof.Campaign20260915.ZetaJnCentral.SharpFirstIntegral
import LiuWang.Proof.Campaign20260915.ZetaJnCentral.SharpLocalHankel

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

theorem source_R0_Jn_budget {eta : ℝ} (he : 0 ≤ eta) (ht : 125 < eta ^ 2) :
    IntervalIntegrable (rsJnIntegrand (1 / 2) eta ⌊eta⌋₊ 1) volume (eta / 2) (-eta / 2) ∧
    ‖∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta ⌊eta⌋₊ 1 y‖ ≤
      (731 / 1000) / eta :=
  jn_floor_one_sharp (by nlinarith)

theorem source_R2_Jn_budget {eta : ℝ} (he : 0 ≤ eta) (ht : 2000 < eta ^ 2) :
    IntervalIntegrable (rsJnIntegrand (1 / 2) eta ⌊eta⌋₊ 7) volume (eta / 2) (-eta / 2) ∧
    ‖∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta ⌊eta⌋₊ 7 y‖ ≤
      (51 / 50) / eta ^ 3 :=
  jn_floor_seven_sharp (by nlinarith)

theorem source_R0_contour_budget {eta : ℝ}
    (he : 0 ≤ eta) (ht : 125 < eta ^ 2) (hint : ∀ k : ℤ, eta ≠ k) :
    ‖jnFloorContour (1 / 2) eta 1‖ ≤ (731 / 1000) / eta := by
  rw [jn_floor_contour_eq (1 / 2) (by nlinarith : 2 ≤ eta) hint 0]
  exact (source_R0_Jn_budget he ht).2

theorem source_R2_contour_budget {eta : ℝ}
    (he : 0 ≤ eta) (ht : 2000 < eta ^ 2) (hint : ∀ k : ℤ, eta ≠ k) :
    ‖jnFloorContour (1 / 2) eta 7‖ ≤ (51 / 50) / eta ^ 3 :=
  floorContour_seven_sharp (by nlinarith) hint

theorem local_hankel_one_sharp_error {eta : ℝ}
    (he : 11 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    ‖(∫ y : ℝ in (eta / 2)..(-eta / 2), rsDescentDirection *
      rsHankelKernel ((1 / 2 : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2)
        ⌊eta⌋₊ (rsDescentPoint eta y)) -
      rsLocalPrefactor (1 / 2) eta ⌊eta⌋₊ *
        (sourceGaussianPhase eta ⌊eta⌋₊ * (rsPhi (sourcePhiParameter eta ⌊eta⌋₊) : ℂ))‖ ≤
      eta ^ (-(1 / 2 : ℝ)) * ((731 / 1000) / eta +
        4 / (Real.pi * eta) * Real.exp (-Real.pi * eta ^ 2 / 4)) := by
  let H := ∫ y : ℝ in (eta / 2)..(-eta / 2), rsDescentDirection *
    rsHankelKernel ((1 / 2 : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2)
      ⌊eta⌋₊ (rsDescentPoint eta y)
  let F := rsLocalPrefactor (1 / 2) eta ⌊eta⌋₊
  let P := sourceGaussianPhase eta ⌊eta⌋₊ * (rsPhi (sourcePhiParameter eta ⌊eta⌋₊) : ℂ)
  let J := ∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta ⌊eta⌋₊ 1 y
  have he0 : 0 < eta := by linarith
  have ho : ‖H - F * (P + J)‖ ≤ eta ^ (-(1 / 2 : ℝ)) *
      (4 / (Real.pi * eta) * Real.exp (-Real.pi * eta ^ 2 / 4)) := by
    simpa only [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num,
      ofReal_div, ofReal_one, ofReal_ofNat] using
      exterior_localHankel_one (1 / 2) (by linarith : 1 ≤ eta) hint
  have hj : ‖F * J‖ ≤ eta ^ (-(1 / 2 : ℝ)) * ((731 / 1000) / eta) := by
    rw [norm_mul, show ‖F‖ = eta ^ (-(1 / 2 : ℝ)) by
      simpa only [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num] using
        exterior_localPrefactor_norm (1 / 2) he0 ⌊eta⌋₊]
    exact mul_le_mul_of_nonneg_left (jn_floor_one_sharp he).2 (Real.rpow_nonneg he0.le _)
  change ‖H - F * P‖ ≤ _
  calc
    _ = ‖(H - F * (P + J)) + F * J‖ := by congr 1; ring
    _ ≤ ‖H - F * (P + J)‖ + ‖F * J‖ := norm_add_le _ _
    _ ≤ _ := (add_le_add ho hj).trans_eq (by ring)

theorem one_polynomial_outer_allocation {eta : ℝ} (he : 11 ≤ eta) :
    4 / (Real.pi * eta) * Real.exp (-Real.pi * eta ^ 2 / 4) ≤ (9 / 1000) / eta := by
  have he0 : 0 < eta := by linarith
  have hx : 50 ≤ Real.pi * eta ^ 2 / 4 := by
    have hs : 121 ≤ eta ^ 2 := by nlinarith
    nlinarith [Real.pi_gt_three]
  have hh := Real.quadratic_le_exp_of_nonneg (by linarith : 0 ≤ Real.pi * eta ^ 2 / 4)
  have hlo : 1000 ≤ Real.exp (Real.pi * eta ^ 2 / 4) := by nlinarith
  have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1000) hlo
  have hxexp : Real.exp (-Real.pi * eta ^ 2 / 4) ≤ 1 / 1000 := by
    rw [show -Real.pi * eta ^ 2 / 4 = -(Real.pi * eta ^ 2 / 4) by ring,
      Real.exp_neg, inv_eq_one_div]
    exact hi
  apply (mul_le_mul_of_nonneg_left hxexp (by positivity : 0 ≤ 4 / (Real.pi * eta))).trans
  field_simp
  nlinarith [Real.pi_gt_three]

theorem local_hankel_one_sharp_R0 {eta : ℝ}
    (he : 0 ≤ eta) (ht : 125 < eta ^ 2) (hint : ∀ k : ℤ, eta ≠ k) :
    ‖(∫ y : ℝ in (eta / 2)..(-eta / 2), rsDescentDirection *
      rsHankelKernel ((1 / 2 : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2)
        ⌊eta⌋₊ (rsDescentPoint eta y)) -
      rsLocalPrefactor (1 / 2) eta ⌊eta⌋₊ *
        (sourceGaussianPhase eta ⌊eta⌋₊ * (rsPhi (sourcePhiParameter eta ⌊eta⌋₊) : ℂ))‖ ≤
      eta ^ (-(1 / 2 : ℝ)) * ((37 / 50) / eta) := by
  have he11 : 11 ≤ eta := by nlinarith
  apply (local_hankel_one_sharp_error he11 hint).trans
  apply mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg he _)
  exact (add_le_add le_rfl (one_polynomial_outer_allocation he11)).trans_eq (by ring)

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
