import LiuWang.Proof.Campaign20260915.ZetaC2RightTail.Pointwise

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory
open scoped Real

namespace LiuWang.Proof.Campaign20260915.ZetaC2RightTail
open LiuWang.Proof.Campaign20260915.ZetaValidation

def rightTailBudget (sigma eta : ℝ) : ℝ :=
  eta ^ (sigma - 1) / (rightTailDenom eta * rightTailRate eta) *
    Real.exp (-((rsSaddleScale * eta) ^ 2) / 11)

theorem right_integrand_continuousOn (s : ℂ) {eta : ℝ} (he : 0 < eta) (m : ℕ) :
    ContinuousOn (rsC2RightIntegrand s eta m) (Ioi (eta / 2)) := by
  intro y hy
  have hy' : eta / 2 ≤ y := hy.le
  have hr : 0 < (rsDescentPoint eta y).re := by
    rw [(right_coordinates eta y).1]
    have : 0 < y := by linarith [hy]
    positivity
  have hd : rsHankelDenominator (rsDescentPoint eta y) ≠ 0 := by
    apply norm_pos_iff.mp
    exact lt_of_lt_of_le
      (mul_pos (rightTailDenom_pos he) (Real.exp_pos _)) (right_denominator_bound hy')
  have ha := (rsHankelNumerator_analytic s m hr.ne').div
    (rsHankelDenominator_analytic _) hd
  have hc : ContinuousAt (fun y : ℝ => rsHankelKernel s m (rsDescentPoint eta y)) y :=
    ha.continuousAt.comp (show ContinuousAt (rsDescentPoint eta) y by
      unfold rsDescentPoint
      fun_prop)
  exact (continuousAt_const.mul hc).continuousWithinAt

theorem right_majorant_integrable (sigma : ℝ) {eta : ℝ} (he : 0 < eta) :
    IntegrableOn (fun y : ℝ =>
      eta ^ (sigma - 1) / rightTailDenom eta * Real.exp (-rightTailRate eta * y))
      (Ioi (eta / 2)) :=
  (integrableOn_exp_mul_Ioi (neg_neg_of_pos (rightTailRate_pos he)) _).const_mul _

theorem right_tail_integrable {sigma eta : ℝ} {m : ℕ}
    (hsigma : sigma ≤ 1) (he : 0 < eta) (hm : eta ≤ (m : ℝ) + 1) :
    IntegrableOn (rsC2RightIntegrand
      ((sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) eta m)
      (Ioi (eta / 2)) := by
  apply (right_majorant_integrable sigma he).mono'
    ((right_integrand_continuousOn _ he m).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact right_integrand_bound hsigma he hy.le hm

theorem right_tail_bound {sigma eta : ℝ} {m : ℕ}
    (hsigma : sigma ≤ 1) (he : 0 < eta) (hm : eta ≤ (m : ℝ) + 1) :
    ‖∫ y : ℝ in Ioi (eta / 2), rsC2RightIntegrand
      ((sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) eta m y‖ ≤
      rightTailBudget sigma eta := by
  have h := norm_integral_le_of_norm_le (right_majorant_integrable sigma he)
    (f := rsC2RightIntegrand
      ((sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) eta m) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
        exact right_integrand_bound hsigma he hy.le hm)
  rw [integral_const_mul, integral_exp_mul_Ioi
    (neg_neg_of_pos (rightTailRate_pos he))] at h
  apply h.trans_eq
  have hexp : -rightTailRate eta * (eta / 2) = -((rsSaddleScale * eta) ^ 2) / 11 := by
    rw [mul_pow, rsSaddleScale_sq, rightTailRate]
    ring
  rw [hexp, rightTailBudget]
  ring

theorem right_tail_bound_floor {sigma eta : ℝ}
    (hsigma : sigma ≤ 1) (he : 0 < eta) :
    ‖∫ y : ℝ in Ioi (eta / 2), rsC2RightIntegrand
      ((sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) eta ⌊eta⌋₊ y‖ ≤
      rightTailBudget sigma eta :=
  right_tail_bound hsigma he (Nat.lt_floor_add_one eta).le

theorem sourceC2_truncation_right_error (sigma : ℝ) {eta : ℝ} {m : ℕ} (N : ℕ)
    (hm0 : 0 < m) (hsigma : sigma ≤ 1) (he : 0 < eta)
    (hint : ∀ n : ℤ, eta ≠ n) (hm : eta ≤ (m : ℝ) + 1) :
    ‖rsSourceC2 ((sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) eta m -
      (rsLocalPrefactor sigma eta m *
        ((∫ y : ℝ in (eta / 2)..(-eta / 2), rsLocalPolynomialIntegrand sigma eta m N y) +
          ∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand sigma eta m N y) +
        ∫ r : ℝ in Ioi 0, rsC2LeftIntegrand
          ((sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) eta m r)‖ ≤
      rightTailBudget sigma eta := by
  rw [rsSourceC2_local_truncation sigma N hm0 hsigma he hint,
    sub_sub_cancel_left, norm_neg]
  exact right_tail_bound hsigma he hm

end LiuWang.Proof.Campaign20260915.ZetaC2RightTail
