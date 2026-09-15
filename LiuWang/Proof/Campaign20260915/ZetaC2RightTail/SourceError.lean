import LiuWang.Proof.Campaign20260915.ZetaC2RightTail.Prefactor

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory
open scoped Real

namespace LiuWang.Proof.Campaign20260915.ZetaC2RightTail
open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem rightTailDenom_half {eta : ℝ} (he : 1 ≤ eta) :
    1 / 2 ≤ rightTailDenom eta := by
  have hs : 1 ≤ Real.sqrt 2 := by
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith [Real.sqrt_nonneg 2]
  have hp : 2 ≤ Real.sqrt 2 * Real.pi := by
    have := mul_le_mul_of_nonneg_right hs Real.pi_pos.le
    nlinarith [Real.two_le_pi]
  have ht : 1 ≤ Real.sqrt 2 * Real.pi * (eta / 2) := by
    have := mul_le_mul_of_nonneg_left he (show 0 ≤ Real.sqrt 2 * Real.pi by positivity)
    nlinarith
  have hx : 2 ≤ Real.exp (Real.sqrt 2 * Real.pi * (eta / 2)) := by
    linarith [Real.add_one_le_exp (Real.sqrt 2 * Real.pi * (eta / 2))]
  have hi : 1 / Real.exp (Real.sqrt 2 * Real.pi * (eta / 2)) ≤ 1 / 2 := by
    rw [div_le_iff₀ (Real.exp_pos _)]
    linarith
  rw [rightTailDenom, neg_mul, Real.exp_neg, inv_eq_one_div]
  linarith

theorem rightTailBudget_effective (sigma : ℝ) {eta : ℝ} (he : 1 ≤ eta) :
    rightTailBudget sigma eta ≤
      11 / (2 * Real.pi) * eta ^ (sigma - 2) *
        Real.exp (-((rsSaddleScale * eta) ^ 2) / 11) := by
  have he0 : 0 < eta := by linarith
  have hr := rightTailRate_pos he0
  have hden := mul_le_mul_of_nonneg_right (rightTailDenom_half he) hr.le
  have h := div_le_div_of_nonneg_left (Real.rpow_nonneg he0.le (sigma - 1))
    (show 0 < 1 / 2 * rightTailRate eta by positivity) hden
  unfold rightTailBudget
  apply mul_le_mul_of_nonneg_right (h.trans_eq ?_) (Real.exp_pos _).le
  have hp : eta ^ (sigma - 2) = eta ^ (sigma - 1) / eta := by
    rw [show sigma - 2 = (sigma - 1) - 1 by ring, Real.rpow_sub he0, Real.rpow_one]
  rw [hp, rightTailRate]
  ring

theorem critical_prefactored_right_tail_effective {eta : ℝ} {m : ℕ}
    (he : 1 ≤ eta) (hm : eta ≤ (m : ℝ) + 1) :
    ‖rsHankelPrefactor ((1 / 2 : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) *
      (∫ y : ℝ in Ioi (eta / 2), rsC2RightIntegrand
        ((1 / 2 : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) eta m y)‖ ≤
      11 / (2 * Real.pi) * eta ^ (-(3 / 2 : ℝ)) *
        Real.exp (-((rsSaddleScale * eta) ^ 2) / 11) := by
  have hb := (critical_prefactored_right_tail (by linarith : 0 < eta) hm).trans
    (rightTailBudget_effective (1 / 2) he)
  norm_num only [show (1 / 2 : ℝ) - 2 = -(3 / 2 : ℝ) by norm_num] at hb
  exact hb

theorem critical_sourceC2_truncation_right_error {eta : ℝ} {m : ℕ} (N : ℕ)
    (hm0 : 0 < m) (he : 0 < eta) (hint : ∀ n : ℤ, eta ≠ n)
    (hm : eta ≤ (m : ℝ) + 1) :
    ‖rsHankelPrefactor ((1 / 2 : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) *
      (rsSourceC2 ((1 / 2 : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) eta m -
        (rsLocalPrefactor (1 / 2) eta m *
          ((∫ y : ℝ in (eta / 2)..(-eta / 2),
              rsLocalPolynomialIntegrand (1 / 2) eta m N y) +
            ∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta m N y) +
          ∫ r : ℝ in Ioi 0, rsC2LeftIntegrand
            ((1 / 2 : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) eta m r))‖ ≤
      rightTailBudget (1 / 2) eta := by
  have hsplit := rsSourceC2_local_truncation (1 / 2) N hm0 (by norm_num) he hint
  norm_num only [ofReal_div, ofReal_one, ofReal_ofNat] at hsplit
  rw [hsplit, sub_sub_cancel_left, mul_neg, norm_neg]
  exact critical_prefactored_right_tail he hm

theorem critical_sourceC2_floor_right_error {eta : ℝ} (N : ℕ)
    (he : 1 ≤ eta) (hint : ∀ n : ℤ, eta ≠ n) :
    ‖rsHankelPrefactor ((1 / 2 : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) *
      (rsSourceC2 ((1 / 2 : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) eta ⌊eta⌋₊ -
        (rsLocalPrefactor (1 / 2) eta ⌊eta⌋₊ *
          ((∫ y : ℝ in (eta / 2)..(-eta / 2),
              rsLocalPolynomialIntegrand (1 / 2) eta ⌊eta⌋₊ N y) +
            ∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta ⌊eta⌋₊ N y) +
          ∫ r : ℝ in Ioi 0, rsC2LeftIntegrand
            ((1 / 2 : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) eta ⌊eta⌋₊ r))‖ ≤
      11 / (2 * Real.pi) * eta ^ (-(3 / 2 : ℝ)) *
        Real.exp (-((rsSaddleScale * eta) ^ 2) / 11) := by
  have h := (critical_sourceC2_truncation_right_error N (Nat.floor_pos.mpr he)
    (by linarith) hint (Nat.lt_floor_add_one eta).le).trans
      (rightTailBudget_effective (1 / 2) he)
  norm_num only [show (1 / 2 : ℝ) - 2 = -(3 / 2 : ℝ) by norm_num] at h
  exact h

#print axioms right_integrand_bound
#print axioms right_tail_integrable
#print axioms right_tail_bound
#print axioms critical_prefactor_norm_sq
#print axioms critical_prefactored_right_tail_effective
#print axioms sourceC2_truncation_right_error
#print axioms critical_sourceC2_floor_right_error

end LiuWang.Proof.Campaign20260915.ZetaC2RightTail
