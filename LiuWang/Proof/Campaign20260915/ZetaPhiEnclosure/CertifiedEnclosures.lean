import LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.PrecisionBounds
import LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.MomentConsumers

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory
open scoped Real

namespace LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure

open LiuWang.Proof.Campaign20260915.ZetaMordell
open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem precisePhi_radius_small {r d : ℚ} (hr : |r| ≤ 1) (hd : d ≤ (1 : ℚ) / 10 ^ 24) :
    (precisePhi r d).radius ≤ (1 : ℚ) / 10 ^ 20 := by
  have h := precisePhi_radius_bound (d := d) hr
  have hd' := mul_le_mul_of_nonneg_left hd (show (0 : ℚ) ≤ derivativeBudget 1 by positivity)
  apply (h.trans (add_le_add le_rfl hd')).trans
  decide +kernel

theorem certified_phi_errors (r d : ℚ) {z : ℝ}
    (hr : |r| ≤ 1) (hd : d ≤ (1 : ℚ) / 10 ^ 24)
    (hz : |z| ≤ 1) (hinput : |z - r| ≤ (d : ℝ)) :
    |rsPhi z - ((precisePhi r d).center : ℝ)| ≤ (1 : ℝ) / 10 ^ 20 ∧
    |rsPhiOne z - ((precisePhiOne r d).center : ℝ)| ≤ (1 : ℝ) / 10 ^ 9 ∧
    |rsPhiTwo z - ((precisePhiTwo r d).center : ℝ)| ≤ (1 : ℝ) / 10 ^ 6 := by
  have hrR : |(r : ℝ)| ≤ 1 := by exact_mod_cast hr
  have h0 := precisePhi_correct r d hrR hz hinput
  have h1 := precisePhiOne_correct r d hrR hz hinput
  have h2 := precisePhiTwo_correct r d hrR hz hinput
  have b0 : ((precisePhi r d).radius : ℝ) ≤ ((1 / 10 ^ 20 : ℚ) : ℝ) :=
    Rat.cast_le.mpr (precisePhi_radius_small hr hd)
  have b1 : ((precisePhiOne r d).radius : ℝ) ≤ ((1 / 10 ^ 9 : ℚ) : ℝ) :=
    Rat.cast_le.mpr (precisePhiOne_radius_small hr hd)
  have b2 : ((precisePhiTwo r d).radius : ℝ) ≤ ((1 / 10 ^ 6 : ℚ) : ℝ) :=
    Rat.cast_le.mpr (precisePhiTwo_radius_small hr hd)
  exact ⟨by simpa using h0.trans b0, by simpa using h1.trans b1, by simpa using h2.trans b2⟩

def rationalR2Center (r d : ℚ) (eta : ℝ) : ℂ :=
  ((precisePhi r d).center : ℂ) - ((precisePhiOne r d).center : ℂ) / eta +
    (((precisePhiTwo r d).center : ℂ) +
      I / (96 * Real.pi) * ((precisePhi r d).center : ℂ)) / (eta : ℂ) ^ 2

def r2EvaluationError (eta : ℝ) : ℝ :=
  1 / 10 ^ 20 + (1 / 10 ^ 9) / eta + (1 / 10 ^ 6 + (1 / 10 ^ 20) / 288) / eta ^ 2

theorem certified_r2_center_error (r d : ℚ) {eta z : ℝ}
    (he : 0 < eta) (hr : |r| ≤ 1) (hd : d ≤ (1 : ℚ) / 10 ^ 24)
    (hz : |z| ≤ 1) (hinput : |z - r| ≤ (d : ℝ)) :
    ‖((rsPhi z : ℂ) - (rsPhiOne z : ℂ) / eta +
        ((rsPhiTwo z : ℂ) + I / (96 * Real.pi) * (rsPhi z : ℂ)) / (eta : ℂ) ^ 2) -
      rationalR2Center r d eta‖ ≤ r2EvaluationError eta := by
  have h := certified_phi_errors r d hr hd hz hinput
  have h0 : ‖(rsPhi z : ℂ) - ((precisePhi r d).center : ℂ)‖ ≤ (1 : ℝ) / 10 ^ 20 := by
    simpa only [← Complex.ofReal_ratCast, ← Complex.ofReal_sub, norm_real, Real.norm_eq_abs] using h.1
  have h1 : ‖(rsPhiOne z : ℂ) - ((precisePhiOne r d).center : ℂ)‖ ≤ (1 : ℝ) / 10 ^ 9 := by
    simpa only [← Complex.ofReal_ratCast, ← Complex.ofReal_sub, norm_real, Real.norm_eq_abs] using h.2.1
  have h2 : ‖(rsPhiTwo z : ℂ) - ((precisePhiTwo r d).center : ℂ)‖ ≤ (1 : ℝ) / 10 ^ 6 := by
    simpa only [← Complex.ofReal_ratCast, ← Complex.ofReal_sub, norm_real, Real.norm_eq_abs] using h.2.2
  have hid : ((rsPhi z : ℂ) - (rsPhiOne z : ℂ) / eta +
        ((rsPhiTwo z : ℂ) + I / (96 * Real.pi) * (rsPhi z : ℂ)) / (eta : ℂ) ^ 2) -
      rationalR2Center r d eta =
      ((rsPhi z : ℂ) - ((precisePhi r d).center : ℂ)) -
        ((rsPhiOne z : ℂ) - ((precisePhiOne r d).center : ℂ)) / eta +
        (((rsPhiTwo z : ℂ) - ((precisePhiTwo r d).center : ℂ)) +
          I / (96 * Real.pi) * ((rsPhi z : ℂ) - ((precisePhi r d).center : ℂ))) / (eta : ℂ) ^ 2 := by
    unfold rationalR2Center
    ring
  rw [hid]
  unfold r2EvaluationError
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (norm_sub_le _ _).trans
    apply add_le_add h0
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos he]
    exact div_le_div_of_nonneg_right h1 he.le
  · rw [norm_div, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos he]
    apply div_le_div_of_nonneg_right _ (sq_nonneg eta)
    apply (norm_add_le _ _).trans
    apply add_le_add h2
    rw [norm_mul, norm_div, norm_mul, norm_I, norm_ofNat, norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have hpi : (1 : ℝ) / (96 * Real.pi) ≤ 1 / 288 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      nlinarith [Real.pi_gt_three]
    exact (mul_le_mul hpi h0 (norm_nonneg _) (by norm_num)).trans_eq (by ring)

theorem sourceLocalPolynomial_seven_certified (r d : ℚ) {eta : ℝ} {m : ℕ}
    (h0 : 0 < eta - m) (h1 : eta - m < 1)
    (hr : |r| ≤ 1) (hd : d ≤ (1 : ℚ) / 10 ^ 24)
    (hinput : |sourcePhiParameter eta m - r| ≤ (d : ℝ)) :
    ‖-(∫ y : ℝ, rsLocalPolynomialIntegrand (1 / 2) eta m 7 y) -
      sourceGaussianPhase eta m * rationalR2Center r d eta‖ ≤
      r2HighMomentBudget eta + r2EvaluationError eta := by
  have he : 0 < eta := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hhigh := sourceLocalPolynomial_seven_high_moment_error h0 h1
  have heval := certified_r2_center_error r d he hr hd (sourcePhiParameter_mem h0.le h1.le) hinput
  let A : ℂ := (rsPhi (sourcePhiParameter eta m) : ℂ) -
    (rsPhiOne (sourcePhiParameter eta m) : ℂ) / eta +
    ((rsPhiTwo (sourcePhiParameter eta m) : ℂ) +
      I / (96 * Real.pi) * (rsPhi (sourcePhiParameter eta m) : ℂ)) / (eta : ℂ) ^ 2
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (-(∫ y : ℝ, rsLocalPolynomialIntegrand (1 / 2) eta m 7 y))
    (sourceGaussianPhase eta m * A) (sourceGaussianPhase eta m * rationalR2Center r d eta)
  have hphase : ‖sourceGaussianPhase eta m * A -
      sourceGaussianPhase eta m * rationalR2Center r d eta‖ ≤ r2EvaluationError eta := by
    rw [← mul_sub, norm_mul, sourceGaussianPhase_norm, one_mul]
    exact heval
  exact ht.trans (add_le_add hhigh hphase)

end LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure
