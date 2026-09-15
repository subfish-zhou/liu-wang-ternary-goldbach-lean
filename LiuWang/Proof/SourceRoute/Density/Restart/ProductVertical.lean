import LiuWang.Proof.SourceRoute.Density.Restart.ProductContour
import LiuWang.Proof.SourceRoute.Density.Restart.ProductRight

/-! The source's two signed vertical estimates, with the full-family mean unchanged. -/

set_option autoImplicit false

noncomputable section

open Complex Set Finset MeasureTheory
open LiuWang.Proof.Interfaces (Character)
open LiuWang.Proof.NonprincipalDensityAdvance
open LiuWang.Proof.NonprincipalDensityMeans
open LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.PVContinuation

namespace LiuWang.Proof.SourceRoute.Density.Restart

def familyMean (q : ℕ) [NeZero q] (X sigma U : ℝ) : ℝ :=
  ∫ t in -U..U, familySquare q X ((sigma : ℂ) + t * I)

theorem familyMean_eq_phi_Fmean (q : ℕ) [NeZero q] (X sigma U : ℝ) :
    familyMean q X sigma U = (q.totient : ℝ) * Fmean q X sigma U := by
  have hp : (q.totient : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q)))
  unfold familyMean familySquare Fmean
  rw [mul_div_cancel₀ _ hp]
  exact intervalIntegral.integral_finsetSum (fun chi hc =>
    f_vertical_integrable ((mem_nonprincipalCharacters chi).mp hc) X sigma U)

theorem familyMean_nonneg (q : ℕ) [NeZero q] (X sigma : ℝ) {U : ℝ} (hU : 0 ≤ U) :
    0 ≤ familyMean q X sigma U := by
  rw [familyMean_eq_phi_Fmean]
  exact mul_nonneg (Nat.cast_nonneg _) (Fmean_nonneg q X sigma hU)

theorem neg_log_norm_one_sub_sq_le_three_halves {z : ℂ} (hz : ‖z‖ ^ 2 ≤ 1 / 3) :
    -Real.log ‖1 - z ^ 2‖ ≤ 3 / 2 * ‖z‖ ^ 2 := by
  have hlo : 1 - ‖z‖ ^ 2 ≤ ‖1 - z ^ 2‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (z ^ (2 : ℕ))
    simpa only [norm_one, norm_pow] using h
  have hpos : 0 < ‖1 - z ^ 2‖ := by linarith
  have hinv : ‖1 - z ^ 2‖⁻¹ ≤ 1 + 3 / 2 * ‖z‖ ^ 2 := by
    rw [← one_div]
    apply (div_le_iff₀ hpos).mpr
    have hm := mul_le_mul_of_nonneg_right hlo (by positivity : 0 ≤ 1 + 3 / 2 * ‖z‖ ^ 2)
    have hq := mul_nonneg (sq_nonneg ‖z‖) (show 0 ≤ 1 - 3 * ‖z‖ ^ 2 by linarith)
    nlinarith
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  linarith

theorem neg_log_H_two_source {q : ℕ} [NeZero q] (chi : Character q) {X : ℝ}
    (hX : 5 ≤ X) {s : ℂ} (hs : s.re = 2) :
    -Real.log ‖H chi X s‖ ≤ 3 / 2 * ‖f chi X s‖ ^ 2 := by
  apply neg_log_norm_one_sub_sq_le_three_halves
  have h := pow_le_pow_left₀ (norm_nonneg _)
    (norm_f_two_le chi (X := X) hs (by linarith)) 2
  have hq : (2 / (X - 1)) ^ 2 ≤ 1 / 3 := by
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < X - 1))).mpr
    nlinarith
  exact h.trans hq

theorem product_log_le_familySquare (q : ℕ) [NeZero q] (X : ℝ) (s : ℂ) :
    Real.log ‖familyProduct q X s‖ ≤ familySquare q X s := by
  by_cases hz : familyProduct q X s = 0
  · simpa only [hz, norm_zero, Real.log_zero] using familySquare_nonneg q X s
  exact (Real.log_le_log (norm_pos_iff.mpr hz) (norm_familyProduct_le_exp q X s)).trans_eq
    (Real.log_exp _)

theorem product_neg_log_two (q : ℕ) [NeZero q] {X : ℝ}
    (hX : 5 ≤ X) {s : ℂ} (hs : s.re = 2) :
    -Real.log ‖familyProduct q X s‖ ≤ 3 / 2 * familySquare q X s := by
  rw [product_log_norm q X (fun chi _ => H_ne_zero_on_two chi hs (by linarith)),
    ← sum_neg_distrib, familySquare, mul_sum]
  exact sum_le_sum (fun chi _ => neg_log_H_two_source chi hX hs)

theorem product_log_vertical_integrable (q : ℕ) [NeZero q] (X sigma U : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.log ‖familyProduct q X ((sigma : ℂ) + t * I)‖)
      volume (-U) U := by
  apply MeromorphicOn.intervalIntegrable_log_norm
  apply AnalyticOnNhd.meromorphicOn
  intro t _
  have h := ((familyProduct_differentiable q X).analyticAt ((sigma : ℂ) + t * I)).restrictScalars
    (𝕜 := ℝ)
  have ha : AnalyticAt ℝ (fun r : ℝ => (sigma : ℂ) + r * I) t :=
    analyticAt_const.add ((Complex.ofRealCLM.analyticAt t).mul analyticAt_const)
  exact AnalyticAt.comp (f := fun r : ℝ => (sigma : ℂ) + r * I) h ha

theorem familySquare_vertical_integrable (q : ℕ) [NeZero q] (X sigma U : ℝ) :
    IntervalIntegrable (fun t : ℝ => familySquare q X ((sigma : ℂ) + t * I)) volume (-U) U :=
  ((familySquare_continuous q X).comp
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))).intervalIntegrable _ _

theorem product_left_integral (q : ℕ) [NeZero q] (X a : ℝ) {U : ℝ} (hU : 0 ≤ U) :
    (∫ t in -U..U, Real.log ‖familyProduct q X ((a : ℂ) + t * I)‖) ≤ familyMean q X a U :=
  intervalIntegral.integral_mono_on (by linarith) (product_log_vertical_integrable q X a U)
    (familySquare_vertical_integrable q X a U) (fun t _ => product_log_le_familySquare q X _)

theorem product_right_integral (q : ℕ) [NeZero q] {X U : ℝ} (hX : 5 ≤ X) (hU : 0 ≤ U) :
    -(∫ t in -U..U, Real.log ‖familyProduct q X ((2 : ℂ) + t * I)‖) ≤
      3 / 2 * familyMean q X 2 U := by
  have hi := (product_log_vertical_integrable q X 2 U).neg
  have h := intervalIntegral.integral_mono_on (by linarith : -U ≤ U) hi
    ((familySquare_vertical_integrable q X 2 U).const_mul (3 / 2))
    (fun t _ => product_neg_log_two q hX (by simp))
  simpa only [Pi.neg_apply, intervalIntegral.integral_neg, intervalIntegral.integral_const_mul, familyMean,
    ofReal_ofNat] using h

theorem product_vertical_source (q : ℕ) [NeZero q] {X U : ℝ} (hX : 5 ≤ X) (hU : 0 ≤ U)
    {a : ℝ} (hb : ∀ chi ∈ nonprincipalCharacters q,
      ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), H chi X s ≠ 0) :
    (q.totient : ℝ) * logSideDifference q X a U ≤
      familyMean q X a U + 3 / 2 * familyMean q X 2 U := by
  rw [← product_vertical_difference q X hb, sub_eq_add_neg]
  exact add_le_add (product_left_integral q X a hU) (product_right_integral q hX hU)

theorem familyMean_two_le (q : ℕ) [NeZero q] {X U : ℝ} (hX : 1 < X) (hU : 0 ≤ U) :
    familyMean q X 2 U ≤ 2 * U * (q.totient - 1 : ℕ) * (4 / (X - 1) ^ 2) := by
  have h := intervalIntegral.integral_mono_on (by linarith : -U ≤ U)
    (familySquare_vertical_integrable q X 2 U) intervalIntegrable_const
    (fun t _ => familySquare_two_le q hX (s := ((2 : ℝ) : ℂ) + t * I) (by simp))
  rw [intervalIntegral.integral_const] at h
  exact h.trans_eq (by simp only [smul_eq_mul]; ring)

end LiuWang.Proof.SourceRoute.Density.Restart
