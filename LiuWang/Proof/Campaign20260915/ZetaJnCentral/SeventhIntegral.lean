import LiuWang.Proof.Campaign20260915.ZetaJnCentral.NinthIntegral
import LiuWang.Proof.Campaign20260915.ZetaJnCentral.SeventhCoefficients

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem jn_seven_to_nine_pointwise (eta : ℝ) (m : ℕ) (y : ℝ) :
    rsJnIntegrand (1 / 2) eta m 7 y =
      rsJnIntegrand (1 / 2) eta m 9 y +
      scaledCoefficient eta 7 * gaussianMonomial eta m 6 y +
      scaledCoefficient eta 8 * gaussianMonomial eta m 7 y := by
  have hr (z : ℂ) : rsSaddleRemainder (1 / 2) (rsSaddleScale * eta) 7 z =
      rsSaddleRemainder (1 / 2) (rsSaddleScale * eta) 9 z +
        rsSaddleCoefficient (1 / 2) (rsSaddleScale * eta) 7 * z ^ 7 +
        rsSaddleCoefficient (1 / 2) (rsSaddleScale * eta) 8 * z ^ 8 := by
    unfold rsSaddleRemainder
    rw [Finset.sum_range_succ (n := 8), Finset.sum_range_succ (n := 7)]
    ring
  unfold rsJnIntegrand
  rw [hr]
  unfold gaussianMonomial scaledCoefficient
  simp only [mul_pow, Nat.reduceAdd]
  ring

theorem jn_seven_to_nine_integral {eta : ℝ} {m : ℕ}
    (he : 0 < eta) (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) :
    (∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta m 7 y) =
      (∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta m 9 y) +
      scaledCoefficient eta 7 * (∫ y : ℝ in (eta / 2)..(-eta / 2), gaussianMonomial eta m 6 y) +
      scaledCoefficient eta 8 * (∫ y : ℝ in (eta / 2)..(-eta / 2), gaussianMonomial eta m 7 y) := by
  have h9 := jn_local_integrable (1 / 2) he hm0 hm1 8
  have h7 : IntervalIntegrable (fun y => scaledCoefficient eta 7 * gaussianMonomial eta m 6 y)
      volume (eta / 2) (-eta / 2) :=
    ((gaussianMonomial_integrable eta m 6 hm0 hm1).intervalIntegrable).const_mul
      (scaledCoefficient eta 7)
  have h8 : IntervalIntegrable (fun y => scaledCoefficient eta 8 * gaussianMonomial eta m 7 y)
      volume (eta / 2) (-eta / 2) :=
    ((gaussianMonomial_integrable eta m 7 hm0 hm1).intervalIntegrable).const_mul
      (scaledCoefficient eta 8)
  rw [show rsJnIntegrand (1 / 2) eta m 7 =
    (fun y => rsJnIntegrand (1 / 2) eta m 9 y +
      scaledCoefficient eta 7 * gaussianMonomial eta m 6 y +
      scaledCoefficient eta 8 * gaussianMonomial eta m 7 y) from
        funext (jn_seven_to_nine_pointwise eta m)]
  rw [intervalIntegral.integral_add (h9.add h7) h8, intervalIntegral.integral_add h9 h7,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

def seventhJnConstant : ℝ :=
  ninthJnConstant (1 / 2) + 34 * gaussianMomentBudget 6 + 48 * gaussianMomentBudget 7

theorem jn_seven_source_order {eta : ℝ} {m : ℕ}
    (he : 2 ≤ eta) (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) :
    ‖∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta m 7 y‖ ≤
      seventhJnConstant / eta ^ 3 := by
  have he0 : 0 < eta := by linarith
  have hmono (N : ℕ) :
      ‖∫ y : ℝ in (eta / 2)..(-eta / 2), gaussianMonomial eta m N y‖ ≤ gaussianMomentBudget N := by
    rw [intervalIntegral.integral_symm (-eta / 2) (eta / 2), norm_neg]
    exact gaussianMonomial_interval eta m N hm0 hm1 (by linarith)
  have h7 : ‖scaledCoefficient eta 7 *
      (∫ y : ℝ in (eta / 2)..(-eta / 2), gaussianMonomial eta m 6 y)‖ ≤
      (34 / eta ^ 3) * gaussianMomentBudget 6 := by
    rw [norm_mul]
    exact mul_le_mul (scaled_seven_bound (by linarith)) (hmono 6) (norm_nonneg _) (by positivity)
  have h8 : ‖scaledCoefficient eta 8 *
      (∫ y : ℝ in (eta / 2)..(-eta / 2), gaussianMonomial eta m 7 y)‖ ≤
      (48 / eta ^ 3) * gaussianMomentBudget 7 := by
    rw [norm_mul]
    exact mul_le_mul (scaled_eight_bound (by linarith)) (hmono 7) (norm_nonneg _) (by positivity)
  have h9 := jn_nine_source_order (1 / 2) he hm0 hm1
  rw [jn_seven_to_nine_integral he0 hm0 hm1]
  apply norm_add₃_le.trans
  exact (add_le_add (add_le_add h9 h7) h8).trans_eq (by unfold seventhJnConstant; ring)

theorem jn_floor_seven_source_order {eta : ℝ} (he : 2 ≤ eta) :
    IntervalIntegrable (rsJnIntegrand (1 / 2) eta ⌊eta⌋₊ 7)
      volume (eta / 2) (-eta / 2) ∧
    ‖∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta ⌊eta⌋₊ 7 y‖ ≤
      seventhJnConstant / eta ^ 3 := by
  have he0 : 0 < eta := by linarith
  have h0 := Nat.zero_le_self_sub_floor he0.le
  have h1 := (Nat.self_sub_floor_lt_one eta).le
  exact ⟨jn_local_integrable (1 / 2) he0 h0 h1 6, jn_seven_source_order he h0 h1⟩

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
