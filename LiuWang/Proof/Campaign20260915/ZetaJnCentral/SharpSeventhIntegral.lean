import LiuWang.Proof.Campaign20260915.ZetaJnCentral.SharpCoefficients
import LiuWang.Proof.Campaign20260915.ZetaJnCentral.TwelfthBudget

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem jn_successor_split (eta : ℝ) (m N : ℕ) (y : ℝ) :
    rsJnIntegrand (1 / 2) eta m (N + 1) y =
      rsJnIntegrand (1 / 2) eta m (N + 2) y +
        scaledCoefficient eta (N + 1) * gaussianMonomial eta m N y := by
  have hr (z : ℂ) :
      rsSaddleRemainder (1 / 2) (rsSaddleScale * eta) (N + 1) z =
        rsSaddleRemainder (1 / 2) (rsSaddleScale * eta) (N + 2) z +
          rsSaddleCoefficient (1 / 2) (rsSaddleScale * eta) (N + 1) * z ^ (N + 1) := by
    unfold rsSaddleRemainder
    rw [Finset.sum_range_succ (n := N + 1)]
    ring
  rw [rsJnIntegrand, hr]
  unfold rsJnIntegrand scaledCoefficient gaussianMonomial
  rw [mul_pow]
  ring

theorem jn_successor_integral {eta : ℝ} {m : ℕ}
    (he : 0 < eta) (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) (N : ℕ) :
    (∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta m (N + 1) y) =
      (∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta m (N + 2) y) +
        scaledCoefficient eta (N + 1) *
          (∫ y : ℝ in (eta / 2)..(-eta / 2), gaussianMonomial eta m N y) := by
  have hj := jn_local_integrable (1 / 2) he hm0 hm1 (N + 1)
  have hm : IntervalIntegrable
      (fun y => scaledCoefficient eta (N + 1) * gaussianMonomial eta m N y)
      volume (eta / 2) (-eta / 2) :=
    ((gaussianMonomial_integrable eta m N hm0 hm1).intervalIntegrable).const_mul _
  simp_rw [jn_successor_split eta m N]
  rw [intervalIntegral.integral_add hj hm, intervalIntegral.integral_const_mul]

theorem jn_finite_remainder_split {eta : ℝ} {m : ℕ}
    (he : 0 < eta) (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) (N K : ℕ) :
    (∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta m (N + 1) y) =
      (∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta m (N + K + 1) y) +
        ∑ j ∈ Finset.range K, scaledCoefficient eta (N + j + 1) *
          (∫ y : ℝ in (eta / 2)..(-eta / 2), gaussianMonomial eta m (N + j) y) := by
  induction K with
  | zero => simp
  | succ K ih =>
    calc
      _ = (∫ y : ℝ in (eta / 2)..(-eta / 2),
          rsJnIntegrand (1 / 2) eta m (N + K + 1) y) +
          ∑ j ∈ Finset.range K, scaledCoefficient eta (N + j + 1) *
            (∫ y : ℝ in (eta / 2)..(-eta / 2), gaussianMonomial eta m (N + j) y) := ih
      _ = _ := by
        rw [jn_successor_integral he hm0 hm1 (N + K), Finset.sum_range_succ]
        simp only [Nat.add_assoc, Nat.reduceAdd]
        ring

theorem weighted_coefficient_drop {eta C : ℝ} (he : 44 ≤ eta) (n lo hi : ℕ)
    (h : ‖(eta : ℂ) ^ (lo + hi) * scaledCoefficient eta n‖ ≤ C) :
    ‖(eta : ℂ) ^ lo * scaledCoefficient eta n‖ ≤ C / (44 : ℝ) ^ hi := by
  have he0 : 0 < eta := by linarith
  have heC := ofReal_ne_zero.mpr he0.ne'
  have hid : (eta : ℂ) ^ lo * scaledCoefficient eta n =
      ((eta : ℂ) ^ (lo + hi) * scaledCoefficient eta n) / (eta : ℂ) ^ hi := by
    rw [pow_add]
    field_simp
  rw [hid]
  exact (norm_div_eta_pow he _ hi).trans (div_le_div_of_nonneg_right h (by positivity))

theorem gaussianMonomial_scaled_interval {eta C : ℝ} {m : ℕ} (he : 0 < eta)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) (N : ℕ)
    (h : ‖(eta : ℂ) ^ 3 * scaledCoefficient eta (N + 1)‖ ≤ C) :
    ‖scaledCoefficient eta (N + 1) *
      (∫ y : ℝ in (eta / 2)..(-eta / 2), gaussianMonomial eta m N y)‖ ≤
        C * exactGaussianBudget Real.pi N / eta ^ 3 := by
  have hC : 0 ≤ C := (norm_nonneg _).trans h
  rw [norm_mul, intervalIntegral.integral_symm (-eta / 2) (eta / 2), norm_neg]
  exact (mul_le_mul (scaled_weighted_to_norm he (N + 1) 3 h)
    (gaussianMonomial_exact_interval eta m N hm0 hm1 (by linarith))
    (norm_nonneg _) (div_nonneg hC (by positivity))).trans_eq (by ring)

theorem jn_seven_correction_budget {eta : ℝ} {m : ℕ} (he : 44 ≤ eta)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) :
    ‖∑ j ∈ Finset.range 5, scaledCoefficient eta (6 + j + 1) *
      (∫ y : ℝ in (eta / 2)..(-eta / 2), gaussianMonomial eta m (6 + j) y)‖ ≤
        (51 / 100) / eta ^ 3 := by
  have he0 : 0 < eta := by linarith
  have h7 := gaussianMonomial_scaled_interval he0 hm0 hm1 6 (sharp_scaled_seven he)
  have h8 := gaussianMonomial_scaled_interval he0 hm0 hm1 7
    (weighted_coefficient_drop he 8 3 1 (sharp_scaled_eight he))
  have h9 := gaussianMonomial_scaled_interval he0 hm0 hm1 8 (sharp_scaled_nine he)
  have h10 := gaussianMonomial_scaled_interval he0 hm0 hm1 9
    (weighted_coefficient_drop he 10 3 1 (sharp_scaled_ten he))
  have h11 := gaussianMonomial_scaled_interval he0 hm0 hm1 10
    (weighted_coefficient_drop he 11 3 2 (sharp_scaled_eleven he))
  apply (norm_sum_le _ _).trans
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, zero_add]
  have hh := add_le_add (add_le_add (add_le_add (add_le_add h7 h8) h9) h10) h11
  simp only [Nat.reduceAdd, pow_one] at hh
  apply hh.trans
  have h := div_le_div_of_nonneg_right exactGaussian_seven_corrections
    (by positivity : 0 ≤ eta ^ 3)
  convert h using 1
  ring

theorem jn_seven_sharp {eta : ℝ} {m : ℕ} (he : 44 ≤ eta)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) :
    ‖∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta m 7 y‖ ≤
      (51 / 50) / eta ^ 3 := by
  have he0 : 0 < eta := by linarith
  have hs := jn_finite_remainder_split he0 hm0 hm1 6 5
  norm_num only [Nat.reduceAdd] at hs
  rw [hs]
  apply (norm_add_le _ _).trans
  exact (add_le_add (jn_twelfth_source_budget he hm0 hm1)
    (jn_seven_correction_budget he hm0 hm1)).trans_eq (by ring)

theorem jn_floor_seven_sharp {eta : ℝ} (he : 44 ≤ eta) :
    IntervalIntegrable (rsJnIntegrand (1 / 2) eta ⌊eta⌋₊ 7) volume (eta / 2) (-eta / 2) ∧
    ‖∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta ⌊eta⌋₊ 7 y‖ ≤
      (51 / 50) / eta ^ 3 := by
  have he0 : 0 < eta := by linarith
  have h0 := Nat.zero_le_self_sub_floor he0.le
  have h1 := (Nat.self_sub_floor_lt_one eta).le
  exact ⟨jn_local_integrable (1 / 2) he0 h0 h1 6, jn_seven_sharp he h0 h1⟩

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
