import LiuWang.Proof.Campaign20260915.ZetaJnCentral.SmallCircleTaylor
import LiuWang.Proof.Campaign20260915.ZetaJnCentral.RationalMoments
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation

def twelfthRadius (eta : ℝ) : ℝ := (2 * eta) ^ (1 / 3 : ℝ)
def twelfthCutoff (eta : ℝ) : ℝ := 3 / 4 * twelfthRadius eta

theorem twelfthRadius_pos {eta : ℝ} (he : 0 < eta) : 0 < twelfthRadius eta :=
  Real.rpow_pos_of_pos (by positivity) _

theorem twelfthRadius_cube {eta : ℝ} (he : 0 < eta) : twelfthRadius eta ^ 3 = 2 * eta := by
  unfold twelfthRadius
  rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ 2 * eta)]
  norm_num

theorem twelfthRadius_data {eta : ℝ} (he : 44 ≤ eta) :
    twelfthRadius eta ≤ eta / 8 ∧
    10 / 3 ≤ twelfthCutoff eta ∧ twelfthCutoff eta ≤ eta / 2 ∧
    twelfthCutoff eta ^ 3 = 27 / 32 * eta := by
  have he0 : 0 < eta := by linarith
  have hR := twelfthRadius_pos he0
  have hu : twelfthRadius eta ≤ eta / 8 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) (by positivity)
    rw [twelfthRadius_cube he0]
    have hs : 1024 ≤ eta ^ 2 := by nlinarith
    have hc := mul_le_mul_of_nonneg_right hs he0.le
    nlinarith
  have hl : 40 / 9 ≤ twelfthRadius eta := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) hR.le
    rw [twelfthRadius_cube he0]
    norm_num
    linarith
  refine ⟨hu, ?_, ?_, ?_⟩
  · unfold twelfthCutoff
    linarith
  · unfold twelfthCutoff
    linarith
  · rw [twelfthCutoff, mul_pow, twelfthRadius_cube he0]
    ring

theorem exp_five_le_150 : Real.exp 5 ≤ 150 := by
  have he : Real.exp 1 ≤ 68 / 25 := by linarith [Real.exp_one_lt_d9]
  calc
    _ = Real.exp 1 ^ 5 := by simpa only [Nat.cast_ofNat, mul_one] using Real.exp_nat_mul 1 5
    _ ≤ (68 / 25 : ℝ) ^ 5 := pow_le_pow_left₀ (Real.exp_pos _).le he _
    _ ≤ _ := by norm_num

theorem twelfthRadius_majorant {eta : ℝ} (he : 0 < eta) :
    smallCircleMajorant (1 / 2) (rsSaddleScale * eta) (rsSaddleScale * twelfthRadius eta) ≤ 150 := by
  have hs := rsSaddleScale_pos.ne'
  have hpow : (rsSaddleScale * eta) ^ 2 *
      ((rsSaddleScale * twelfthRadius eta) / (rsSaddleScale * eta)) ^ 3 = 4 * Real.pi := by
    rw [mul_div_mul_left _ _ hs, div_pow, mul_pow, twelfthRadius_cube he, rsSaddleScale_sq]
    field_simp
    norm_num
  unfold smallCircleMajorant
  rw [show 8 / 21 * (rsSaddleScale * eta) ^ 2 *
      ((rsSaddleScale * twelfthRadius eta) / (rsSaddleScale * eta)) ^ 3 =
        8 / 21 * ((rsSaddleScale * eta) ^ 2 *
          ((rsSaddleScale * twelfthRadius eta) / (rsSaddleScale * eta)) ^ 3) by ring, hpow]
  apply (Real.exp_le_exp.mpr ?_).trans exp_five_le_150
  norm_num only [show |(1 / 2 : ℝ) - 1| = 1 / 2 by norm_num]
  linarith [Real.pi_lt_d2]

theorem twelfthRadius_twelfth {eta : ℝ} (he : 0 < eta) :
    twelfthRadius eta ^ 12 = 16 * eta ^ 4 := by
  rw [show (12 : ℕ) = 3 * 4 by norm_num, pow_mul, twelfthRadius_cube he, mul_pow]
  norm_num

theorem jn_twelfth_central {eta : ℝ} {m : ℕ} (he : 44 ≤ eta)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) :
    ‖∫ y : ℝ in (-twelfthCutoff eta)..(twelfthCutoff eta),
        rsJnIntegrand (1 / 2) eta m 12 y‖ ≤ (15 / 2) / eta ^ 4 := by
  have he0 : 0 < eta := by linarith
  have hR0 := twelfthRadius_pos he0
  have hs := rsSaddleScale_pos
  have hdata := twelfthRadius_data he
  have h := jn_smallCircle_integral (1 / 2) he0 (mul_pos hs hR0)
    (R := rsSaddleScale * twelfthRadius eta) (d := twelfthCutoff eta)
    (by nlinarith [mul_le_mul_of_nonneg_left hdata.1 hs.le])
    (by linarith [hdata.2.1])
    (by unfold twelfthCutoff; ring_nf; exact le_rfl) hm0 hm1 11
  simp only [Nat.reduceAdd] at h
  have hratio : (rsSaddleScale / (rsSaddleScale * twelfthRadius eta)) ^ 12 =
      1 / (16 * eta ^ 4) := by
    rw [div_mul_cancel_left₀ hs.ne', inv_pow, twelfthRadius_twelfth he0, one_div]
  rw [hratio] at h
  apply h.trans
  have hm := twelfthRadius_majorant he0
  have hq := mul_le_mul
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 4))
      (by positivity : (0 : ℝ) ≤ 1 / (16 * eta ^ 4)))
    exactGaussianBudget_eleven
    (by
      unfold exactGaussianBudget
      exact add_nonneg (gaussianAbsoluteMoment_nonneg Real.pi_pos 12)
        (div_nonneg (gaussianAbsoluteMoment_nonneg Real.pi_pos 11) (by positivity)))
    (by positivity : (0 : ℝ) ≤ 4 * 150 * (1 / (16 * eta ^ 4)))
  exact hq.trans_eq (by ring)

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
