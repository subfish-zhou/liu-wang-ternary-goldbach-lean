import LiuWang.Proof.Campaign20260915.ZetaJnCentral.GaussianMoments

set_option autoImplicit false
noncomputable section
open Complex

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation

def ninthRadius (eta : ℝ) : ℝ := (rsSaddleScale * eta) ^ (1 / 3 : ℝ)

def ninthCutoff (eta : ℝ) : ℝ := 20 / 21 * ninthRadius eta / rsSaddleScale

theorem ninthRadius_pos {eta : ℝ} (he : 0 < eta) : 0 < ninthRadius eta := by
  exact Real.rpow_pos_of_pos (mul_pos rsSaddleScale_pos he) _

theorem ninthRadius_cube {eta : ℝ} (he : 0 < eta) :
    ninthRadius eta ^ 3 = rsSaddleScale * eta := by
  unfold ninthRadius
  rw [← Real.rpow_mul_natCast (mul_pos rsSaddleScale_pos he).le]
  norm_num

theorem saddleScale_two_three : 2 ≤ rsSaddleScale ∧ rsSaddleScale ≤ 3 := by
  have hs := rsSaddleScale_pos
  have hsq := rsSaddleScale_sq
  constructor <;> nlinarith [Real.two_le_pi, Real.pi_lt_four]

theorem ninthRadius_upper {eta : ℝ} (he : 2 ≤ eta) :
    ninthRadius eta ≤ 21 / 40 * (rsSaddleScale * eta) := by
  have he0 : 0 < eta := by linarith
  have hl : 4 ≤ rsSaddleScale * eta := by
    nlinarith [saddleScale_two_three.1,
      mul_nonneg (sub_nonneg.mpr saddleScale_two_three.1) (sub_nonneg.mpr he)]
  apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) (by positivity)
  rw [ninthRadius_cube he0]
  have hsq : 16 ≤ (rsSaddleScale * eta) ^ 2 := by nlinarith
  have hc := mul_le_mul_of_nonneg_right hsq (mul_pos rsSaddleScale_pos he0).le
  nlinarith

theorem ninthRadius_lower {eta : ℝ} (he : 2 ≤ eta) :
    21 / 40 * rsSaddleScale ≤ ninthRadius eta := by
  have he0 : 0 < eta := by linarith
  have hs := rsSaddleScale_pos
  apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) (ninthRadius_pos he0).le
  rw [ninthRadius_cube he0]
  have hsq : rsSaddleScale ^ 2 ≤ 9 := by nlinarith [saddleScale_two_three.2]
  have hc := mul_le_mul_of_nonneg_right hsq hs.le
  have ht := mul_le_mul_of_nonneg_left he hs.le
  nlinarith

theorem ninthRadius_data {eta : ℝ} (he : 2 ≤ eta) :
    0 < ninthRadius eta ∧
    ninthRadius eta ≤ 3 / 5 * (rsSaddleScale * eta) ∧
    1 / 2 ≤ ninthCutoff eta ∧ ninthCutoff eta ≤ eta / 2 ∧
    21 / 20 * (rsSaddleScale * ninthCutoff eta) = ninthRadius eta := by
  have he0 : 0 < eta := by linarith
  have hs := rsSaddleScale_pos
  have hu := ninthRadius_upper he
  have hl := ninthRadius_lower he
  refine ⟨ninthRadius_pos he0, by nlinarith [mul_pos hs he0], ?_, ?_, ?_⟩
  · unfold ninthCutoff
    rw [le_div_iff₀ hs]
    linarith
  · unfold ninthCutoff
    rw [div_le_iff₀ hs]
    nlinarith
  · unfold ninthCutoff
    field_simp

theorem ninthSourceMajorant (sigma : ℝ) {eta : ℝ} (he : 0 < eta) :
    rsSourceMajorant sigma (rsSaddleScale * eta) (ninthRadius eta) =
      Real.exp (|sigma - 1| * Real.log (5 / 2) + 5 / 6) := by
  have hl := mul_pos rsSaddleScale_pos he
  have hs := rsSaddleScale_pos.ne'
  have hx : 5 / 6 * (rsSaddleScale * eta) ^ 2 *
      (ninthRadius eta / (rsSaddleScale * eta)) ^ 3 = 5 / 6 := by
    rw [div_pow, ninthRadius_cube he]
    field_simp
  rw [rsSourceMajorant, hx]

theorem ninthRadius_ninth {eta : ℝ} (he : 0 < eta) :
    ninthRadius eta ^ 9 = rsSaddleScale ^ 3 * eta ^ 3 := by
  rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul, ninthRadius_cube he, mul_pow]

theorem ninthCentralConstant (sigma : ℝ) {eta : ℝ} (he : 0 < eta) :
    centralTaylorConstant sigma eta (ninthRadius eta) 9 =
      21 * Real.exp (|sigma - 1| * Real.log (5 / 2) + 5 / 6) *
        rsSaddleScale ^ 6 / eta ^ 3 := by
  rw [centralTaylorConstant, ninthSourceMajorant sigma he, div_pow, ninthRadius_ninth he]
  have hs := rsSaddleScale_pos.ne'
  have he' := he.ne'
  field_simp

theorem ninthCutoff_ninth {eta : ℝ} (he : 0 < eta) :
    ninthCutoff eta ^ 9 = (20 / 21 : ℝ) ^ 9 * eta ^ 3 / rsSaddleScale ^ 6 := by
  rw [ninthCutoff, div_pow, mul_pow, ninthRadius_ninth he]
  have hs := rsSaddleScale_pos.ne'
  field_simp

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
