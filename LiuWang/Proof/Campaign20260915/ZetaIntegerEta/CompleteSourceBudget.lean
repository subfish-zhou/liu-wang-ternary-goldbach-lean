import LiuWang.Proof.Campaign20260915.ZetaIntegerEta.SourceJumpCompensation
import LiuWang.Proof.Campaign20260915.ZetaIntegerEta.SharpTailAllocation
import LiuWang.Proof.Campaign20260915.ZetaJnCentral.SourceLocalBudgets

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaIntegerEta
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell
open LiuWang.Proof.Campaign20260915.ZetaJnCentral
open LiuWang.Proof.Campaign20260915.ZetaC2LeftTail

theorem source_remainder_three_piece_identity {eta : ℝ} (he : 1 ≤ eta)
    (hint : ∀ k : ℤ, eta ≠ k) (N : ℕ) :
    let s : ℂ := (1 / 2 : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2
    sourceZetaPolynomialRemainder (1 / 2) eta ⌊eta⌋₊ N =
      rsHankelPrefactor s *
        ((∫ y : ℝ in (eta / 2)..(-eta / 2), rsC2RightIntegrand s eta ⌊eta⌋₊ y) -
          rsLocalPrefactor (1 / 2) eta ⌊eta⌋₊ *
            (sourceGaussianPhase eta ⌊eta⌋₊ *
              ∑ k ∈ Finset.range N, rsSaddleCoefficient (1 / 2) (rsSaddleScale * eta) k *
                (rsSaddleScale : ℂ) ^ k * correctionMoment k (sourcePhiParameter eta ⌊eta⌋₊))) +
        rsHankelPrefactor s *
          (∫ r : ℝ in Ioi 0, rsC2LeftIntegrand s eta ⌊eta⌋₊ r) -
        rsHankelPrefactor s *
          (∫ y : ℝ in Ioi (eta / 2), rsC2RightIntegrand s eta ⌊eta⌋₊ y) := by
  dsimp only
  have he0 : 0 < eta := by linarith
  have hm := Nat.floor_pos.mpr he
  have hf := sourceFraction_floor he0.le hint
  rw [sourceZetaPolynomialRemainder_eq_C2 (1 / 2) (by norm_num) hm hf.1 hf.2 N,
    rsSourceC2_local_split hm (by norm_num [pow_two, mul_re, mul_im]) he0 hint]
  norm_num only [ofReal_div, ofReal_one, ofReal_ofNat]
  have hp := sourceLocalPolynomial_integral (1 / 2) hf.1 hf.2 N
  linear_combination
    -rsHankelPrefactor ((1 / 2 : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) *
      rsLocalPrefactor (1 / 2) eta ⌊eta⌋₊ * hp

theorem source_remainder_three_piece_bound {eta : ℝ} (he : 10 ≤ eta)
    (hint : ∀ k : ℤ, eta ≠ k) (N : ℕ) :
    let s : ℂ := (1 / 2 : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2
    ‖sourceZetaPolynomialRemainder (1 / 2) eta ⌊eta⌋₊ N‖ ≤
      ‖(∫ y : ℝ in (eta / 2)..(-eta / 2), rsC2RightIntegrand s eta ⌊eta⌋₊ y) -
          rsLocalPrefactor (1 / 2) eta ⌊eta⌋₊ *
            (sourceGaussianPhase eta ⌊eta⌋₊ *
              ∑ k ∈ Finset.range N, rsSaddleCoefficient (1 / 2) (rsSaddleScale * eta) k *
                (rsSaddleScale : ℂ) ^ k * correctionMoment k (sourcePhiParameter eta ⌊eta⌋₊))‖ +
        (1 / 500) * (eta ^ (-(1 / 2 : ℝ)) / eta ^ 3) := by
  dsimp only
  let s : ℂ := (1 / 2 : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2
  have hs : s.re = 1 / 2 := by norm_num [s, pow_two, mul_re, mul_im]
  have ht : s.im = 2 * Real.pi * eta ^ 2 := by
    simp [s, ← ofReal_pow, mul_pow, rsSaddleScale_sq]
  have hl := left_tail_source_allocation he hs ht
  have hr := right_tail_source_allocation he
  rw [source_remainder_three_piece_identity (by linarith : 1 ≤ eta) hint N]
  apply (norm_sub_le _ _).trans
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  rw [norm_mul]
  have hp := critical_hankel_prefactor_norm_le_one hs
  have hc := mul_le_mul_of_nonneg_right hp (norm_nonneg
    ((∫ y : ℝ in (eta / 2)..(-eta / 2), rsC2RightIntegrand s eta ⌊eta⌋₊ y) -
      rsLocalPrefactor (1 / 2) eta ⌊eta⌋₊ *
        (sourceGaussianPhase eta ⌊eta⌋₊ *
          ∑ k ∈ Finset.range N, rsSaddleCoefficient (1 / 2) (rsSaddleScale * eta) k *
            (rsSaddleScale : ℂ) ^ k * correctionMoment k (sourcePhiParameter eta ⌊eta⌋₊))))
  simp only [one_mul] at hc
  dsimp [s] at hc hl
  linarith

theorem complete_source_R0_noninteger {eta : ℝ}
    (he : 0 ≤ eta) (ht : 125 < eta ^ 2) (hint : ∀ k : ℤ, eta ≠ k) :
    ‖sourceZetaPolynomialRemainder (1 / 2) eta ⌊eta⌋₊ 1‖ ≤
      (371 / 500) * (eta ^ (-(1 / 2 : ℝ)) / eta) := by
  have he0 : 0 < eta := by nlinarith
  have h := source_remainder_three_piece_bound (by nlinarith : 10 ≤ eta) hint 1
  have hz := sourcePhiParameter_floor_domain he
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    sourceSaddle_scaled_zero, one_mul, correctionMoment_zero_phi hz] at h
  have hc := local_hankel_one_sharp_R0 he ht hint
  have hs := mul_le_mul_of_nonneg_left (source_error_scale_three_le_one
    (by nlinarith : 1 ≤ eta)) (by norm_num : (0 : ℝ) ≤ 1 / 500)
  dsimp only [rsC2RightIntegrand] at h
  calc
    _ ≤ _ := h
    _ ≤ eta ^ (-(1 / 2 : ℝ)) * ((37 / 50) / eta) +
        (1 / 500) * (eta ^ (-(1 / 2 : ℝ)) / eta) := add_le_add hc hs
    _ = _ := by ring

theorem complete_source_R2_noninteger {eta : ℝ}
    (he : 0 ≤ eta) (ht : 2000 < eta ^ 2) (hint : ∀ k : ℤ, eta ≠ k) :
    ‖sourceZetaPolynomialRemainder (1 / 2) eta ⌊eta⌋₊ 7‖ ≤
      (129 / 125) * (eta ^ (-(1 / 2 : ℝ)) / eta ^ 3) := by
  have h := source_remainder_three_piece_bound (by nlinarith : 10 ≤ eta) hint 7
  have hc := local_hankel_seven_sharp_R2 he ht hint
  dsimp only [rsC2RightIntegrand] at h
  calc
    _ ≤ _ := h
    _ ≤ eta ^ (-(1 / 2 : ℝ)) * ((103 / 100) / eta ^ 3) +
        (1 / 500) * (eta ^ (-(1 / 2 : ℝ)) / eta ^ 3) := add_le_add hc le_rfl
    _ = _ := by ring

end LiuWang.Proof.Campaign20260915.ZetaIntegerEta
