import LiuWang.Proof.Campaign20260915.ZetaC2LeftTail.OriginalScale

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaC2LeftTail
open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem saddle_critical_coordinates (eta : ℝ) :
    ((1 / 2 : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2).re = 1 / 2 ∧
      ((1 / 2 : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2).im =
        2 * Real.pi * eta ^ 2 := by
  have hsq : ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2 =
      ((2 * Real.pi * eta ^ 2 : ℝ) : ℂ) := by
    rw [← ofReal_pow, mul_pow, rsSaddleScale_sq]
  rw [hsq]
  norm_num [pow_two]

theorem source_local_left_identity (N : ℕ) {eta : ℝ} (he : 1 ≤ eta)
    (hint : ∀ n : ℤ, eta ≠ n) :
    let s : ℂ := (1 / 2 : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2
    rsSourceC2 s eta ⌊eta⌋₊ -
      rsLocalPrefactor (1 / 2) eta ⌊eta⌋₊ *
        ((∫ y : ℝ in (eta / 2)..(-eta / 2),
            rsLocalPolynomialIntegrand (1 / 2) eta ⌊eta⌋₊ N y) +
          ∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta ⌊eta⌋₊ N y) +
      (∫ y : ℝ in Ioi (eta / 2), rsC2RightIntegrand s eta ⌊eta⌋₊ y) =
        ∫ r : ℝ in Ioi 0, rsC2LeftIntegrand s eta ⌊eta⌋₊ r := by
  dsimp only
  have hm : 0 < ⌊eta⌋₊ := Nat.floor_pos.mpr he
  have h := rsSourceC2_local_truncation (1 / 2) (m := ⌊eta⌋₊) N hm
    (by norm_num) (by linarith) hint
  norm_num only [ofReal_div, ofReal_one, ofReal_ofNat] at h
  linear_combination h

theorem source_local_truncation_left_budget (N : ℕ) {eta : ℝ} (he : 10 ≤ eta)
    (hint : ∀ n : ℤ, eta ≠ n) :
    let s : ℂ := (1 / 2 : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2
    ‖rsHankelPrefactor s *
      (rsSourceC2 s eta ⌊eta⌋₊ -
        rsLocalPrefactor (1 / 2) eta ⌊eta⌋₊ *
          ((∫ y : ℝ in (eta / 2)..(-eta / 2),
              rsLocalPolynomialIntegrand (1 / 2) eta ⌊eta⌋₊ N y) +
            ∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta ⌊eta⌋₊ N y) +
        ∫ y : ℝ in Ioi (eta / 2), rsC2RightIntegrand s eta ⌊eta⌋₊ y)‖ ≤
      1 / (10 * eta ^ 4) := by
  dsimp only
  rw [source_local_left_identity N (by linarith) hint]
  exact left_hankel_floor_budget he (saddle_critical_coordinates eta).1
    (saddle_critical_coordinates eta).2

theorem source_R0_left_budget {eta : ℝ} (he : 0 ≤ eta) (hR : 125 < eta ^ 2)
    (hint : ∀ n : ℤ, eta ≠ n) :
    let s : ℂ := (1 / 2 : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2
    ‖rsHankelPrefactor s *
      (rsSourceC2 s eta ⌊eta⌋₊ -
        rsLocalPrefactor (1 / 2) eta ⌊eta⌋₊ *
          ((∫ y : ℝ in (eta / 2)..(-eta / 2),
              rsLocalPolynomialIntegrand (1 / 2) eta ⌊eta⌋₊ 1 y) +
            ∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta ⌊eta⌋₊ 1 y) +
        ∫ y : ℝ in Ioi (eta / 2), rsC2RightIntegrand s eta ⌊eta⌋₊ y)‖ ≤
      1 / 10 * (eta ^ 2) ^ (-(3 / 4 : ℝ)) := by
  have h10 : 10 ≤ eta := (sq_le_sq₀ (by norm_num) he).mp (by nlinarith)
  exact (source_local_truncation_left_budget 1 h10 hint).trans
    (left_scalar_original_scale (by linarith) (by norm_num))

theorem source_R2_left_budget {eta : ℝ} (he : 0 ≤ eta) (hR : 2000 < eta ^ 2)
    (hint : ∀ n : ℤ, eta ≠ n) :
    let s : ℂ := (1 / 2 : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2
    ‖rsHankelPrefactor s *
      (rsSourceC2 s eta ⌊eta⌋₊ -
        rsLocalPrefactor (1 / 2) eta ⌊eta⌋₊ *
          ((∫ y : ℝ in (eta / 2)..(-eta / 2),
              rsLocalPolynomialIntegrand (1 / 2) eta ⌊eta⌋₊ 7 y) +
            ∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta ⌊eta⌋₊ 7 y) +
        ∫ y : ℝ in Ioi (eta / 2), rsC2RightIntegrand s eta ⌊eta⌋₊ y)‖ ≤
      1 / 10 * (eta ^ 2) ^ (-(7 / 4 : ℝ)) := by
  have h10 : 10 ≤ eta := (sq_le_sq₀ (by norm_num) he).mp (by nlinarith)
  exact (source_local_truncation_left_budget 7 h10 hint).trans
    (left_scalar_original_scale (by linarith) (by norm_num))

end LiuWang.Proof.Campaign20260915.ZetaC2LeftTail
