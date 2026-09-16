import LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.CorrectionEnclosures
import LiuWang.Proof.Campaign20260915.ZetaValidation.RationalAngle

set_option autoImplicit false
noncomputable section

open scoped Real

namespace LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure

open LiuWang.Proof.Campaign20260915.ZetaValidation

def machinPi (n : ℕ) : ℚ :=
  16 * rationalAtanTaylor n (1 / 5) - 4 * rationalAtanTaylor n (1 / 239)

def machinPiError (n : ℕ) : ℚ := 40 * (1 / 2) ^ (n + 1) / (n + 1)

theorem machinPi_correct (n : ℕ) : |Real.pi - (machinPi n : ℝ)| ≤ (machinPiError n : ℝ) := by
  have h5 := rationalAtanTaylor_error n (q := 1 / 5) (by norm_num)
  have h239 := rationalAtanTaylor_error n (q := 1 / 239) (by norm_num)
  have hm := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  have he : Real.pi - (machinPi n : ℝ) =
      16 * (Real.arctan ((1 / 5 : ℚ) : ℝ) - (rationalAtanTaylor n (1 / 5) : ℝ)) -
      4 * (Real.arctan ((1 / 239 : ℚ) : ℝ) - (rationalAtanTaylor n (1 / 239) : ℝ)) := by
    norm_num [machinPi] at hm ⊢
    linarith
  rw [he]
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_mul]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 16),
    abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have h := add_le_add (mul_le_mul_of_nonneg_left h5 (by norm_num : (0 : ℝ) ≤ 16))
    (mul_le_mul_of_nonneg_left h239 (by norm_num : (0 : ℝ) ≤ 4))
  push_cast at h
  apply h.trans_eq
  push_cast [machinPiError]
  ring

def roundedMachinPi (n D : ℕ) : ℚ := (⌊machinPi n * D⌋ : ℚ) / D
def roundedMachinError (n D : ℕ) : ℚ := machinPiError n + 1 / D

theorem roundedMachinPi_correct (n D : ℕ) (hD : 0 < D) :
    |Real.pi - (roundedMachinPi n D : ℝ)| ≤ (roundedMachinError n D : ℝ) := by
  have hDQ : (0 : ℚ) < D := by exact_mod_cast hD
  have hround : |machinPi n - roundedMachinPi n D| ≤ (1 : ℚ) / D := by
    have h1 := Int.floor_le (machinPi n * D)
    have h2 := Int.lt_floor_add_one (machinPi n * D)
    unfold roundedMachinPi
    rw [sub_div' hDQ.ne', abs_div, abs_of_pos hDQ, div_le_div_iff_of_pos_right hDQ, abs_le]
    constructor <;> linarith
  have hR : |(machinPi n : ℝ) - (roundedMachinPi n D : ℝ)| ≤ ((1 / (D : ℚ) : ℚ) : ℝ) := by
    exact_mod_cast hround
  have h := (abs_sub_le Real.pi (machinPi n : ℝ) (roundedMachinPi n D : ℝ)).trans
    (add_le_add (machinPi_correct n) hR)
  simpa only [roundedMachinError, Rat.cast_add] using h

def precisePi : ℚ := roundedMachinPi 400 (10 ^ 130)
def precisePiError : ℚ := roundedMachinError 400 (10 ^ 130)

theorem precisePi_correct : |Real.pi - (precisePi : ℝ)| ≤ (precisePiError : ℝ) :=
  roundedMachinPi_correct 400 (10 ^ 130) (by positivity)

theorem precisePiError_small : precisePiError ≤ (1 : ℚ) / 10 ^ 120 := by
  decide +kernel

def precisePhi (r d : ℚ) : RationalBall := phiApprox 128 precisePi precisePiError r d
def precisePhiOne (r d : ℚ) : RationalBall :=
  phiOneApprox 128 precisePi precisePiError r (1 / 10 ^ 17) d
def precisePhiTwo (r d : ℚ) : RationalBall :=
  phiTwoApprox 128 precisePi precisePiError r (1 / 10 ^ 17) d

theorem precisePhi_correct (r d : ℚ) {z : ℝ}
    (hr : |(r : ℝ)| ≤ 1) (hz : |z| ≤ 1) (hd : |z - r| ≤ (d : ℝ)) :
    (precisePhi r d).Contains (rsPhi z) :=
  phiApprox_correct 128 precisePi precisePiError r d precisePi_correct hr hz hd

theorem precisePhiOne_correct (r d : ℚ) {z : ℝ}
    (hr : |(r : ℝ)| ≤ 1) (hz : |z| ≤ 1) (hd : |z - r| ≤ (d : ℝ)) :
    (precisePhiOne r d).Contains (rsPhiOne z) :=
  phiOneApprox_correct 128 precisePi precisePiError r (1 / 10 ^ 17) d precisePi_correct hr
    (by norm_num) (by norm_num) hz hd

theorem precisePhiTwo_correct (r d : ℚ) {z : ℝ}
    (hr : |(r : ℝ)| ≤ 1) (hz : |z| ≤ 1) (hd : |z - r| ≤ (d : ℝ)) :
    (precisePhiTwo r d).Contains (rsPhiTwo z) :=
  phiTwoApprox_correct 128 precisePi precisePiError r (1 / 10 ^ 17) d precisePi_correct hr
    (by norm_num) (by norm_num) hz hd

end LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure
