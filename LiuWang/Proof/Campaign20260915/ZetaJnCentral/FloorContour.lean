import LiuWang.Proof.Campaign20260915.ZetaJnCentral.ArcLocalConsumer

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

def jnMinorLocalContour (sigma eta : ℝ) (m N : ℕ) (k : ℤ) (e : ℝ) : ℂ :=
  (∫ y : ℝ in (eta / 2)..sourcePoleDistance, rsJnIntegrand sigma eta m N y) +
  (∫ y : ℝ in sourcePoleDistance..(sourceMinorHigh eta k e), rsJnIntegrand sigma eta m N y) +
  (e : ℂ) * jnSourceMinorArc sigma eta m N k e +
  (∫ y : ℝ in (sourceMinorLow eta k e)..(-sourcePoleDistance), rsJnIntegrand sigma eta m N y) +
  (∫ y : ℝ in (-sourcePoleDistance)..(-eta / 2), rsJnIntegrand sigma eta m N y)

def jnFloorContour (sigma eta : ℝ) (N : ℕ) : ℂ :=
  if eta - ⌊eta⌋₊ ≤ Real.sqrt 2 * sourcePoleRadius then
    jnMinorLocalContour sigma eta ⌊eta⌋₊ N (⌊eta⌋₊ : ℤ) 1
  else if (⌊eta⌋₊ : ℝ) + 1 - eta ≤ Real.sqrt 2 * sourcePoleRadius then
    jnMinorLocalContour sigma eta ⌊eta⌋₊ N ((⌊eta⌋₊ : ℤ) + 1) (-1)
  else
    ∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand sigma eta ⌊eta⌋₊ N y

theorem source_pole_disks_separated : 2 * (Real.sqrt 2 * sourcePoleRadius) < 1 := by
  have hs : Real.sqrt 2 < Real.sqrt Real.pi :=
    Real.sqrt_lt_sqrt (by norm_num) (by linarith [Real.pi_gt_three])
  unfold sourcePoleRadius
  have hid : 2 * (Real.sqrt 2 * (1 / (2 * Real.sqrt Real.pi))) =
      Real.sqrt 2 / Real.sqrt Real.pi := by ring
  rw [hid, div_lt_one (by positivity : 0 < Real.sqrt Real.pi)]
  exact hs

theorem source_pole_disks_not_both (eta : ℝ) (m : ℕ) :
    ¬(eta - m ≤ Real.sqrt 2 * sourcePoleRadius ∧
      (m : ℝ) + 1 - eta ≤ Real.sqrt 2 * sourcePoleRadius) := by
  rintro ⟨hl, hr⟩
  linarith [source_pole_disks_separated]

theorem jn_floor_contour_eq (sigma : ℝ) {eta : ℝ}
    (he : 2 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) (N : ℕ) :
    jnFloorContour sigma eta (N + 1) =
      ∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand sigma eta ⌊eta⌋₊ (N + 1) y := by
  have he0 : 0 < eta := by linarith
  have hf := sourceFraction_floor he0.le hint
  have h0 := Nat.zero_le_self_sub_floor he0.le
  have h1 := (Nat.self_sub_floor_lt_one eta).le
  have hD : sourcePoleDistance ≤ eta / 2 := by linarith [sourcePoleDistance_lt_one]
  unfold jnFloorContour
  split_ifs with hl hr
  · exact (jn_local_minor_split sigma he0 hD (e := 1) (k := (⌊eta⌋₊ : ℤ))
      (by norm_num) (by simpa using hf.1)
      (by simpa only [Int.cast_natCast, abs_of_pos hf.1] using hl) h0 h1 N).symm
  · have hside : 0 < (-1 : ℝ) * (eta - (((⌊eta⌋₊ : ℤ) + 1 : ℤ) : ℝ)) := by
      push_cast
      linarith [hf.2]
    have hk : |eta - (((⌊eta⌋₊ : ℤ) + 1 : ℤ) : ℝ)| ≤ Real.sqrt 2 * sourcePoleRadius := by
      push_cast
      rw [abs_of_nonpos (by linarith [hf.2])]
      linarith
    exact (jn_local_minor_split sigma he0 hD (e := -1) (by norm_num) hside hk h0 h1 N).symm
  · rfl

theorem jn_floor_contour_bound (sigma : ℝ) {eta R : ℝ}
    (he : 2 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k)
    (hR0 : 0 < R) (hR : R ≤ 3 / 5 * (rsSaddleScale * eta))
    (hDR : 21 / 20 * (rsSaddleScale * sourcePoleDistance) ≤ R) (N : ℕ) :
    ‖jnFloorContour sigma eta (N + 1)‖ ≤ arcLocalBudget sigma eta R N := by
  have he0 : 0 < eta := by linarith
  have hf := sourceFraction_floor he0.le hint
  have h0 := Nat.zero_le_self_sub_floor he0.le
  have h1 := (Nat.self_sub_floor_lt_one eta).le
  have hD : sourcePoleDistance ≤ eta / 2 := by linarith [sourcePoleDistance_lt_one]
  rw [jn_floor_contour_eq sigma he hint N]
  by_cases hl : eta - ⌊eta⌋₊ ≤ Real.sqrt 2 * sourcePoleRadius
  · exact jn_local_arc_budget sigma he0 hD hR0 hR hDR (e := 1) (k := (⌊eta⌋₊ : ℤ))
      (by norm_num) (by simpa using hf.1)
      (by simpa only [Int.cast_natCast, abs_of_pos hf.1] using hl) h0 h1 N
  · by_cases hr : (⌊eta⌋₊ : ℝ) + 1 - eta ≤ Real.sqrt 2 * sourcePoleRadius
    · have hside : 0 < (-1 : ℝ) * (eta - (((⌊eta⌋₊ : ℤ) + 1 : ℤ) : ℝ)) := by
        push_cast
        linarith [hf.2]
      have hk : |eta - (((⌊eta⌋₊ : ℤ) + 1 : ℤ) : ℝ)| ≤ Real.sqrt 2 * sourcePoleRadius := by
        push_cast
        rw [abs_of_nonpos (by linarith [hf.2])]
        linarith
      exact jn_local_arc_budget sigma he0 hD hR0 hR hDR (e := -1)
        (by norm_num) hside hk h0 h1 N
    · apply (jn_local_budget sigma he0 hR0 hR sourcePoleDistance_pos hDR hD h0 h1 N).trans
      unfold arcLocalBudget
      have hB := poleArcCoreBound_nonneg sigma eta hR0 (N + 1)
      have hnonneg : 0 ≤ Real.pi * sourcePoleRadius * poleArcCoreBound sigma eta R (N + 1) :=
        mul_nonneg (mul_nonneg Real.pi_pos.le sourcePoleRadius_pos.le) hB
      linarith

theorem local_hankel_floor_contour (sigma : ℝ) {eta : ℝ}
    (he : 2 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) (N : ℕ) :
    (∫ y : ℝ in (eta / 2)..(-eta / 2), rsDescentDirection *
      rsHankelKernel ((sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2)
        ⌊eta⌋₊ (rsDescentPoint eta y)) =
      rsLocalPrefactor sigma eta ⌊eta⌋₊ *
        ((∫ y : ℝ in (eta / 2)..(-eta / 2), rsLocalPolynomialIntegrand sigma eta ⌊eta⌋₊ (N + 1) y) +
          jnFloorContour sigma eta (N + 1)) := by
  rw [rsHankel_local_truncation sigma ⌊eta⌋₊ (N + 1) (by linarith) hint,
    jn_floor_contour_eq sigma he hint N]

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
