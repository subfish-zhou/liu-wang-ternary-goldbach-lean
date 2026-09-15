import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.Titchmarsh.EulerIdentity
import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.CriticalMean
import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.AuxiliaryDomain

/-! LWD p.285, (3.39), including the original closed sigma and height domains. -/

set_option autoImplicit false
noncomputable section

open Complex Set
open LiuWang.Proof.DirichletZeroCount.Applications

namespace LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.Titchmarsh

def smallHeightBound (sigma t : ℝ) : ℝ :=
  (1 / 2) * Real.sqrt (((sigma + 1) ^ 2 + t ^ 2) / ((sigma - 1) ^ 2 + t ^ 2)) +
    Real.sqrt (sigma ^ 2 + t ^ 2) / (2 * sigma)

private theorem weighted_schwarz_two {x z R : ℝ}
    (hx : 0 ≤ x) (hz : 0 ≤ z) (hR : 0 < R)
    (h : x ^ 2 + R * z ^ 2 ≤ R * (R + 1)) :
    x + z ≤ R + 1 := by
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ R + 1 by linarith)
  have hs : R * (x + z) ^ 2 ≤ R * (R + 1) ^ 2 := by
    nlinarith only [hm, sq_nonneg (x - R * z)]
  have hs' := (mul_le_mul_iff_right₀ hR).mp hs
  nlinarith

theorem smallHeightBound_le_five {sigma t : ℝ}
    (hs : 1 / 2 ≤ sigma) (hs' : sigma ≤ 3 / 4) (ht : |t| ≤ 1) :
    smallHeightBound sigma t ≤ 5 := by
  have ht2 : t ^ 2 ≤ 1 := by
    nlinarith [sq_abs t, mul_nonneg (sub_nonneg.mpr ht) (abs_nonneg t)]
  have hd : 0 < (sigma - 1) ^ 2 + t ^ 2 := by
    have : 0 < (sigma - 1) ^ 2 := sq_pos_of_ne_zero (by linarith)
    positivity
  have hrat : ((sigma + 1) ^ 2 + t ^ 2) / ((sigma - 1) ^ 2 + t ^ 2) ≤ 49 := by
    apply (div_le_iff₀ hd).mpr
    have hm := mul_nonneg (show 0 ≤ 3 / 4 - sigma by linarith)
      (show 0 ≤ 2 / 3 - sigma / 3 by linarith)
    nlinarith [sq_nonneg t]
  have hr := Real.sq_sqrt (show
    0 ≤ ((sigma + 1) ^ 2 + t ^ 2) / ((sigma - 1) ^ 2 + t ^ 2) by positivity)
  have hx : Real.sqrt (((sigma + 1) ^ 2 + t ^ 2) / ((sigma - 1) ^ 2 + t ^ 2)) ≤ 7 := by
    nlinarith [Real.sqrt_nonneg
      (((sigma + 1) ^ 2 + t ^ 2) / ((sigma - 1) ^ 2 + t ^ 2))]
  have hc := Real.sq_sqrt (show 0 ≤ sigma ^ 2 + t ^ 2 by positivity)
  have hz : Real.sqrt (sigma ^ 2 + t ^ 2) / (2 * sigma) ≤ 3 / 2 := by
    apply (div_le_iff₀ (by linarith : 0 < 2 * sigma)).mpr
    nlinarith [Real.sqrt_nonneg (sigma ^ 2 + t ^ 2)]
  unfold smallHeightBound
  linarith

theorem smallHeightBound_le_inverse_gap {sigma t : ℝ}
    (hs : 3 / 4 ≤ sigma) (hs' : sigma < 1) (ht : |t| ≤ 1) :
    smallHeightBound sigma t ≤ 1 / (1 - sigma) := by
  let d := 1 - sigma
  let r := t ^ 2
  let R := (sigma + 1) / d
  let x := Real.sqrt (((sigma + 1) ^ 2 + r) / (d ^ 2 + r))
  let z := Real.sqrt (sigma ^ 2 + r) / sigma
  have hd : 0 < d := by dsimp [d]; linarith
  have hd' : d ≤ 1 / 4 := by dsimp [d]; linarith
  have hs0 : 0 < sigma := by linarith
  have hr : 0 ≤ r := sq_nonneg t
  have hr' : r ≤ 1 := by
    dsimp [r]
    nlinarith [sq_abs t, mul_nonneg (sub_nonneg.mpr ht) (abs_nonneg t)]
  have hb : 0 < d ^ 2 + r := by positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hx2 : x ^ 2 = ((sigma + 1) ^ 2 + r) / (d ^ 2 + r) :=
    Real.sq_sqrt (by positivity)
  have hz2 : z ^ 2 = (sigma ^ 2 + r) / sigma ^ 2 := by
    dsimp [z]
    rw [div_pow, Real.sq_sqrt (by positivity)]
  have hd2 : d ^ 2 ≤ 1 / 16 := by nlinarith
  have hprod : d * (sigma + 1) * (d ^ 2 + r) ≤ 17 / 32 := by
    have h1 := mul_le_mul hd' (show sigma + 1 ≤ 2 by linarith)
      (show 0 ≤ sigma + 1 by linarith) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have h2 := mul_le_mul h1 (show d ^ 2 + r ≤ 17 / 16 by linarith)
      (by positivity : 0 ≤ d ^ 2 + r) (by norm_num : (0 : ℝ) ≤ (1 / 4) * 2)
    linarith
  have hs3 : 27 / 64 ≤ sigma ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 4) hs 3
    norm_num at this
    exact this
  have hcond : d * (sigma + 1) * (d ^ 2 + r) ≤ 4 * sigma ^ 3 := by linarith
  have hweighted : x ^ 2 + R * z ^ 2 ≤ R * (R + 1) := by
    rw [hx2, hz2]
    dsimp [R]
    have heq :
        (sigma + 1) / d * ((sigma + 1) / d + 1) -
          (((sigma + 1) ^ 2 + r) / (d ^ 2 + r) +
            (sigma + 1) / d * ((sigma ^ 2 + r) / sigma ^ 2)) =
        r * (4 * sigma ^ 3 - d * (sigma + 1) * (d ^ 2 + r)) /
          (d ^ 2 * (d ^ 2 + r) * sigma ^ 2) := by
      field_simp
      dsimp [d]
      ring
    have hn : 0 ≤ r * (4 * sigma ^ 3 - d * (sigma + 1) * (d ^ 2 + r)) /
        (d ^ 2 * (d ^ 2 + r) * sigma ^ 2) :=
      div_nonneg (mul_nonneg hr (sub_nonneg.mpr hcond)) (by positivity)
    linarith
  have hsum := weighted_schwarz_two (x := x) (z := z) (Real.sqrt_nonneg _)
    (div_nonneg (Real.sqrt_nonneg _) hs0.le) hR hweighted
  have heq : smallHeightBound sigma t = (x + z) / 2 := by
    unfold smallHeightBound
    dsimp [x, z, r, d]
    rw [show (sigma - 1) ^ 2 = (1 - sigma) ^ 2 by ring]
    ring
  have hR' : (R + 1) / 2 = 1 / (1 - sigma) := by
    dsimp [R, d]
    field_simp [show 1 - sigma ≠ 0 by linarith]
    ring
  rw [heq, ← hR']
  linarith

theorem smallHeightBound_le_source {y sigma t : ℝ}
    (hy : 10000 * Real.log 6 ≤ y)
    (hs : sigma ∈ Icc (1 / 2) (1 - sourceDelta y)) (ht : |t| ≤ 1) :
    smallHeightBound sigma t ≤ 1.5 * Real.log y := by
  have hl := (source_height_log_bounds hy).2
  have hd : 0 < sourceDelta y := by unfold sourceDelta; positivity
  have hs1 : sigma < 1 := by linarith [hs.2]
  by_cases hsmall : sigma ≤ 3 / 4
  · exact (smallHeightBound_le_five hs.1 hsmall ht).trans (by linarith)
  · have hgap := one_div_le_one_div_of_le hd
      (show sourceDelta y ≤ 1 - sigma by linarith [hs.2])
    have heq : 1 / sourceDelta y = 1.5 * Real.log y := by
      unfold sourceDelta
      simp
    exact (smallHeightBound_le_inverse_gap (le_of_not_ge hsmall) hs1 ht).trans
      (hgap.trans_eq heq)

theorem equation_3_39 {y sigma t : ℝ}
    (hy : 10000 * Real.log 6 ≤ y)
    (hs : sigma ∈ Icc (1 / 2) (1 - sourceDelta y)) (ht : |t| ≤ 1) :
    ‖riemannZeta ((sigma : ℂ) + t * I)‖ ≤
        (1 / 2) * Real.sqrt (((sigma + 1) ^ 2 + t ^ 2) / ((sigma - 1) ^ 2 + t ^ 2)) +
          Real.sqrt (sigma ^ 2 + t ^ 2) / (2 * sigma) ∧
      (1 / 2) * Real.sqrt (((sigma + 1) ^ 2 + t ^ 2) / ((sigma - 1) ^ 2 + t ^ 2)) +
          Real.sqrt (sigma ^ 2 + t ^ 2) / (2 * sigma) ≤ 1.5 * Real.log y := by
  have hl := (source_height_log_bounds hy).2
  have hd : 0 < sourceDelta y := by unfold sourceDelta; positivity
  have hs1 : (sigma : ℂ) + t * I ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith [hs.2]
  exact ⟨equation_3_39_first (by linarith [hs.1]) hs1,
    smallHeightBound_le_source hy hs ht⟩

theorem zeta_small_height {y sigma t : ℝ}
    (hy : 10000 * Real.log 6 ≤ y)
    (hs : sigma ∈ Icc (1 / 2) (1 - sourceDelta y)) (ht : |t| ≤ 1) :
    ‖riemannZeta ((sigma : ℂ) + t * I)‖ ≤ 1.5 * Real.log y :=
  (equation_3_39 hy hs ht).1.trans (equation_3_39 hy hs ht).2

end LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.Titchmarsh
