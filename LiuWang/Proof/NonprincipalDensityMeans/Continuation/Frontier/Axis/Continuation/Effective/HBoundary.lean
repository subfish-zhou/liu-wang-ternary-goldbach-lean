import LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.Continuation.Effective.Means

/-! Effective H vertical logarithms with the right side paid and no free M. -/

set_option autoImplicit false
noncomputable section

open Finset MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.NonprincipalDensityAdvance
open LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.PVContinuation

namespace LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.PVEffective

theorem balancedPower_ge_inv {q y sigma : ℝ} (hq : 1 ≤ q) (hy : 1 ≤ y)
    (hs : sigma ∈ Set.Icc (3 / 4) 1) : q⁻¹ ≤ balancedPower q y sigma := by
  have hq0 : 0 < q := by linarith
  have hy0 : 0 < y := by linarith
  have ha : (-1 : ℝ) ≤ 1 - 2 * sigma ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - sigma by linarith [hs.2])
      (show 0 ≤ 1 + sigma by linarith [hs.1])]
  have hb : 0 ≤ (1 - sigma) * (2 * sigma + 3) :=
    mul_nonneg (by linarith [hs.2]) (by linarith [hs.1])
  have h1 : q⁻¹ ≤ q ^ (1 - 2 * sigma ^ 2) := by
    simpa only [Real.rpow_neg_one] using Real.rpow_le_rpow_of_exponent_le hq ha
  have h2 : (1 : ℝ) ≤ y ^ ((1 - sigma) * (2 * sigma + 3)) := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hy hb
  exact h1.trans (le_mul_of_one_le_right (Real.rpow_nonneg hq0.le _) h2)

theorem right_log_cost_effective (q : ℕ) [NeZero q] {y sigma : ℝ} (hy : 2 ≤ y)
    (hs : sigma ∈ Set.Icc (3 / 4) 1) :
    nonprincipalRatio q * (16 * y / ((q : ℝ) * y - 1) ^ 2) ≤
      64 * balancedPower q y sigma * (1 + Real.log ((q : ℝ) * y)) ^ 5 := by
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hq0 : (0 : ℝ) < q := by positivity
  have hz : 2 ≤ (q : ℝ) * y := by nlinarith
  have hr : nonprincipalRatio q ≤ 1 := by
    have hp : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
    apply (div_le_one hp).mpr
    exact_mod_cast Nat.sub_le q.totient 1
  have hrat : 16 * y / ((q : ℝ) * y - 1) ^ 2 ≤ 64 / (q : ℝ) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos (by linarith : 0 < (q : ℝ) * y - 1)) hq0).mpr
    nlinarith [sq_nonneg ((q : ℝ) * y - 2)]
  have h1 := (mul_le_of_le_one_left (by positivity) hr).trans hrat
  have h2 := mul_le_mul_of_nonneg_left (balancedPower_ge_inv hq (by linarith : 1 ≤ y) hs)
    (by norm_num : (0 : ℝ) ≤ 64)
  have hL : 1 ≤ (1 + Real.log ((q : ℝ) * y)) ^ 5 := by
    apply one_le_pow₀
    have := Real.log_nonneg (show 1 ≤ (q : ℝ) * y by linarith)
    linarith
  have hW := (balancedPower_pos hq0 (by linarith : 0 < y) sigma).le
  have h3 := le_mul_of_one_le_right (show 0 ≤ 64 * balancedPower q y sigma by positivity) hL
  simp only [div_eq_mul_inv] at h1
  exact h1.trans (h2.trans h3)

theorem logSideDifference_effective (q : ℕ) [NeZero q] {y sigma : ℝ} (hy : 2 ≤ y)
    (hqy : (q : ℝ) ≤ y) (hs : sigma ∈ Set.Icc (3 / 4) 1) :
    logSideDifference q ((q : ℝ) * y) sigma y ≤
      169024 * balancedPower q y sigma * (1 + Real.log ((q : ℝ) * y)) ^ 5 := by
  have h := (logSideDifference_PV_fixed_X q hy ⟨by linarith [hs.1], hs.2⟩
    (balancedLength_bounds q hy hqy hs).1).trans
    (add_le_add (balanced_budget_bound q hy hqy hs) (right_log_cost_effective q hy hs))
  exact h.trans_eq (by ring)

theorem logSideDifference_effective_unnormalized (q : ℕ) [NeZero q] {y sigma : ℝ} (hy : 2 ≤ y)
    (hqy : (q : ℝ) ≤ y) (hs : sigma ∈ Set.Icc (3 / 4) 1) :
    (∑ chi ∈ nonprincipalCharacters q, ∫ t in -y..y,
      (Real.log ‖H chi ((q : ℝ) * y) ((sigma : ℂ) + t * Complex.I)‖ -
        Real.log ‖H chi ((q : ℝ) * y) ((2 : ℂ) + t * Complex.I)‖)) ≤
      (q.totient : ℝ) * (169024 * balancedPower q y sigma * (1 + Real.log ((q : ℝ) * y)) ^ 5) := by
  have hp : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  exact ((div_le_iff₀ hp).mp (logSideDifference_effective q hy hqy hs)).trans_eq (mul_comm _ _)

theorem posLog_H_axis_effective (q : ℕ) [NeZero q] {y sigma : ℝ} (hy : 2 ≤ y)
    (hqy : (q : ℝ) ≤ y) (hs : sigma ∈ Set.Icc (3 / 4) 1) :
    (∑ chi ∈ nonprincipalCharacters q, ∫ t : ℝ,
      Real.posLog ‖H chi ((q : ℝ) * y) ((sigma : ℂ) + t * Complex.I)‖ * Real.exp (-|t| / y)) /
        q.totient ≤ 2703360 * balancedPower q y sigma * (1 + Real.log ((q : ℝ) * y)) ^ 5 := by
  have h := (posLog_H_axis_PV q hy ⟨by linarith [hs.1], hs.2⟩
    (balancedLength_bounds q hy hqy hs).1).trans
    (mul_le_mul_of_nonneg_left (balanced_budget_bound q hy hqy hs) (by norm_num : (0 : ℝ) ≤ 16))
  exact h.trans_eq (by ring)

end LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.PVEffective
