import LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.Continuation.Effective.Costs

/-! Effective means with no caller-chosen truncation; X=q*y stays fixed at every window height. -/

set_option autoImplicit false
noncomputable section

open Finset MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.NonprincipalDensityAdvance
open LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.PVContinuation

namespace LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.PVEffective

theorem Fmean_effective (q : ℕ) [NeZero q] {y sigma : ℝ} (hy : 2 ≤ y)
    (hqy : (q : ℝ) ≤ y) (hs : sigma ∈ Set.Icc (3 / 4) 1) :
    Fmean q ((q : ℝ) * y) sigma y ≤
      168960 * (q : ℝ) ^ (1 - 2 * sigma ^ 2) * y ^ ((1 - sigma) * (2 * sigma + 3)) *
        (1 + Real.log ((q : ℝ) * y)) ^ 5 := by
  have h := (Fmean_PV_fixed_X q hy ⟨by linarith [hs.1], hs.2⟩
    (balancedLength_bounds q hy hqy hs).1).trans (balanced_budget_bound q hy hqy hs)
  exact h.trans_eq (by unfold balancedPower; ring)

theorem Fmean_effective_all_heights (q : ℕ) [NeZero q] {y sigma u : ℝ} (hy : 2 ≤ y)
    (hqy : (q : ℝ) ≤ y) (hs : sigma ∈ Set.Icc (3 / 4) 1) (hu : 0 ≤ u) :
    Fmean q ((q : ℝ) * y) sigma u ≤
      (1 + u / y) ^ 3 *
        (168960 * balancedPower q y sigma * (1 + Real.log ((q : ℝ) * y)) ^ 5) :=
  (Fmean_PV_all_heights q hy ⟨by linarith [hs.1], hs.2⟩ hu
    (balancedLength_bounds q hy hqy hs).1).trans
    (mul_le_mul_of_nonneg_left (balanced_budget_bound q hy hqy hs) (by positivity))

theorem exponential_effective (q : ℕ) [NeZero q] {y sigma : ℝ} (hy : 2 ≤ y)
    (hqy : (q : ℝ) ≤ y) (hs : sigma ∈ Set.Icc (3 / 4) 1) :
    exponentialMean q ((q : ℝ) * y) sigma y ≤
      2703360 * balancedPower q y sigma * (1 + Real.log ((q : ℝ) * y)) ^ 5 := by
  have h := (exponential_PV_fixed_X q hy ⟨by linarith [hs.1], hs.2⟩
    (balancedLength_bounds q hy hqy hs).1).trans
    (mul_le_mul_of_nonneg_left (balanced_budget_bound q hy hqy hs) (by norm_num : (0 : ℝ) ≤ 16))
  exact h.trans_eq (by ring)

theorem cosine_effective (q : ℕ) [NeZero q] {y sigma : ℝ} (hy : 2 ≤ y)
    (hqy : (q : ℝ) ≤ y) (hs : sigma ∈ Set.Icc (3 / 4) 1) :
    cosineMean q ((q : ℝ) * y) sigma y ≤
      43253760 * balancedPower q y sigma * (1 + Real.log ((q : ℝ) * y)) ^ 5 := by
  have h := (cosine_PV_fixed_X q hy ⟨by linarith [hs.1], hs.2⟩
    (balancedLength_bounds q hy hqy hs).1).trans
    (mul_le_mul_of_nonneg_left (balanced_budget_bound q hy hqy hs) (by norm_num : (0 : ℝ) ≤ 256))
  exact h.trans_eq (by ring)

theorem Fmean_effective_axis_recovery (q : ℕ) [NeZero q] {y sigma : ℝ} (hy : 2 ≤ y)
    (hqy : (q : ℝ) ≤ y) (hs : sigma ∈ Set.Icc (3 / 4) 1) :
    Fmean q ((q : ℝ) * y) sigma y ≤
      129761280 * balancedPower q y sigma * (1 + Real.log ((q : ℝ) * y)) ^ 5 := by
  exact (Fmean_le_cosineMean q _ hy ⟨by linarith [hs.1], hs.2⟩).trans
    ((mul_le_mul_of_nonneg_left (cosine_effective q hy hqy hs)
      (by norm_num : (0 : ℝ) ≤ 3)).trans_eq (by ring))

theorem Fmean_effective_unnormalized (q : ℕ) [NeZero q] {y sigma : ℝ} (hy : 2 ≤ y)
    (hqy : (q : ℝ) ≤ y) (hs : sigma ∈ Set.Icc (3 / 4) 1) :
    (∑ chi ∈ nonprincipalCharacters q, ∫ t in -y..y,
      ‖NonprincipalDensityAdvance.f chi ((q : ℝ) * y) ((sigma : ℂ) + t * Complex.I)‖ ^ 2) ≤
        (q.totient : ℝ) * (168960 * balancedPower q y sigma * (1 + Real.log ((q : ℝ) * y)) ^ 5) := by
  have h := Fmean_effective q hy hqy hs
  have hp : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  have hb := (div_le_iff₀ hp).mp h
  exact hb.trans_eq (by unfold balancedPower; ring)

theorem exponential_effective_unnormalized (q : ℕ) [NeZero q] {y sigma : ℝ} (hy : 2 ≤ y)
    (hqy : (q : ℝ) ≤ y) (hs : sigma ∈ Set.Icc (3 / 4) 1) :
    (∑ chi ∈ nonprincipalCharacters q, ∫ t : ℝ,
      ‖NonprincipalDensityAdvance.f chi ((q : ℝ) * y) ((sigma : ℂ) + t * Complex.I)‖ ^ 2 *
        Real.exp (-|t| / y)) ≤
      (q.totient : ℝ) * (2703360 * balancedPower q y sigma * (1 + Real.log ((q : ℝ) * y)) ^ 5) :=
  exponentialMean_unnormalized q _ sigma y _ (exponential_effective q hy hqy hs)

theorem cosine_effective_unnormalized (q : ℕ) [NeZero q] {y sigma : ℝ} (hy : 2 ≤ y)
    (hqy : (q : ℝ) ≤ y) (hs : sigma ∈ Set.Icc (3 / 4) 1) :
    (∑ chi ∈ nonprincipalCharacters q, ∫ t : ℝ,
      ‖cosineDetector chi ((q : ℝ) * y) y ((sigma : ℂ) + t * Complex.I)‖ ^ 2) ≤
      (q.totient : ℝ) * (43253760 * balancedPower q y sigma * (1 + Real.log ((q : ℝ) * y)) ^ 5) := by
  have hp : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  exact ((div_le_iff₀ hp).mp (cosine_effective q hy hqy hs)).trans_eq (mul_comm _ _)

theorem Fmean_effective_unnormalized_q_power (q : ℕ) [NeZero q] {y sigma : ℝ} (hy : 2 ≤ y)
    (hqy : (q : ℝ) ≤ y) (hs : sigma ∈ Set.Icc (3 / 4) 1) :
    (∑ chi ∈ nonprincipalCharacters q, ∫ t in -y..y,
      ‖NonprincipalDensityAdvance.f chi ((q : ℝ) * y) ((sigma : ℂ) + t * Complex.I)‖ ^ 2) ≤
        168960 * (q : ℝ) ^ (2 - 2 * sigma ^ 2) * y ^ ((1 - sigma) * (2 * sigma + 3)) *
          (1 + Real.log ((q : ℝ) * y)) ^ 5 := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hW := (balancedPower_pos hq0 (by linarith : 0 < y) sigma).le
  have hL := Real.log_nonneg (show 1 ≤ (q : ℝ) * y by
    have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
    nlinarith)
  have h := mul_le_mul_of_nonneg_right (Nat.cast_le (α := ℝ) |>.mpr (Nat.totient_le q))
    (by positivity : 0 ≤ 168960 * balancedPower q y sigma * (1 + Real.log ((q : ℝ) * y)) ^ 5)
  apply (Fmean_effective_unnormalized q hy hqy hs).trans (h.trans_eq ?_)
  unfold balancedPower
  rw [show 2 - 2 * sigma ^ 2 = 1 + (1 - 2 * sigma ^ 2) by ring,
    Real.rpow_add hq0, Real.rpow_one]
  ring

end LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.PVEffective
