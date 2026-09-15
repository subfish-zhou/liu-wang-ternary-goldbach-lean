import LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.Continuation.Effective.HBoundary

/-! Fixed-X logarithmic costs at independently perturbed heights. -/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.NonprincipalDensityAdvance
open LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.PVContinuation

namespace LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.PVEffective

theorem balancedPower_antitone {q y a b : ℝ} (hq : 1 ≤ q) (hy : 1 ≤ y)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    balancedPower q y b ≤ balancedPower q y a := by
  have hab2 : a ^ 2 ≤ b ^ 2 := sq_le_sq₀ ha (ha.trans hab) |>.mpr hab
  unfold balancedPower
  apply mul_le_mul
  · exact Real.rpow_le_rpow_of_exponent_le hq (by nlinarith)
  · exact Real.rpow_le_rpow_of_exponent_le hy (by nlinarith)
  · exact Real.rpow_nonneg (by linarith) _
  · exact Real.rpow_nonneg (by linarith) _

theorem logSideDifference_effective_all_heights (q : ℕ) [NeZero q]
    {y sigma u : ℝ} (hy : 2 ≤ y) (hqy : (q : ℝ) ≤ y)
    (hs : sigma ∈ Set.Icc (3 / 4) 1) (hu : 0 ≤ u) :
    logSideDifference q ((q : ℝ) * y) sigma u ≤
      (1 + u / y) ^ 3 *
        (169024 * balancedPower q y sigma * (1 + Real.log ((q : ℝ) * y)) ^ 5) := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hy0 : 0 < y := by linarith
  have hW := (balancedPower_pos hq0 hy0 sigma).le
  have hL := Real.log_nonneg (show 1 ≤ (q : ℝ) * y by nlinarith)
  by_cases hsmall : q ≤ 2
  · have he : q = 1 ∨ q = 2 := by have := NeZero.pos q; omega
    rcases he with rfl | rfl <;> simp only [logSideDifference, nonprincipalCharacters_one,
      nonprincipalCharacters_two, Finset.sum_empty, zero_div] <;> positivity
  have hq3 : 3 ≤ q := by omega
  have hq3r : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hX : 5 ≤ (q : ℝ) * y := by nlinarith
  let k := 1 + u / y
  have hk : 1 ≤ k := (height_scale hy0 hu).1
  have hk3 : k ≤ k ^ 3 := by simpa only [pow_one] using pow_le_pow_right₀ hk (by norm_num : 1 ≤ 3)
  have huy : u ≤ k ^ 3 * y :=
    (height_scale hy0 hu).2.1.trans (mul_le_mul_of_nonneg_right hk3 hy0.le)
  have hr : nonprincipalRatio q * (16 * u / ((q : ℝ) * y - 1) ^ 2) ≤
      k ^ 3 * (nonprincipalRatio q * (16 * y / ((q : ℝ) * y - 1) ^ 2)) := by
    have h := mul_le_mul_of_nonneg_left huy
      (by unfold nonprincipalRatio; positivity :
        0 ≤ nonprincipalRatio q * (16 / ((q : ℝ) * y - 1) ^ 2))
    calc
      _ = (nonprincipalRatio q * (16 / ((q : ℝ) * y - 1) ^ 2)) * u := by ring
      _ ≤ _ := h
      _ = _ := by ring
  have hR := hr.trans (mul_le_mul_of_nonneg_left (right_log_cost_effective q hy hs)
    (show 0 ≤ k ^ 3 by positivity))
  have hF := Fmean_effective_all_heights q hy hqy hs hu
  have h := (logSideDifference_le q hX sigma hu).trans (add_le_add hF hR)
  exact h.trans_eq (by dsimp [k]; ring)

end LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.PVEffective
