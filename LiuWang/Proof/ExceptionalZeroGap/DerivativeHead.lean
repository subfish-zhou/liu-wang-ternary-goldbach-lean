import LiuWang.Proof.ExceptionalZeroGap.DerivativeTail

/-!
# 完整有限头及头尾合并

保留 `n=2,3`；从第四项开始积分 `log t / t`，因此保留
负项 `-(log 3)^2/2`。实数截断点不替换为整数。
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.ExceptionalZeroGap

open Complex Finset
open DirichletLAbelWeightVariation

def finiteHeadBudget (y : ℝ) : ℝ :=
  (1 / 2) * (Real.log y) ^ 2 - (1 / 2) * (Real.log 3) ^ 2 +
    Real.log 3 / 3 + Real.log 2 / 2

theorem two_le_log_of_ten_le {y : ℝ} (hy : 10 ≤ y) : 2 ≤ Real.log y := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3 ^ 2)
    (show (3 : ℝ) ^ 2 ≤ y by linarith)
  rw [Real.log_pow] at h
  norm_num at h
  linarith [Real.log_three_gt_d9]

theorem integral_log_div {b : ℝ} (hb : 3 ≤ b) :
    (∫ t in (3 : ℝ)..b, Real.log t / t) =
      (1 / 2) * (Real.log b) ^ 2 - (1 / 2) * (Real.log 3) ^ 2 := by
  have hn (t : ℝ) (ht : t ∈ Set.uIcc 3 b) : t ≠ 0 := by
    rw [Set.uIcc_of_le hb] at ht
    linarith [ht.1]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => (1 / 2) * (Real.log t) ^ 2)
  · intro t ht
    convert! ((Real.hasDerivAt_log (hn t ht)).pow 2).const_mul (1 / 2) using 1
    simp [div_eq_mul_inv]
    ring
  · apply ContinuousOn.intervalIntegrable
    intro t ht
    exact ((Real.continuousAt_log (hn t ht)).div continuousAt_id (hn t ht)).continuousWithinAt

theorem sum_log_div_le_finiteHeadBudget {y : ℝ} (hy : 10 ≤ y) :
    (∑ k ∈ range (⌊y⌋₊ + 1), Real.log (k : ℝ) / k) ≤ finiteHeadBudget y := by
  have hm : 3 ≤ ⌊y⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hmR : (3 : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast hm
  have hmono : AntitoneOn (fun t : ℝ => Real.log t / t) (Set.Ici 3) := by
    intro a ha b hb hab
    have h := antitoneOn_realLogWeight (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (0 : ℝ) < 3) (by linarith [Real.log_three_gt_d9]) ha hb hab
    simpa [realLogWeight, Real.rpow_neg_one, div_eq_mul_inv] using h
  have hsum := (hmono.mono (show Set.Icc (3 : ℝ) ⌊y⌋₊ ⊆ Set.Ici 3 from
    fun _ ht => ht.1)).sum_le_integral_Ico hm
  norm_num only [Nat.cast_ofNat] at hsum
  rw [integral_log_div hmR] at hsum
  have htail :
      (∑ k ∈ Ico 4 (⌊y⌋₊ + 1), Real.log (k : ℝ) / k) ≤
        (1 / 2) * (Real.log (⌊y⌋₊ : ℝ)) ^ 2 - (1 / 2) * (Real.log 3) ^ 2 := by
    simpa only [sum_Ico_add' (fun k : ℕ => Real.log (k : ℝ) / k) 3 ⌊y⌋₊ 1] using hsum
  rw [← sum_range_add_sum_Ico _ (by omega : 4 ≤ ⌊y⌋₊ + 1)]
  have hsmall : (∑ k ∈ range 4, Real.log (k : ℝ) / k) =
      Real.log 2 / 2 + Real.log 3 / 3 := by
    norm_num [sum_range_succ]
  rw [hsmall]
  have hlog := Real.log_le_log (by linarith : (0 : ℝ) < ⌊y⌋₊)
    (Nat.floor_le (by linarith : 0 ≤ y))
  have hlog0 := Real.log_nonneg (show (1 : ℝ) ≤ ⌊y⌋₊ by linarith)
  unfold finiteHeadBudget
  nlinarith

theorem realLogWeight_eq_log_div_mul {σ t : ℝ} (ht : 0 < t) :
    realLogWeight σ t = (Real.log t / t) * t ^ (1 - σ) := by
  rw [realLogWeight, show (1 - σ : ℝ) = -σ + 1 by ring, Real.rpow_add_one ht.ne']
  field_simp

theorem realLogWeight_antitone_exponent {σ τ t : ℝ}
    (hτσ : τ ≤ σ) (ht : 1 ≤ t) :
    realLogWeight σ t ≤ realLogWeight τ t := by
  unfold realLogWeight
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le ht (neg_le_neg hτσ)) (Real.log_nonneg ht)

theorem sum_realLogWeight_le {σ y : ℝ} (hσ : σ ≤ 1) (hy : 10 ≤ y) :
    (∑ k ∈ range (⌊y⌋₊ + 1), realLogWeight σ k) ≤
      y ^ (1 - σ) * finiteHeadBudget y := by
  calc
    _ ≤ ∑ k ∈ range (⌊y⌋₊ + 1),
        y ^ (1 - σ) * (Real.log (k : ℝ) / k) := by
      apply sum_le_sum
      intro k hk
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simp [realLogWeight]
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
      rw [realLogWeight_eq_log_div_mul hkR, mul_comm]
      apply mul_le_mul_of_nonneg_right
      · apply Real.rpow_le_rpow hkR.le _ (sub_nonneg.mpr hσ)
        exact (show (k : ℝ) ≤ ⌊y⌋₊ by exact_mod_cast (by
          have := mem_range.mp hk
          omega : k ≤ ⌊y⌋₊)).trans (Nat.floor_le (by linarith))
      · exact div_nonneg (Real.log_natCast_nonneg _) hkR.le
    _ = y ^ (1 - σ) * ∑ k ∈ range (⌊y⌋₊ + 1), Real.log (k : ℝ) / k :=
      (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_log_div_le_finiteHeadBudget hy)
      (Real.rpow_nonneg (by linarith) _)

variable {r : ℕ} [NeZero r]

omit [NeZero r] in
theorem norm_derivative_head_le_of_le (χ : DirichletCharacter ℂ r)
    {σ τ y : ℝ} (hτσ : τ ≤ σ) (hτ : τ ≤ 1) (hy : 10 ≤ y) :
    ‖∑ k ∈ range (⌊y⌋₊ + 1), logCpowWeight (σ : ℂ) k * χ k‖ ≤
      y ^ (1 - τ) * finiteHeadBudget y := by
  refine (norm_sum_le _ _).trans ((sum_le_sum (fun k _ => ?_)).trans
    (sum_realLogWeight_le hτ hy))
  rw [norm_mul, logCpowWeight_ofReal (Nat.cast_nonneg k), norm_neg,
    Complex.norm_real, Real.norm_eq_abs]
  have hk : 0 ≤ realLogWeight σ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [realLogWeight]
    · exact realLogWeight_nonneg σ (by exact_mod_cast hk)
  rw [abs_of_nonneg hk]
  refine (mul_le_of_le_one_right hk (χ.norm_le_one _)).trans ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp [realLogWeight]
  · exact realLogWeight_antitone_exponent hτσ (by exact_mod_cast hk0)

omit [NeZero r] in
theorem norm_derivative_head_le (χ : DirichletCharacter ℂ r)
    {σ y : ℝ} (hσ : σ ≤ 1) (hy : 10 ≤ y) :
    ‖∑ k ∈ range (⌊y⌋₊ + 1), logCpowWeight (σ : ℂ) k * χ k‖ ≤
      y ^ (1 - σ) * finiteHeadBudget y :=
  norm_derivative_head_le_of_le χ le_rfl hσ hy

/-- 完整真实头尾界；尚未做 `y=13 sqrt r` 的数值吸收。 -/
theorem norm_deriv_le_complete_head_tail_of_le {χ : DirichletCharacter ℂ r}
    (hχ : χ.IsPrimitive) (hr : 987 ≤ r) {σ τ y : ℝ}
    (hτ0 : 1 / 2 ≤ τ) (hτ1 : τ ≤ 1) (hτσ : τ ≤ σ) (hy : 10 ≤ y) :
    ‖deriv χ.LFunction (σ : ℂ)‖ ≤
      (finiteHeadBudget y + Real.sqrt r * Real.log r * Real.log y / y) *
        y ^ (1 - τ) := by
  have htail := norm_deriv_sub_sum_floor_le hχ hr
    (by linarith : 0 < σ) (by linarith : 1 ≤ y)
    (by nlinarith [two_le_log_of_ten_le hy] : 1 ≤ σ * Real.log y)
  have htail' : Real.sqrt r * Real.log r * (Real.log y / y ^ σ) ≤
      Real.sqrt r * Real.log r * (Real.log y / y ^ τ) := by
    simp only [div_eq_mul_inv, ← Real.rpow_neg (by linarith : 0 ≤ y)]
    exact mul_le_mul_of_nonneg_left
      (realLogWeight_antitone_exponent hτσ (by linarith))
      (mul_nonneg (Real.sqrt_nonneg _) (Real.log_natCast_nonneg _))
  have hhead := norm_derivative_head_le_of_le χ hτσ hτ1 hy
  have htri := norm_add_le
    (deriv χ.LFunction (σ : ℂ) -
      ∑ k ∈ range (⌊y⌋₊ + 1), logCpowWeight (σ : ℂ) k * χ k)
    (∑ k ∈ range (⌊y⌋₊ + 1), logCpowWeight (σ : ℂ) k * χ k)
  rw [sub_add_cancel] at htri
  refine (htri.trans (add_le_add (htail.trans htail') hhead)).trans_eq ?_
  rw [div_eq_mul_inv (Real.log y), ← Real.rpow_neg (by linarith : 0 ≤ y), ← realLogWeight,
    realLogWeight_eq_log_div_mul (by linarith : 0 < y)]
  ring

theorem norm_deriv_le_complete_head_tail {χ : DirichletCharacter ℂ r}
    (hχ : χ.IsPrimitive) (hr : 987 ≤ r) {σ y : ℝ}
    (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) (hy : 10 ≤ y) :
    ‖deriv χ.LFunction (σ : ℂ)‖ ≤
      (finiteHeadBudget y + Real.sqrt r * Real.log r * Real.log y / y) *
        y ^ (1 - σ) :=
  norm_deriv_le_complete_head_tail_of_le hχ hr hσ0 hσ1 le_rfl hy

end LiuWang.Proof.ExceptionalZeroGap
