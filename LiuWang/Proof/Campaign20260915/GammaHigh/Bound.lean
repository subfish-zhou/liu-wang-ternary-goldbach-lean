import LiuWang.Proof.ZeroRegionFamily.Sharp.Gamma

set_option autoImplicit false
noncomputable section

open Complex Finset Filter
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.Campaign20260915.GammaHigh

theorem reciprocal_reverse_product_bound {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (y : ℝ) :
    a / (a ^ 2 + y ^ 2) - b / (b ^ 2 + y ^ 2) ≤ (b - a) / (a * b) := by
  have hb : 0 < b := ha.trans_le hab
  have hA : 0 < a ^ 2 + y ^ 2 := by positivity
  have hB : 0 < b ^ 2 + y ^ 2 := by positivity
  have he : a / (a ^ 2 + y ^ 2) - b / (b ^ 2 + y ^ 2) =
      (b - a) * (a * b - y ^ 2) / ((a ^ 2 + y ^ 2) * (b ^ 2 + y ^ 2)) := by
    field_simp
    ring
  have hbound : a * b * (a * b - y ^ 2) ≤
      (a ^ 2 + y ^ 2) * (b ^ 2 + y ^ 2) := by
    nlinarith [mul_nonneg (sq_nonneg y)
      (show 0 ≤ a ^ 2 + b ^ 2 + a * b + y ^ 2 by positivity)]
  rw [he, div_le_div_iff₀ (mul_pos hA hB) (mul_pos ha hb)]
  have hh := mul_le_mul_of_nonneg_left hbound (sub_nonneg.mpr hab)
  nlinarith only [hh]

theorem sum_reference_product_le {b : ℝ} (hb : 3 / 2 ≤ b) (n : ℕ) :
    ∑ j ∈ range n, 1 / (((j : ℝ) + 1) * ((j : ℝ) + b)) ≤ 5 / 3 := by
  cases n with
  | zero => norm_num
  | succ n =>
    rw [sum_range_succ']
    have htail :
        ∑ j ∈ range n, 1 / (((↑(j + 1) : ℝ) + 1) * ((↑(j + 1) : ℝ) + b)) ≤
          ∑ j ∈ range n, (1 / ((j : ℝ) + 1) - 1 / ((↑(j + 1) : ℝ) + 1)) := by
      apply sum_le_sum
      intro j _
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
      have he : 1 / ((j : ℝ) + 1) - 1 / ((↑(j + 1) : ℝ) + 1) =
          1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
        push_cast
        field_simp
        ring
      rw [he]
      apply one_div_le_one_div_of_le (by positivity)
      push_cast
      nlinarith
    rw [sum_range_sub'] at htail
    have hhead : 1 / b ≤ 2 / 3 := by
      apply (div_le_iff₀ (by linarith)).mpr
      linarith
    norm_num only [Nat.cast_zero, zero_add, one_mul, div_one] at *
    linarith [show 0 ≤ 1 / ((n : ℝ) + 1) by positivity]

theorem digamma_shift_up_from_one {b : ℝ} (hb : 3 / 2 ≤ b) (y : ℝ) :
    (digamma ((b : ℂ) + I * y)).re - (digamma (1 + I * y)).re ≤
      5 / 3 * (b - 1) := by
  have hs := digamma_difference_hasSum (show 0 < b by linarith) zero_lt_one y
  norm_num only [Complex.ofReal_one] at hs
  apply le_of_tendsto hs.tendsto_sum_nat
  apply Filter.Eventually.of_forall
  intro n
  calc
    _ ≤ ∑ j ∈ range n, (b - 1) *
        (1 / (((j : ℝ) + 1) * ((j : ℝ) + b))) := by
      apply sum_le_sum
      intro j _
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
      have hh := reciprocal_reverse_product_bound
        (a := (j : ℝ) + 1) (b := (j : ℝ) + b) (by positivity) (by linarith) y
      convert! hh using 1
      ring
    _ = (b - 1) * ∑ j ∈ range n, 1 / (((j : ℝ) + 1) * ((j : ℝ) + b)) := by
      rw [mul_sum]
    _ ≤ (b - 1) * (5 / 3) :=
      mul_le_mul_of_nonneg_left (sum_reference_product_le hb n) (by linarith)
    _ = _ := by ring

theorem digamma_shift_down_from_one {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (y : ℝ) :
    (digamma ((a : ℂ) + I * y)).re - (digamma ((b : ℂ) + I * y)).re ≤
      (b - a) / 2 := by
  have ha0 : 0 < a := by linarith
  have hs := digamma_difference_hasSum ha0 (ha0.trans_le hab) y
  apply le_of_tendsto hs.tendsto_sum_nat
  apply Filter.Eventually.of_forall
  intro n
  calc
    _ ≤ ∑ j ∈ range n, (b - a) / 4 * (1 / ((j : ℝ) + a) ^ 2) := by
      apply sum_le_sum
      intro j _
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
      have hh := reciprocal_difference_le (a := (j : ℝ) + a) (b := (j : ℝ) + b)
        (by linarith) (by linarith) y
      convert! hh using 1
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = (b - a) / 4 * ∑ j ∈ range n, 1 / ((j : ℝ) + a) ^ 2 := by rw [mul_sum]
    _ ≤ (b - a) / 4 * 2 :=
      mul_le_mul_of_nonneg_left (sum_shift_square_le_two ha n) (by positivity)
    _ = _ := by ring

theorem shifted_digamma_bound {sigma : ℝ}
    (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (t : ℝ) :
    ((digamma (((sigma : ℂ) + I * t) / 2 + 1)).re -
      stechkinK * (digamma (((stechkinSigma sigma : ℂ) + I * t) / 2 + 1)).re) / 2 ≤
        stechkinConductorCoeff * Real.log (max 1 |t|) + (23 - 19 * stechkinK) / 48 := by
  have hge := stechkinSigma_ge hs
  have hgap := stechkinSigma_sub_le hs
  have hu := digamma_shift_up_from_one (b := sigma / 2 + 1) (by linarith) (t / 2)
  have hl := digamma_shift_down_from_one
    (a := sigma / 2 + 1) (b := stechkinSigma sigma / 2 + 1)
    (by linarith) (by linarith) (t / 2)
  have href := digamma_one_re_le_log_max (t / 2)
  have hlog : 2 * |t / 2| = |t| := by rw [abs_div]; norm_num; ring
  rw [hlog] at href
  have ha : (digamma (((sigma / 2 + 1 : ℝ) : ℂ) + I * (t / 2 : ℝ))).re ≤
      Real.log (max 1 |t|) + 23 / 24 := by linarith
  have h1 := mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr stechkinK_mem.2)
  have h2 := mul_le_mul_of_nonneg_left hl stechkinK_mem.1
  have h3 := mul_le_mul_of_nonneg_left hgap stechkinK_mem.1
  have hcast (u : ℝ) : ((u : ℂ) + I * t) / 2 + 1 =
      (((u / 2 + 1 : ℝ) : ℂ) + I * (t / 2 : ℝ)) := by push_cast; ring
  rw [hcast, hcast]
  dsimp [stechkinConductorCoeff]
  nlinarith

theorem shifted_digamma_high {sigma t : ℝ}
    (hs : sigma ∈ Set.Ioo (1 : ℝ) 1.15) (ht : 1 ≤ |t|) :
    ((digamma (((sigma : ℂ) + I * t) / 2 + 1)).re -
      stechkinK * (digamma (((stechkinSigma sigma : ℂ) + I * t) / 2 + 1)).re) / 2 <
        stechkinConductorCoeff * Real.log |t| + 0.3316 := by
  have hb := shifted_digamma_bound hs.1 (by linarith [hs.2]) t
  rw [max_eq_right ht] at hb
  linarith [stechkinK_ge]

#print axioms shifted_digamma_high

end LiuWang.Proof.Campaign20260915.GammaHigh
