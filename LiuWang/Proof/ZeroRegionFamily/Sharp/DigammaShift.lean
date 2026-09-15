import LiuWang.Proof.ZeroRegionFamily.Sharp.DigammaReference

/-! # 同高度digamma实部平移：差核先抵消再估计 -/

set_option autoImplicit false
noncomputable section

open Complex Finset Filter
open scoped Topology

namespace LiuWang.Proof.ZeroRegionFamily.Sharp

theorem reciprocal_difference_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (y : ℝ) :
    b/(b^2+y^2)-a/(a^2+y^2) ≤ (b-a)/(4*a^2) := by
  have hb : 0 < b := ha.trans_le hab
  have hA : 0 < a^2+y^2 := by positivity
  have hB : 0 < b^2+y^2 := by positivity
  have he : b/(b^2+y^2)-a/(a^2+y^2) =
      (b-a)*(y^2-a*b)/((a^2+y^2)*(b^2+y^2)) := by field_simp; ring
  have hdiff : 0 ≤ b^2-a^2 := by nlinarith
  have hbound : 4*a^2*(y^2-a*b) ≤ (a^2+y^2)*(b^2+y^2) := by
    have hp := mul_nonneg (show 0 ≤ a^2+y^2 by positivity) hdiff
    have hab0 : 0 ≤ a^3*b := by positivity
    nlinarith [sq_nonneg (a^2-y^2)]
  rw [he, div_le_div_iff₀ (mul_pos hA hB) (by positivity)]
  have hh := mul_le_mul_of_nonneg_left hbound (sub_nonneg.mpr hab)
  nlinarith

theorem reciprocal_reverse_difference_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (y : ℝ) :
    a/(a^2+y^2)-b/(b^2+y^2) ≤ (b-a)/a^2 := by
  have hb : 0 < b := ha.trans_le hab
  have hA : 0 < a^2+y^2 := by positivity
  have hB : 0 < b^2+y^2 := by positivity
  have he : a/(a^2+y^2)-b/(b^2+y^2) =
      (b-a)*(a*b-y^2)/((a^2+y^2)*(b^2+y^2)) := by field_simp; ring
  have hbound : a^2*(a*b-y^2) ≤ (a^2+y^2)*(b^2+y^2) := by
    have hprod : a*b ≤ b^2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hprod (sq_nonneg a)
    have hyy : 0 ≤ y^2*(a^2+b^2+y^2) := by positivity
    nlinarith
  rw [he, div_le_div_iff₀ (mul_pos hA hB) (by positivity)]
  have hh := mul_le_mul_of_nonneg_left hbound (sub_nonneg.mpr hab)
  nlinarith

theorem sum_shift_square_le {a : ℝ} (ha : 1/2 ≤ a) (n : ℕ) :
    ∑ j ∈ range n, 1/((j : ℝ)+a)^2 ≤ 5 := by
  cases n with
  | zero => norm_num
  | succ n =>
    rw [sum_range_succ']
    have htail : ∑ j ∈ range n, 1/((↑(j+1) : ℝ)+a)^2 ≤
        ∑ j ∈ range n, (1/((j : ℝ)+1)-1/((↑(j+1) : ℝ)+1)) := by
      apply sum_le_sum
      intro j _
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
      have he : 1/((j : ℝ)+1)-1/((↑(j+1) : ℝ)+1) =
          1/(((j : ℝ)+1)*((j : ℝ)+2)) := by push_cast; field_simp; ring
      rw [he]
      apply one_div_le_one_div_of_le (by positivity)
      push_cast
      nlinarith [sq_nonneg a]
    rw [sum_range_sub'] at htail
    have hhead : 1/a^2 ≤ 4 := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith [sq_nonneg (a-1/2)]
    norm_num only [Nat.cast_zero, zero_add, div_one] at *
    linarith [show 0 ≤ 1/((n : ℝ)+1) by positivity]

theorem sum_shift_square_le_two {a : ℝ} (ha : 1 ≤ a) (n : ℕ) :
    ∑ j ∈ range n, 1/((j : ℝ)+a)^2 ≤ 2 := by
  cases n with
  | zero => norm_num
  | succ n =>
    rw [sum_range_succ']
    have htail : ∑ j ∈ range n, 1/((↑(j+1) : ℝ)+a)^2 ≤
        ∑ j ∈ range n, (1/((j : ℝ)+1)-1/((↑(j+1) : ℝ)+1)) := by
      apply sum_le_sum
      intro j _
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
      have he : 1/((j : ℝ)+1)-1/((↑(j+1) : ℝ)+1) =
          1/(((j : ℝ)+1)*((j : ℝ)+2)) := by push_cast; field_simp; ring
      rw [he]
      apply one_div_le_one_div_of_le (by positivity)
      push_cast
      nlinarith [sq_nonneg a]
    rw [sum_range_sub'] at htail
    have hhead : 1/a^2 ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      nlinarith [sq_nonneg (a-1)]
    norm_num only [Nat.cast_zero, zero_add, div_one] at *
    linarith [show 0 ≤ 1/((n : ℝ)+1) by positivity]

theorem digamma_difference_hasSum {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (y : ℝ) :
    HasSum (fun n : ℕ =>
      ((n : ℝ)+b)/(((n : ℝ)+b)^2+y^2)-
        ((n : ℝ)+a)/(((n : ℝ)+a)^2+y^2))
      ((Complex.digamma ((a : ℂ)+Complex.I*y)).re-
        (Complex.digamma ((b : ℂ)+Complex.I*y)).re) := by
  have hp (u : ℝ) (hu : 0 < u) : ∀ n : ℕ, (u : ℂ)+Complex.I*y ≠ -(n : ℂ) := by
    intro n hn
    have h := congrArg Complex.re hn
    simp [Complex.mul_re] at h
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    linarith
  have h := (Complex.hasSum_re (Complex.hasSum_digamma (hp a ha))).sub
    (Complex.hasSum_re (Complex.hasSum_digamma (hp b hb)))
  simp only [Complex.add_re, Complex.ofReal_re] at h
  convert! h using 1
  · funext n
    simp [one_div, Complex.inv_re, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  · ring

theorem digamma_shift_down_le {a b : ℝ} (ha : 1/2 ≤ a) (hab : a ≤ b) (y : ℝ) :
    (Complex.digamma ((a : ℂ)+Complex.I*y)).re-
      (Complex.digamma ((b : ℂ)+Complex.I*y)).re ≤ 5*(b-a)/4 := by
  have ha0 : 0 < a := by linarith
  have hs := digamma_difference_hasSum ha0 (ha0.trans_le hab) y
  apply le_of_tendsto hs.tendsto_sum_nat
  apply Filter.Eventually.of_forall
  intro n
  calc
    _ ≤ ∑ j ∈ range n, (b-a)/4*(1/((j : ℝ)+a)^2) := by
      apply sum_le_sum
      intro j _
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
      have hh := reciprocal_difference_le (a := (j : ℝ)+a) (b := (j : ℝ)+b)
        (by linarith) (by linarith) y
      convert! hh using 1
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = (b-a)/4*∑ j ∈ range n, 1/((j : ℝ)+a)^2 := by rw [mul_sum]
    _ ≤ (b-a)/4*5 := mul_le_mul_of_nonneg_left (sum_shift_square_le ha n) (by positivity)
    _ = _ := by ring

theorem digamma_shift_up_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (y : ℝ) :
    (Complex.digamma ((b : ℂ)+Complex.I*y)).re-
      (Complex.digamma ((a : ℂ)+Complex.I*y)).re ≤ 2*(b-a) := by
  have ha0 : 0 < a := by linarith
  have hs := digamma_difference_hasSum (ha0.trans_le hab) ha0 y
  apply le_of_tendsto hs.tendsto_sum_nat
  apply Filter.Eventually.of_forall
  intro n
  calc
    _ ≤ ∑ j ∈ range n, (b-a)*(1/((j : ℝ)+a)^2) := by
      apply sum_le_sum
      intro j _
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
      have hh := reciprocal_reverse_difference_le (a := (j : ℝ)+a) (b := (j : ℝ)+b)
        (by linarith) (by linarith) y
      convert! hh using 1
      ring
    _ = (b-a)*∑ j ∈ range n, 1/((j : ℝ)+a)^2 := by rw [mul_sum]
    _ ≤ (b-a)*2 := mul_le_mul_of_nonneg_left (sum_shift_square_le_two ha n) (by positivity)
    _ = _ := by ring

end LiuWang.Proof.ZeroRegionFamily.Sharp
