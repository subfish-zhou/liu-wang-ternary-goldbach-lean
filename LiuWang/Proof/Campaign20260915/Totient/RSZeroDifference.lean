import LiuWang.Proof.Campaign20260915.Totient.RSHighZeros
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Complex Finset BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ChebyshevBound.HighHeight

namespace LiuWang.Proof.Campaign20260915.Totient

def rsZeroPrimitive (m : ℕ) (x : ℝ) (p : RiemannXiDivisorZeroIndex) : ℂ :=
  (x : ℂ) ^ (riemannXiDivisorZeroValue p + (m : ℂ)) /
    ∏ k ∈ range (m + 1), (riemannXiDivisorZeroValue p + (k : ℂ))

def rsZeroMoment (m : ℕ) (L : ℝ) (p : RiemannXiDivisorZeroIndex) : ℝ :=
  Real.exp (((riemannXiDivisorZeroValue p).re - 1) * L) /
    |(riemannXiDivisorZeroValue p).im| ^ (m + 1)

theorem rsZeroPrimitive_deriv (m : ℕ) (p : RiemannXiDivisorZeroIndex)
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y => rsZeroPrimitive (m + 1) y p) (rsZeroPrimitive m x p) x := by
  have hr : riemannXiDivisorZeroValue p + (m : ℂ) ≠ -1 := by
    intro he
    have hi := congrArg Complex.im he
    have ht := xi_zero_height_gt_one p
    simp only [Complex.add_im, Complex.natCast_im, add_zero, Complex.neg_im,
      Complex.one_im, neg_zero] at hi
    simp only [hi, abs_zero] at ht
    linarith
  have hd := (hasDerivAt_ofReal_cpow_const' hx.ne' hr).div_const
    (∏ k ∈ range (m + 1), (riemannXiDivisorZeroValue p + (k : ℂ)))
  convert! hd using 1
  ext y
  simp only [rsZeroPrimitive]
  rw [Finset.prod_range_succ, div_div]
  push_cast
  congr 1 <;> ring

theorem rs_zero_denominator_lower (m : ℕ) (p : RiemannXiDivisorZeroIndex) :
    |(riemannXiDivisorZeroValue p).im| ^ (m + 1) ≤
      ‖∏ k ∈ range (m + 1), (riemannXiDivisorZeroValue p + (k : ℂ))‖ := by
  rw [norm_prod]
  calc
    _ = ∏ _k ∈ range (m + 1), |(riemannXiDivisorZeroValue p).im| := by simp
    _ ≤ _ := prod_le_prod (fun _ _ => abs_nonneg _) (fun k _ => by
      simpa only [Complex.add_im, Complex.natCast_im, add_zero] using
        Complex.abs_im_le_norm (riemannXiDivisorZeroValue p + (k : ℂ)))

theorem rsZeroPrimitive_shift_bound (m k : ℕ) (p : RiemannXiDivisorZeroIndex)
    {x δ : ℝ} (hx : 0 < x) (hδ : 0 ≤ δ) :
    ‖rsZeroPrimitive m (x + (k : ℝ) * (δ * x)) p‖ ≤
      x ^ (m + 1) * ((1 + δ) ^ (m + 1)) ^ k *
        rsZeroMoment m (Real.log x) p := by
  let β := (riemannXiDivisorZeroValue p).re
  let u := 1 + (k : ℝ) * δ
  have hu : 1 ≤ u := by
    have hn : 0 ≤ (k : ℝ) * δ := mul_nonneg (Nat.cast_nonneg k) hδ
    dsimp [u]
    linarith
  have hu0 : 0 < u := by linarith
  have hb := riemannXiDivisorZeroValue_re_mem_Ioo p
  have hbu : β + m ≤ (m + 1 : ℕ) := by dsimp [β]; push_cast; linarith [hb.2]
  have huB : u ≤ (1 + δ) ^ k := one_add_mul_le_pow (by linarith) k
  have hpow : u ^ (β + m) ≤ ((1 + δ) ^ (m + 1)) ^ k := by
    calc
      _ ≤ u ^ ((m + 1 : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hu hbu
      _ = u ^ (m + 1) := Real.rpow_natCast _ _
      _ ≤ ((1 + δ) ^ k) ^ (m + 1) := pow_le_pow_left₀ hu0.le huB _
      _ = _ := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hxpow : x ^ (β + m) =
      x ^ (m + 1) * Real.exp ((β - 1) * Real.log x) := by
    rw [Real.rpow_def_of_pos hx, ← Real.exp_log hx, ← Real.exp_nat_mul]
    rw [← Real.exp_add, Real.log_exp]
    congr 1
    push_cast
    ring
  have ht : 0 < |(riemannXiDivisorZeroValue p).im| :=
    lt_trans (by norm_num) (xi_zero_height_gt_one p)
  have hn : ‖((x + (k : ℝ) * (δ * x) : ℝ) : ℂ) ^
      (riemannXiDivisorZeroValue p + (m : ℂ))‖ ≤
        x ^ (m + 1) * Real.exp ((β - 1) * Real.log x) *
          ((1 + δ) ^ (m + 1)) ^ k := by
    rw [show x + (k : ℝ) * (δ * x) = x * u by dsimp [u]; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos hx hu0),
      Complex.add_re, Complex.natCast_re,
      Real.mul_rpow hx.le hu0.le, hxpow]
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  unfold rsZeroPrimitive
  rw [norm_div]
  calc
    _ ≤ ‖((x + (k : ℝ) * (δ * x) : ℝ) : ℂ) ^
        (riemannXiDivisorZeroValue p + (m : ℂ))‖ /
          |(riemannXiDivisorZeroValue p).im| ^ (m + 1) :=
      div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos ht _)
        (rs_zero_denominator_lower m p)
    _ ≤ _ := (div_le_div_of_nonneg_right hn (by positivity)).trans_eq (by
      dsimp [rsZeroMoment, β]
      ring)

theorem rsZeroPrimitive_difference_bound (m : ℕ) (p : RiemannXiDivisorZeroIndex)
    {x δ : ℝ} (hx : 0 < x) (hδ : 0 ≤ δ) :
    ‖(fwdDiff (δ * x))^[m] (fun y => rsZeroPrimitive m y p) x‖ ≤
      x ^ (m + 1) * (1 + (1 + δ) ^ (m + 1)) ^ m *
        rsZeroMoment m (Real.log x) p := by
  rw [fwdDiff_iter_eq_sum_shift]
  calc
    _ ≤ ∑ k ∈ range (m + 1),
        ‖((-1 : ℤ) ^ (m - k) * m.choose k) •
          rsZeroPrimitive m (x + k • (δ * x)) p‖ := norm_sum_le _ _
    _ = ∑ k ∈ range (m + 1),
        (m.choose k : ℝ) * ‖rsZeroPrimitive m (x + (k : ℝ) * (δ * x)) p‖ := by
      apply sum_congr rfl
      intro k _
      rw [norm_zsmul ℝ]
      simp
    _ ≤ ∑ k ∈ range (m + 1),
        (m.choose k : ℝ) * (x ^ (m + 1) * ((1 + δ) ^ (m + 1)) ^ k *
          rsZeroMoment m (Real.log x) p) := by
      apply sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left (rsZeroPrimitive_shift_bound m k p hx hδ)
        (Nat.cast_nonneg _)
    _ = _ := by
      rw [show 1 + (1 + δ) ^ (m + 1) = (1 + δ) ^ (m + 1) + 1 by ring,
        add_pow ((1 + δ) ^ (m + 1)) 1 m]
      simp only [one_pow, mul_one, Finset.mul_sum, Finset.sum_mul]
      apply sum_congr rfl
      intro k _
      ring

#print axioms rsZeroPrimitive_deriv
#print axioms rs_zero_denominator_lower
#print axioms rsZeroPrimitive_shift_bound
#print axioms rsZeroPrimitive_difference_bound

end LiuWang.Proof.Campaign20260915.Totient
