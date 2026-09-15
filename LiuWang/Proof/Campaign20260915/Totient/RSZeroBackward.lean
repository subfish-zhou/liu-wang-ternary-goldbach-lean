import LiuWang.Proof.Campaign20260915.Totient.RSZeroDifferenceSum
import LiuWang.Proof.Campaign20260915.Totient.RSPsiBox

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Complex Finset BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.Campaign20260915.Totient

theorem rsZeroPrimitive_norm_mono (m : ℕ) (p : RiemannXiDivisorZeroIndex)
    {t x : ℝ} (ht : 0 < t) (htx : t ≤ x) :
    ‖rsZeroPrimitive m t p‖ ≤ ‖rsZeroPrimitive m x p‖ := by
  unfold rsZeroPrimitive
  rw [norm_div, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht,
    Complex.norm_cpow_eq_rpow_re_of_pos (ht.trans_le htx)]
  apply Real.rpow_le_rpow ht.le htx
  simp only [Complex.add_re, Complex.natCast_re]
  exact add_nonneg (riemannXiDivisorZeroValue_re_mem_Ioo p).1.le (Nat.cast_nonneg m)

theorem rsZeroPrimitive_backward_bound (m : ℕ) (p : RiemannXiDivisorZeroIndex)
    {x h : ℝ} (hh : 0 ≤ h) (hleft : 0 < x - (m : ℝ) * h) :
    ‖(fwdDiff h)^[m] (fun y => rsZeroPrimitive m y p) (x - (m : ℝ) * h)‖ ≤
      x ^ (m + 1) * 2 ^ m * rsZeroMoment m (Real.log x) p := by
  have hmh : 0 ≤ (m : ℝ) * h := mul_nonneg (Nat.cast_nonneg m) hh
  have hx : 0 < x := by linarith
  have hpoint (k : ℕ) (hk : k ∈ range (m + 1)) :
      ‖rsZeroPrimitive m (x - (m : ℝ) * h + k • h) p‖ ≤
        x ^ (m + 1) * rsZeroMoment m (Real.log x) p := by
    have hkm : (k : ℝ) ≤ m := by exact_mod_cast (show k ≤ m by simpa using hk)
    have hkh : (k : ℝ) * h ≤ (m : ℝ) * h := mul_le_mul_of_nonneg_right hkm hh
    have hk0 : 0 ≤ (k : ℝ) * h := mul_nonneg (Nat.cast_nonneg k) hh
    have hn := rsZeroPrimitive_norm_mono m p
      (show 0 < x - (m : ℝ) * h + k • h by simpa only [nsmul_eq_mul] using
        (show 0 < x - (m : ℝ) * h + (k : ℝ) * h by linarith))
      (show x - (m : ℝ) * h + k • h ≤ x by
        simpa only [nsmul_eq_mul] using (show x - (m : ℝ) * h + (k : ℝ) * h ≤ x by linarith))
    exact hn.trans (by simpa using rsZeroPrimitive_shift_bound m 0 p hx (le_refl (0 : ℝ)))
  rw [fwdDiff_iter_eq_sum_shift]
  calc
    _ ≤ ∑ k ∈ range (m + 1),
        ‖((-1 : ℤ) ^ (m - k) * m.choose k) •
          rsZeroPrimitive m (x - (m : ℝ) * h + k • h) p‖ := norm_sum_le _ _
    _ = ∑ k ∈ range (m + 1),
        (m.choose k : ℝ) * ‖rsZeroPrimitive m (x - (m : ℝ) * h + k • h) p‖ := by
      apply sum_congr rfl
      intro k _
      rw [norm_zsmul ℝ]
      simp
    _ ≤ ∑ k ∈ range (m + 1),
        (m.choose k : ℝ) * (x ^ (m + 1) * rsZeroMoment m (Real.log x) p) :=
      sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (hpoint k hk) (Nat.cast_nonneg _))
    _ = _ := by
      rw [← sum_mul]
      have hc : (∑ k ∈ range (m + 1), (m.choose k : ℝ)) = 2 ^ m := by
        exact_mod_cast Nat.sum_range_choose m
      rw [hc]
      ring

theorem rsZeroPrimitive_sum_backward_bound {m : ℕ} (hm : 1 ≤ m)
    {x h : ℝ} (hh : 0 ≤ h) (hleft : 1 ≤ x - (m : ℝ) * h) :
    ‖(fwdDiff h)^[m] (fun y => ∑' p, rsZeroPrimitive m y p) (x - (m : ℝ) * h)‖ ≤
      x ^ (m + 1) * 2 ^ m * ∑' p, rsZeroMoment m (Real.log x) p := by
  have hmh : 0 ≤ (m : ℝ) * h := mul_nonneg (Nat.cast_nonneg m) hh
  have hx : 1 ≤ x := by linarith
  rw [rsZeroPrimitive_difference_tsum hm hh m hleft]
  have hs := rsZeroPrimitive_iter_summable hm hh m hleft
  have ht := (rsZeroMoment_summable hm (Real.log_nonneg hx)).mul_left
    (x ^ (m + 1) * 2 ^ m)
  exact (norm_tsum_le_tsum_norm hs.norm).trans
    ((hs.norm.tsum_le_tsum
      (fun p => rsZeroPrimitive_backward_bound m p hh (by linarith)) ht).trans_eq tsum_mul_left)

theorem rsZeroPrimitive_original_backward {m : ℕ} (hm : 1 ≤ m)
    {δ a x : ℝ} (hδ : 0 < δ) (ha : 0 < a)
    (hcut : 1 + (m : ℝ) * δ * a < a) (hax : a ≤ x) :
    ‖(fwdDiff (δ * x))^[m] (fun y => ∑' p, rsZeroPrimitive m y p)
        (x - (m : ℝ) * (δ * x))‖ / (δ * x) ^ m ≤
      x * 2 ^ m / δ ^ m * ∑' p, rsZeroMoment m (Real.log x) p := by
  have hd := rsPsiBox_original_domain hδ ha hcut hax
  have hx : 0 < x := ha.trans_le hax
  apply (div_le_div_of_nonneg_right
    (rsZeroPrimitive_sum_backward_bound hm hd.1.le hd.2.le)
    (pow_nonneg hd.1.le m)).trans_eq
  rw [mul_pow, pow_succ]
  field_simp

#print axioms rsZeroPrimitive_norm_mono
#print axioms rsZeroPrimitive_backward_bound
#print axioms rsZeroPrimitive_sum_backward_bound
#print axioms rsZeroPrimitive_original_backward

end LiuWang.Proof.Campaign20260915.Totient
