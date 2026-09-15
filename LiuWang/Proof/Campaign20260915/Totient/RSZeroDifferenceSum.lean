import LiuWang.Proof.Campaign20260915.Totient.RSZeroDifference

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Complex Finset BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ChebyshevBound.HighHeight

namespace LiuWang.Proof.Campaign20260915.Totient

theorem rsZeroMoment_summable {m : ℕ} (hm : 1 ≤ m) {L : ℝ} (hL : 0 ≤ L) :
    Summable (rsZeroMoment m L) := by
  apply Summable.of_nonneg_of_le (fun p => by unfold rsZeroMoment; positivity)
    (f := fun p => 1 / (riemannXiDivisorZeroValue p).im ^ 2) _
    xi_height_inverse_square_summable
  intro p
  have ht := xi_zero_height_gt_one p
  have hs : (riemannXiDivisorZeroValue p).im ^ 2 ≤
      |(riemannXiDivisorZeroValue p).im| ^ (m + 1) := by
    simpa only [sq_abs] using pow_le_pow_right₀ ht.le (show 2 ≤ m + 1 by omega)
  have he : Real.exp (((riemannXiDivisorZeroValue p).re - 1) * L) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (by linarith [(riemannXiDivisorZeroValue_re_mem_Ioo p).2]) hL)
  exact (div_le_div_of_nonneg_right he (by positivity)).trans
    (one_div_le_one_div_of_le
      (sq_pos_of_ne_zero (abs_pos.mp (lt_trans (by norm_num) ht))) hs)

theorem rsZeroPrimitive_summable {m : ℕ} (hm : 1 ≤ m) {x : ℝ} (hx : 1 ≤ x) :
    Summable (rsZeroPrimitive m x) := by
  have hx0 : 0 < x := by linarith
  apply summable_norm_iff.mp
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (f := fun p => x ^ (m + 1) * rsZeroMoment m (Real.log x) p) _
    ((rsZeroMoment_summable hm (Real.log_nonneg hx)).mul_left _)
  intro p
  simpa using rsZeroPrimitive_shift_bound m 0 p hx0 (le_refl (0 : ℝ))

theorem rsZeroPrimitive_iter_summable {m : ℕ} (hm : 1 ≤ m) {h : ℝ}
    (hh : 0 ≤ h) (n : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    Summable (fun p => (fwdDiff h)^[n] (fun y => rsZeroPrimitive m y p) x) := by
  induction n generalizing x with
  | zero => exact rsZeroPrimitive_summable hm hx
  | succ n ih =>
    simpa only [Function.iterate_succ_apply', fwdDiff] using
      (ih (show 1 ≤ x + h by linarith)).sub (ih hx)

theorem rsZeroPrimitive_difference_tsum {m : ℕ} (hm : 1 ≤ m) {h : ℝ}
    (hh : 0 ≤ h) (n : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    (fwdDiff h)^[n] (fun y => ∑' p, rsZeroPrimitive m y p) x =
      ∑' p, (fwdDiff h)^[n] (fun y => rsZeroPrimitive m y p) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change (fwdDiff h)^[n] (fun y => ∑' p, rsZeroPrimitive m y p) (x + h) -
      (fwdDiff h)^[n] (fun y => ∑' p, rsZeroPrimitive m y p) x = _
    rw [ih (by linarith), ih hx, ← (rsZeroPrimitive_iter_summable hm hh n
      (show 1 ≤ x + h by linarith)).tsum_sub (rsZeroPrimitive_iter_summable hm hh n hx)]
    simp only [Function.iterate_succ_apply', fwdDiff]

theorem rsZeroPrimitive_sum_difference_bound {m : ℕ} (hm : 1 ≤ m)
    {x δ : ℝ} (hx : 1 ≤ x) (hδ : 0 ≤ δ) :
    ‖(fwdDiff (δ * x))^[m] (fun y => ∑' p, rsZeroPrimitive m y p) x‖ ≤
      x ^ (m + 1) * (1 + (1 + δ) ^ (m + 1)) ^ m *
        ∑' p, rsZeroMoment m (Real.log x) p := by
  have hx0 : 0 < x := by linarith
  rw [rsZeroPrimitive_difference_tsum hm (mul_nonneg hδ hx0.le) m hx]
  have hs := rsZeroPrimitive_iter_summable hm (mul_nonneg hδ hx0.le) m hx
  have ht := (rsZeroMoment_summable hm (Real.log_nonneg hx)).mul_left
    (x ^ (m + 1) * (1 + (1 + δ) ^ (m + 1)) ^ m)
  exact (norm_tsum_le_tsum_norm hs.norm).trans
    ((hs.norm.tsum_le_tsum (fun p => rsZeroPrimitive_difference_bound m p hx0 hδ) ht).trans_eq
      (tsum_mul_left))

theorem rsZeroPrimitive_normalized_difference_bound {m : ℕ} (hm : 1 ≤ m)
    {x δ : ℝ} (hx : 1 ≤ x) (hδ : 0 < δ) :
    ‖(fwdDiff (δ * x))^[m] (fun y => ∑' p, rsZeroPrimitive m y p) x‖ /
        (δ * x) ^ m ≤
      x * (1 + (1 + δ) ^ (m + 1)) ^ m / δ ^ m *
        ∑' p, rsZeroMoment m (Real.log x) p := by
  have hx0 : 0 < x := by linarith
  apply (div_le_div_of_nonneg_right (rsZeroPrimitive_sum_difference_bound hm hx hδ.le)
    (pow_nonneg (mul_nonneg hδ.le hx0.le) m)).trans_eq
  rw [mul_pow, pow_succ]
  field_simp

#print axioms rsZeroMoment_summable
#print axioms rsZeroPrimitive_summable
#print axioms rsZeroPrimitive_iter_summable
#print axioms rsZeroPrimitive_difference_tsum
#print axioms rsZeroPrimitive_sum_difference_bound
#print axioms rsZeroPrimitive_normalized_difference_bound

end LiuWang.Proof.Campaign20260915.Totient
