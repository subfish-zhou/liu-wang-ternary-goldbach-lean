import LiuWang.Proof.Campaign20260915.Totient.RSTrivialKernel

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open MeasureTheory Set Finset

namespace LiuWang.Proof.Campaign20260915.Totient

theorem rs_difference_congr_positive {E : Type*} [AddCommGroup E]
    {f g : ℝ → E} (he : ∀ x, 1 < x → f x = g x)
    {h x : ℝ} (hh : 0 ≤ h) (hx : 1 < x) (m : ℕ) :
    (fwdDiff h)^[m] f x = (fwdDiff h)^[m] g x := by
  rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
  apply sum_congr rfl
  intro k _
  rw [he _ (hx.trans_le (le_add_of_nonneg_right (nsmul_nonneg hh k)))]

theorem rs_local_difference_integrable {f : ℝ → ℝ}
    (hf : ∀ a b, 1 < a → 1 < b → IntervalIntegrable f volume a b)
    {h : ℝ} (hh : 0 ≤ h) (m : ℕ) {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable ((fwdDiff h)^[m] f) volume a b := by
  induction m generalizing a b with
  | zero => exact hf a b ha hb
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    have hi : IntervalIntegrable
        (fun x => (fwdDiff h)^[m] f (x + h)) volume a b := by
      simpa only [add_sub_cancel_right] using
        (ih (by linarith : 1 < a + h) (by linarith : 1 < b + h)).comp_add_right h
    exact hi.sub (ih ha hb)

theorem rs_local_difference_integral {f : ℝ → ℝ}
    (hf : ∀ a b, 1 < a → 1 < b → IntervalIntegrable f volume a b)
    {h x : ℝ} (hh : 0 ≤ h) (hx : 1 < x) (m : ℕ) :
    (fwdDiff h)^[m] (fun y => ∫ t in (0 : ℝ)..h, f (y + t)) x =
      ∫ t in (0 : ℝ)..h, (fwdDiff h)^[m] f (x + t) := by
  have hi (k : ℕ) :
      IntervalIntegrable (fun t => f (x + k • h + t)) volume 0 h := by
    have hk : 0 ≤ k • h := nsmul_nonneg hh k
    simpa only [add_sub_cancel_right, sub_self] using
      (hf (x + k • h) (h + (x + k • h)) (by linarith) (by linarith)).comp_add_left (x + k • h)
  rw [fwdDiff_iter_eq_sum_shift]
  calc
    _ = ∑ k ∈ range (m + 1), ∫ t in (0 : ℝ)..h,
        ((-1 : ℤ) ^ (m - k) * m.choose k) • f (x + k • h + t) := by
      apply sum_congr rfl
      intro k _
      exact ((hi k).integral_smul _).symm
    _ = ∫ t in (0 : ℝ)..h, ∑ k ∈ range (m + 1),
        ((-1 : ℤ) ^ (m - k) * m.choose k) • f (x + k • h + t) :=
      (intervalIntegral.integral_finsetSum (fun k _ =>
        (hi k).smul ((-1 : ℤ) ^ (m - k) * m.choose k))).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [fwdDiff_iter_eq_sum_shift]
      apply sum_congr rfl
      intro k _
      rw [add_right_comm x (k • h) t]

theorem rs_difference_re (f : ℝ → ℂ) (h : ℝ) (m : ℕ) (x : ℝ) :
    (fwdDiff h)^[m] (fun t => (f t).re) x = ((fwdDiff h)^[m] f x).re := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih => simp only [Function.iterate_succ_apply', fwdDiff, ih, Complex.sub_re]

theorem rs_difference_ofReal (f : ℝ → ℝ) (h : ℝ) (m : ℕ) (x : ℝ) :
    (fwdDiff h)^[m] (fun t => (f t : ℂ)) x = (((fwdDiff h)^[m] f x : ℝ) : ℂ) := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih => simp only [Function.iterate_succ_apply', fwdDiff, ih, Complex.ofReal_sub]

#print axioms rs_difference_congr_positive
#print axioms rs_local_difference_integrable
#print axioms rs_local_difference_integral
#print axioms rs_difference_re
#print axioms rs_difference_ofReal

end LiuWang.Proof.Campaign20260915.Totient
