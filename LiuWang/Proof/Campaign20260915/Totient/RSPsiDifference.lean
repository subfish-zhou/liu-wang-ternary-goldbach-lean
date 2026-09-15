import LiuWang.Proof.Campaign20260915.Totient.RSPsiBox
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open MeasureTheory Set

namespace LiuWang.Proof.Campaign20260915.Totient

def rsPsiPrimitive : ℕ → ℝ → ℝ
  | 0 => Chebyshev.psi
  | m + 1 => fun x => ∫ t in (0 : ℝ)..x, rsPsiPrimitive m t

theorem rsPsiPrimitive_integrable (m : ℕ) (a b : ℝ) :
    IntervalIntegrable (rsPsiPrimitive m) volume a b := by
  induction m generalizing a b with
  | zero => exact Chebyshev.psi_mono.intervalIntegrable
  | succ m ih => exact (intervalIntegral.continuous_primitive ih 0).intervalIntegrable a b

theorem rsPsiPrimitive_difference (h : ℝ) (m : ℕ) (x : ℝ) :
    fwdDiff h (rsPsiPrimitive (m + 1)) x =
      ∫ t in (0 : ℝ)..h, rsPsiPrimitive m (x + t) := by
  rw [intervalIntegral.integral_comp_add_left, add_zero]
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (rsPsiPrimitive_integrable m 0 x) (rsPsiPrimitive_integrable m x (h + x))
  dsimp [fwdDiff, rsPsiPrimitive]
  rw [add_comm x h]
  linarith

private theorem difference_integrable (h : ℝ) {f : ℝ → ℝ}
    (hf : ∀ a b, IntervalIntegrable f volume a b) (m : ℕ) :
    ∀ a b, IntervalIntegrable ((fwdDiff h)^[m] f) volume a b := by
  induction m with
  | zero => exact hf
  | succ m ih =>
    intro a b
    rw [Function.iterate_succ_apply']
    have hi : IntervalIntegrable
        (fun x => (fwdDiff h)^[m] f (x + h)) volume a b := by
      simpa only [add_sub_cancel_right] using
        (ih (a + h) (b + h)).comp_add_right h
    exact hi.sub (ih a b)

theorem rs_difference_integral (h : ℝ) {f : ℝ → ℝ}
    (hf : ∀ a b, IntervalIntegrable f volume a b) (m : ℕ) (x : ℝ) :
    (fwdDiff h)^[m] (fun y => ∫ t in (0 : ℝ)..h, f (y + t)) x =
      ∫ t in (0 : ℝ)..h, (fwdDiff h)^[m] f (x + t) := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    change (fwdDiff h)^[m] (fun y => ∫ t in (0 : ℝ)..h, f (y + t)) (x + h) -
      (fwdDiff h)^[m] (fun y => ∫ t in (0 : ℝ)..h, f (y + t)) x = _
    rw [ih, ih]
    have hi (c : ℝ) : IntervalIntegrable
        (fun t => (fwdDiff h)^[m] f (c + t)) volume 0 h := by
      simpa only [add_sub_cancel_right, sub_self] using
        (difference_integrable h hf m c (h + c)).comp_add_left c
    rw [← intervalIntegral.integral_sub (hi (x + h)) (hi x)]
    apply intervalIntegral.integral_congr
    intro t _
    rw [Function.iterate_succ_apply']
    simp only [fwdDiff]
    rw [add_right_comm x h t]

theorem rsPsiPrimitive_finite_difference (h : ℝ) (m : ℕ) (x : ℝ) :
    (fwdDiff h)^[m] (rsPsiPrimitive m) x = rsPsiBox h m x := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    have he : fwdDiff h (rsPsiPrimitive (m + 1)) =
        fun y => ∫ t in (0 : ℝ)..h, rsPsiPrimitive m (y + t) :=
      funext (rsPsiPrimitive_difference h m)
    rw [he, rs_difference_integral h (rsPsiPrimitive_integrable m)]
    exact intervalIntegral.integral_congr (fun t _ => ih (x + t))

theorem rsPsiPrimitive_original_desmoothing {m : ℕ} {δ a x : ℝ}
    (hδ : 0 < δ) (ha : 0 < a) (hcut : 1 + (m : ℝ) * δ * a < a)
    (hax : a ≤ x) :
    1 < x - (m : ℝ) * (δ * x) ∧
      (fwdDiff (δ * x))^[m] (rsPsiPrimitive m) (x - (m : ℝ) * (δ * x)) /
        (δ * x) ^ m ≤ Chebyshev.psi x ∧
      Chebyshev.psi x ≤
        (fwdDiff (δ * x))^[m] (rsPsiPrimitive m) x / (δ * x) ^ m := by
  simpa only [rsPsiPrimitive_finite_difference] using
    rsPsiBox_original_desmoothing hδ ha hcut hax

#print axioms rsPsiPrimitive_integrable
#print axioms rsPsiPrimitive_difference
#print axioms rs_difference_integral
#print axioms rsPsiPrimitive_finite_difference
#print axioms rsPsiPrimitive_original_desmoothing

end LiuWang.Proof.Campaign20260915.Totient
