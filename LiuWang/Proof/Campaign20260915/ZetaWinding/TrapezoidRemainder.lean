import LiuWang.Proof.Campaign20260915.ZetaWinding.ZetaLehmanIdentity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset

namespace LiuWang.Proof.Campaign20260915.ZetaWinding

theorem trapezoid_unit_abs {f g h H : ℝ → ℝ} {a : ℝ}
    (hf : ∀ u ∈ Set.uIcc a (a + 1), HasDerivAt f (g u) u)
    (hg : ∀ u ∈ Set.uIcc a (a + 1), HasDerivAt g (h u) u)
    (hh : ContinuousOn h (Set.uIcc a (a + 1)))
    (hH : IntervalIntegrable H volume a (a + 1))
    (hb : ∀ u ∈ Set.Icc a (a + 1), |h u| ≤ H u) :
    |(f a + f (a + 1)) / 2 - ∫ u in a..a + 1, f u| ≤
      (∫ u in a..a + 1, H u) / 8 := by
  let p : ℝ → ℝ := fun u => (u - a) * (u - a - 1) / 2
  let d : ℝ → ℝ := fun u => u - a - 1 / 2
  have hp : ∀ u ∈ Set.uIcc a (a + 1), HasDerivAt p (d u) u := by
    intro u _
    convert! (((hasDerivAt_id u).sub_const a).mul
      (((hasDerivAt_id u).sub_const a).sub_const 1)).div_const 2 using 1
    dsimp [d]
    ring
  have hd : ∀ u ∈ Set.uIcc a (a + 1), HasDerivAt d 1 u := by
    intro u _
    simpa only [d] using! ((hasDerivAt_id u).sub_const a).sub_const (1 / 2)
  have hgi : IntervalIntegrable g volume a (a + 1) :=
    (continuousOn_of_forall_continuousAt (fun u hu => (hg u hu).continuousAt)).intervalIntegrable
  have he1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul hf hd hgi
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a (a + 1))
  have he2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul hg hp hh.intervalIntegrable
    ((by fun_prop : Continuous d).intervalIntegrable _ _)
  have he : (f a + f (a + 1)) / 2 - (∫ u in a..a + 1, f u) =
      ∫ u in a..a + 1, -p u * h u := by
    simp only [mul_one] at he1
    have hp0 : p a = 0 := by simp [p]
    have hp1 : p (a + 1) = 0 := by simp [p]
    have hd0 : d a = -1 / 2 := by dsimp [d]; ring
    have hd1 : d (a + 1) = 1 / 2 := by dsimp [d]; ring
    rw [hp0, hp1, mul_zero, mul_zero, sub_self] at he2
    rw [hd0, hd1] at he1
    have hx : (∫ u in a..a + 1, -p u * h u) =
        -(∫ u in a..a + 1, h u * p u) := by
      rw [← intervalIntegral.integral_neg]
      congr 1
      funext u
      ring
    rw [hx]
    linarith
  rw [he]
  calc
    _ ≤ ∫ u in a..a + 1, ‖-p u * h u‖ := by
      simpa only [Real.norm_eq_abs] using
        intervalIntegral.norm_integral_le_integral_norm (f := fun u => -p u * h u)
          (by linarith : a ≤ a + 1)
    _ ≤ ∫ u in a..a + 1, H u / 8 := by
      apply intervalIntegral.integral_mono_on (by linarith)
        (((by fun_prop : Continuous p).continuousOn.neg.mul hh).norm.intervalIntegrable) (hH.div_const 8)
      intro u hu
      have hpbound : |p u| ≤ 1 / 8 := by
        have hnon : p u ≤ 0 := by
          dsimp [p]
          exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos
            (by linarith [hu.1]) (by linarith [hu.2])) (by norm_num)
        rw [abs_of_nonpos hnon]
        dsimp [p]
        nlinarith [sq_nonneg (u - a - 1 / 2)]
      simp only [Pi.mul_apply, Pi.neg_apply, norm_mul, Real.norm_eq_abs, abs_neg]
      calc
        |p u| * |h u| ≤ (1 / 8 : ℝ) * H u :=
          mul_le_mul hpbound (hb u hu) (abs_nonneg _) (by norm_num)
        _ = H u / 8 := by ring
    _ = _ := by rw [intervalIntegral.integral_div]

theorem trapezoid_sum_abs {f g h H F G : ℝ → ℝ}
    (hf : ∀ u : ℝ, 0 ≤ u → HasDerivAt f (g u) u)
    (hg : ∀ u : ℝ, 0 ≤ u → HasDerivAt g (h u) u)
    (hh : ContinuousOn h (Set.Ici 0)) (hc : ContinuousOn H (Set.Ici 0))
    (hb : ∀ u : ℝ, 0 ≤ u → |h u| ≤ H u)
    (hF : ∀ u : ℝ, 0 ≤ u → HasDerivAt F (f u) u)
    (hG : ∀ u : ℝ, 0 ≤ u → HasDerivAt G (H u) u) (N : ℕ) :
    |(∑ n ∈ range N, f n) + (f N - f 0) / 2 - (F N - F 0)| ≤
      (G N - G 0) / 8 := by
  have hu {n : ℕ} {u : ℝ} (hu : u ∈ Set.uIcc (n : ℝ) (n + 1)) : 0 ≤ u := by
    rw [Set.uIcc_of_le (by linarith : (n : ℝ) ≤ n + 1)] at hu
    exact (Nat.cast_nonneg n).trans hu.1
  induction N with
  | zero => simp
  | succ N ih =>
    have hunit := trapezoid_unit_abs (a := (N : ℝ))
      (fun u hx => hf u (hu hx)) (fun u hx => hg u (hu hx))
      (hh.mono (fun u hx => hu hx))
      ((hc.mono (fun u hx => hu hx)).intervalIntegrable)
      (fun u hx => hb u ((Nat.cast_nonneg N).trans hx.1))
    have hfi : IntervalIntegrable f volume (N : ℝ) (N + 1) :=
      (continuousOn_of_forall_continuousAt (fun u hx => (hf u (hu hx)).continuousAt)).intervalIntegrable
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u hx => hF u (hu hx)) hfi,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u hx => hG u (hu hx))
        ((hc.mono (fun u hx => hu hx)).intervalIntegrable)] at hunit
    have he :
        (∑ n ∈ range (N + 1), f n) + (f (N + 1) - f 0) / 2 - (F (N + 1) - F 0) =
        ((∑ n ∈ range N, f n) + (f N - f 0) / 2 - (F N - F 0)) +
          ((f N + f (N + 1)) / 2 - (F (N + 1) - F N)) := by
      rw [Finset.sum_range_succ]
      ring
    simp only [Nat.cast_add, Nat.cast_one]
    rw [he]
    exact (abs_add_le _ _).trans ((add_le_add ih hunit).trans_eq (by ring))

#print axioms trapezoid_unit_abs
#print axioms trapezoid_sum_abs

end LiuWang.Proof.Campaign20260915.ZetaWinding
