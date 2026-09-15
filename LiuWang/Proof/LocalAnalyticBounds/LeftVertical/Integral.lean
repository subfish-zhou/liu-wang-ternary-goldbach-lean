import LiuWang.Proof.LocalAnalyticBounds.LeftVertical.Integrand

/-!
# 非对称左边的真实 `du` 积分

只扩大非负主函数的积分区间；实际两个端点不要求对称。
衰减核真正积分为对数，不以整段最大值乘高度。
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace LiuWang.Proof.LocalAnalyticBounds.LeftVertical

theorem continuous_one_div_abs_add_one :
    Continuous (fun u : Real => 1 / (|u| + 1)) :=
  continuous_const.div (continuous_abs.add continuous_const) (fun u => by positivity)

theorem integral_one_div_abs_add_one {A : Real} (hA : 0 ≤ A) :
    (∫ u in -A..A, 1 / (|u| + 1)) = 2 * Real.log (A + 1) := by
  have hp : (∫ u in 0..A, 1 / (|u| + 1)) = Real.log (A + 1) := by
    calc
      _ = ∫ u in (0 : Real)..A, 1 / (u + 1) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [Set.uIcc_of_le hA] at hu
        simp only [abs_of_nonneg hu.1]
      _ = ∫ u in (1 : Real)..(A + 1), 1 / u := by
        simp only [intervalIntegral.integral_comp_add_right, zero_add]
      _ = Real.log (A + 1) := by
        rw [integral_one_div_of_pos (by norm_num) (by positivity)]
        simp
  have hn : (∫ u in -A..0, 1 / (|u| + 1)) =
      ∫ u in 0..A, 1 / (|u| + 1) := by
    simpa only [abs_neg, neg_zero] using
      (intervalIntegral.integral_comp_neg (fun u : Real => 1 / (|u| + 1))
        (a := 0) (b := A)).symm
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_one_div_abs_add_one.intervalIntegrable (-A) 0)
    (continuous_one_div_abs_add_one.intervalIntegrable 0 A), hn, hp]
  ring

theorem norm_left_integral_le_explicit
    {q : Nat} [NeZero q] {chi : DirichletCharacter Complex q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {t T Hplus Hminus : Real} (ht : 9 ≤ t) (hT : 1 ≤ T)
    (hp : |Hplus - T| ≤ 1) (hm : |Hminus + T| ≤ 1) :
    ‖∫ u in Hminus..Hplus, HorizontalEstimate.horizontalIntegrand chi t
      ((-1 / 2 : Complex) + (u : Complex) * Complex.I)‖ ≤
      6 * (Real.log q + Real.log (T + 3) + 40) * Real.log (T + 2) := by
  let D : Real := Real.log q + Real.log (T + 3) + 40
  have hqone : (1 : Real) ≤ q := by exact_mod_cast (NeZero.one_le : 1 ≤ q)
  have hD : 0 ≤ D := by
    dsimp [D]
    linarith [Real.log_nonneg hqone, Real.log_nonneg (show 1 ≤ T + 3 by linarith)]
  have hpa := abs_le.mp hp
  have hma := abs_le.mp hm
  have hab : Hminus ≤ Hplus := by linarith
  have hca : -(T + 1) ≤ Hminus := by linarith
  have hbd : Hplus ≤ T + 1 := by linarith
  have hg : Continuous (fun u : Real => (3 * D) * (1 / (|u| + 1))) :=
    continuous_const.mul continuous_one_div_abs_add_one
  have hb : ∀ u ∈ Set.Ioc Hminus Hplus,
      ‖HorizontalEstimate.horizontalIntegrand chi t
        ((-1 / 2 : Complex) + (u : Complex) * Complex.I)‖ ≤
        (3 * D) * (1 / (|u| + 1)) := by
    intro u hu
    have hau : |u| ≤ T + 1 := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have h := norm_horizontalIntegrand_left_le hchi hPrimitive ht
      (s := (-1 / 2 : Complex) + (u : Complex) * Complex.I) (by norm_num)
    have hl : Real.log (|u| + 2) ≤ Real.log (T + 3) :=
      Real.log_le_log (by positivity) (by linarith)
    have hi : ((-1 / 2 : Complex) + (u : Complex) * Complex.I).im = u := by norm_num
    rw [hi] at h
    calc
      _ ≤ 3 * (Real.log q + Real.log (|u| + 2) + 40) / (|u| + 1) := h
      _ ≤ (3 * D) / (|u| + 1) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        dsimp [D]
        linarith
      _ = _ := by ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hab
    (Filter.Eventually.of_forall hb) (hg.intervalIntegrable Hminus Hplus)
  have hmj := intervalIntegral.integral_mono_interval (μ := volume) hca hab hbd
    (f := fun u : Real => (3 * D) * (1 / (|u| + 1)))
    (Filter.Eventually.of_forall (fun u => by positivity))
    (hg.intervalIntegrable (-(T + 1)) (T + 1))
  calc
    _ ≤ ∫ u in Hminus..Hplus, (3 * D) * (1 / (|u| + 1)) := hi
    _ ≤ ∫ u in -(T + 1)..(T + 1), (3 * D) * (1 / (|u| + 1)) := hmj
    _ = 6 * D * Real.log (T + 2) := by
      rw [intervalIntegral.integral_const_mul,
        integral_one_div_abs_add_one (by linarith : 0 ≤ T + 1)]
      rw [show T + 1 + 1 = T + 2 by ring]
      ring

end LiuWang.Proof.LocalAnalyticBounds.LeftVertical
