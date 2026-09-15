import LiuWang.Proof.SourceRoute.SecondArc.DensityIntegral

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.DirichletZeroCount.Applications

namespace LiuWang.Proof.SourceRoute.SecondArc

theorem sourceSeven_envelope {q : ℕ} [NeZero q] {alpha y : ℝ}
    (hy : 1 ≤ y) (hz : 1 ≤ Real.log ((q : ℝ) * y)) (ha : alpha ≤ 1) :
    sourceSevenBound q alpha y ≤
      (254231 / Real.log ((q : ℝ) * y) + 33643) *
        (Real.log ((q : ℝ) * y)) ^ (6 : ℕ) *
          Real.exp (4 * Real.log ((q : ℝ) * y) * (1 - alpha)) := by
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hy0 : 0 < y := by linarith
  have hqy : 0 < (q : ℝ) * y := by positivity
  have hl : 0 ≤ Real.log y := Real.log_nonneg hy
  have hlz : Real.log y ≤ Real.log ((q : ℝ) * y) :=
    Real.log_le_log hy0 (le_mul_of_one_le_left hy0.le hq)
  have hlpow : (Real.log y) ^ (6 : ℕ) ≤
      (Real.log ((q : ℝ) * y)) ^ (6 : ℕ) := pow_le_pow_left₀ hl hlz _
  have hzpow : (Real.log ((q : ℝ) * y)) ^ (6 * alpha) ≤
      (Real.log ((q : ℝ) * y)) ^ (6 : ℕ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hz (by norm_num; linarith)
  have hbase : (q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ) ≤ ((q : ℝ) * y) ^ (4 : ℕ) := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hq (by norm_num : 3 ≤ 4)) (by positivity)
  have hp : ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)) ^ (1 - alpha) ≤
      Real.exp (4 * Real.log ((q : ℝ) * y) * (1 - alpha)) := by
    apply (Real.rpow_le_rpow (by positivity) hbase (sub_nonneg.mpr ha)).trans_eq
    rw [Real.rpow_def_of_pos (by positivity), Real.log_pow]
    norm_num
  have he : 1 ≤ Real.exp (4 * Real.log ((q : ℝ) * y) * (1 - alpha)) :=
    Real.one_le_exp_iff.mpr (mul_nonneg (by positivity) (sub_nonneg.mpr ha))
  have hc : 0 ≤ 17102 + 254231 / Real.log ((q : ℝ) * y) := by positivity
  unfold sourceSevenBound
  calc
    _ ≤ 16541 * (Real.log ((q : ℝ) * y)) ^ (6 : ℕ) *
          Real.exp (4 * Real.log ((q : ℝ) * y) * (1 - alpha)) +
        (17102 + 254231 / Real.log ((q : ℝ) * y)) *
          Real.exp (4 * Real.log ((q : ℝ) * y) * (1 - alpha)) *
            (Real.log ((q : ℝ) * y)) ^ (6 : ℕ) := by
      apply add_le_add
      · exact (mul_le_mul_of_nonneg_left hlpow (by norm_num)).trans
          (le_mul_of_one_le_right (by positivity) he)
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hp hc) hzpow
          (Real.rpow_nonneg (by positivity) _) (by positivity)
    _ = _ := by ring

theorem sourceSeven_weight_envelope {q : ℕ} [NeZero q] {x alpha y : ℝ}
    (hx : 0 < x) (hy : 1 ≤ y) (hz : 1 ≤ Real.log ((q : ℝ) * y))
    (hH : 0 ≤ Real.log x) (ha : alpha ≤ 1) :
    alphaKernel x alpha * sourceSevenBound q alpha y ≤
      (254231 / Real.log ((q : ℝ) * y) + 33643) *
        (Real.log ((q : ℝ) * y)) ^ (6 : ℕ) *
          (Real.log x * Real.exp ((alpha - 1) *
            (Real.log x - 4 * Real.log ((q : ℝ) * y)))) := by
  apply (mul_le_mul_of_nonneg_left (sourceSeven_envelope hy hz ha)
    (mul_nonneg (Real.rpow_nonneg hx.le _) hH)).trans_eq
  rw [Real.rpow_def_of_pos hx]
  have he : Real.exp (Real.log x * (alpha - 1)) *
      Real.exp (4 * Real.log ((q : ℝ) * y) * (1 - alpha)) =
        Real.exp ((alpha - 1) * (Real.log x - 4 * Real.log ((q : ℝ) * y))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = ((254231 / Real.log ((q : ℝ) * y) + 33643) *
        (Real.log ((q : ℝ) * y)) ^ (6 : ℕ) * Real.log x) *
        (Real.exp (Real.log x * (alpha - 1)) *
          Real.exp (4 * Real.log ((q : ℝ) * y) * (1 - alpha))) := by ring
    _ = _ := by rw [he]; ring

/-- The innermost density integral before (5.9), without assuming a zero-count bound. -/
theorem sourceSeven_integral_le_ordered {q : ℕ} [NeZero q] {x y a c : ℝ}
    (hx : 0 < x) (hy : 1 ≤ y) (hz : 1 ≤ Real.log ((q : ℝ) * y))
    (hH : 4 * Real.log ((q : ℝ) * y) < Real.log x) (hc : 0 ≤ c)
    (ha : a ≤ 1 - c / Real.log ((q : ℝ) * y)) :
    (∫ alpha in a..(1 - c / Real.log ((q : ℝ) * y)),
      alphaKernel x alpha * sourceSevenBound q alpha y) ≤
      (254231 / Real.log ((q : ℝ) * y) + 33643) *
        (Real.log ((q : ℝ) * y)) ^ (6 : ℕ) * Real.exp (4 * c) *
          (Real.log x / (Real.log x - 4 * Real.log ((q : ℝ) * y))) *
            Real.exp (-c * Real.log x / Real.log ((q : ℝ) * y)) := by
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hy0 : 0 < y := by linarith
  have hz0 : 0 < Real.log ((q : ℝ) * y) := by linarith
  have hb : 1 - c / Real.log ((q : ℝ) * y) ≤ 1 :=
    sub_le_self _ (div_nonneg hc hz0.le)
  have hcont : Continuous (fun alpha : ℝ =>
      alphaKernel x alpha * sourceSevenBound q alpha y) := by
    have hx0 := hx.ne'
    have hlog0 := hz0.ne'
    have hbase : (q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ) ≠ 0 := by positivity
    unfold alphaKernel sourceSevenBound
    fun_prop
  have hcont' : Continuous (fun alpha : ℝ =>
      (254231 / Real.log ((q : ℝ) * y) + 33643) *
        (Real.log ((q : ℝ) * y)) ^ (6 : ℕ) *
          (Real.log x * Real.exp ((alpha - 1) *
            (Real.log x - 4 * Real.log ((q : ℝ) * y))))) := by fun_prop
  calc
    _ ≤ ∫ alpha in a..(1 - c / Real.log ((q : ℝ) * y)),
        (254231 / Real.log ((q : ℝ) * y) + 33643) *
          (Real.log ((q : ℝ) * y)) ^ (6 : ℕ) *
            (Real.log x * Real.exp ((alpha - 1) *
              (Real.log x - 4 * Real.log ((q : ℝ) * y)))) := by
      apply intervalIntegral.integral_mono_on ha
        (hcont.intervalIntegrable _ _) (hcont'.intervalIntegrable _ _)
      intro alpha halpha
      exact sourceSeven_weight_envelope hx hy hz (by linarith) (halpha.2.trans hb)
    _ ≤ _ := by
      rw [intervalIntegral.integral_const_mul]
      have h := mul_le_mul_of_nonneg_left
        (density_cap_integral_le hz0 hH a c)
        (by positivity : 0 ≤ (254231 / Real.log ((q : ℝ) * y) + 33643) *
          (Real.log ((q : ℝ) * y)) ^ (6 : ℕ))
      exact h.trans_eq (by ring)

theorem sourceSeven_integral_le {q : ℕ} [NeZero q] {x y a c : ℝ}
    (hx : 0 < x) (hy : 1 ≤ y) (hz : 1 ≤ Real.log ((q : ℝ) * y))
    (hH : 4 * Real.log ((q : ℝ) * y) < Real.log x) (hc : 0 ≤ c) :
    (∫ alpha in a..(1 - c / Real.log ((q : ℝ) * y)),
      alphaKernel x alpha * sourceSevenBound q alpha y) ≤
      (254231 / Real.log ((q : ℝ) * y) + 33643) *
        (Real.log ((q : ℝ) * y)) ^ (6 : ℕ) * Real.exp (4 * c) *
          (Real.log x / (Real.log x - 4 * Real.log ((q : ℝ) * y))) *
            Real.exp (-c * Real.log x / Real.log ((q : ℝ) * y)) := by
  by_cases ha : a ≤ 1 - c / Real.log ((q : ℝ) * y)
  · exact sourceSeven_integral_le_ordered hx hy hz hH hc ha
  · have hf (alpha : ℝ) : 0 ≤ alphaKernel x alpha * sourceSevenBound q alpha y := by
      have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
      have hlog : 0 < Real.log x := by linarith
      unfold alphaKernel sourceSevenBound
      positivity
    have hi := intervalIntegral.integral_nonneg_of_forall (μ := volume) (le_of_not_ge ha) hf
    rw [intervalIntegral.integral_symm]
    apply (neg_nonpos.mpr hi).trans
    have hden : 0 < Real.log x - 4 * Real.log ((q : ℝ) * y) := by linarith
    have hlog : 0 < Real.log x := by linarith
    positivity

end LiuWang.Proof.SourceRoute.SecondArc
