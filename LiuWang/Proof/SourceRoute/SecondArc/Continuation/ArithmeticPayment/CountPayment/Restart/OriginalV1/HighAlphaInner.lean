import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ActualIntegral

set_option autoImplicit false
noncomputable section
open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.DirichletZeroCount.Applications

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1

theorem sourceSeven_original_envelope {q : ℕ} [NeZero q] {alpha y : ℝ}
    (hy : 1 ≤ y) (hz : 1 ≤ Real.log ((q : ℝ) * y)) (ha : alpha ≤ 1) :
    sourceSevenBound q alpha y ≤
      (254231 / Real.log ((q : ℝ) * y) + 33643) *
        Real.log ((q : ℝ) * y) ^ (6 : ℕ) *
          Real.exp (Real.log ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)) * (1 - alpha)) := by
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hy0 : 0 < y := by linarith
  have hlog : 0 ≤ Real.log y := Real.log_nonneg hy
  have hlogle : Real.log y ≤ Real.log ((q : ℝ) * y) :=
    Real.log_le_log hy0 (le_mul_of_one_le_left hy0.le hq)
  have hp := pow_le_pow_left₀ hlog hlogle 6
  have hr : Real.log ((q : ℝ) * y) ^ (6 * alpha) ≤
      Real.log ((q : ℝ) * y) ^ (6 : ℕ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hz (by norm_num; linarith)
  have hb : 1 ≤ (q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hq) (one_le_pow₀ hy)
  have he : 1 ≤ Real.exp
      (Real.log ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)) * (1 - alpha)) :=
    Real.one_le_exp_iff.mpr (mul_nonneg (Real.log_nonneg hb) (sub_nonneg.mpr ha))
  have hc : 0 ≤ 17102 + 254231 / Real.log ((q : ℝ) * y) := by positivity
  unfold sourceSevenBound
  rw [Real.rpow_def_of_pos (by positivity : 0 < (q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ))]
  calc
    _ ≤ 16541 * Real.log ((q : ℝ) * y) ^ (6 : ℕ) *
          Real.exp (Real.log ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)) * (1 - alpha)) +
        (17102 + 254231 / Real.log ((q : ℝ) * y)) *
          Real.exp (Real.log ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)) * (1 - alpha)) *
            Real.log ((q : ℝ) * y) ^ (6 : ℕ) := by
      exact add_le_add
        ((mul_le_mul_of_nonneg_left hp (by norm_num)).trans
          (le_mul_of_one_le_right (by positivity) he))
        (mul_le_mul_of_nonneg_left hr (by positivity))
    _ = _ := by ring

theorem sourceSeven_original_inner {q : ℕ} [NeZero q] {x y a c : ℝ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ Real.log ((q : ℝ) * y))
    (hgap : Real.log ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)) < Real.log x)
    (hc : 0 ≤ c) (ha : a ≤ 1 - c / Real.log ((q : ℝ) * y)) :
    (∫ alpha in a..(1 - c / Real.log ((q : ℝ) * y)),
      alphaKernel x alpha * sourceSevenBound q alpha y) ≤
      (254231 / Real.log ((q : ℝ) * y) + 33643) *
        Real.log ((q : ℝ) * y) ^ (6 : ℕ) *
        (Real.log x / (Real.log x -
          Real.log ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)))) *
        Real.exp (-c * (Real.log x -
          Real.log ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ))) / Real.log ((q : ℝ) * y)) := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hz0 : 0 < Real.log ((q : ℝ) * y) := by linarith
  have hbase : (q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ) ≠ 0 := by positivity
  have hf : Continuous (fun alpha : ℝ => alphaKernel x alpha * sourceSevenBound q alpha y) := by
    have hxne := hx0.ne'
    have hzne := hz0.ne'
    unfold alphaKernel sourceSevenBound
    fun_prop
  have hg : Continuous (fun alpha : ℝ =>
      (254231 / Real.log ((q : ℝ) * y) + 33643) *
        Real.log ((q : ℝ) * y) ^ (6 : ℕ) *
          (Real.log x * Real.exp ((alpha - 1) *
            (Real.log x - Real.log ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)))))) := by fun_prop
  calc
    _ ≤ ∫ alpha in a..(1 - c / Real.log ((q : ℝ) * y)),
        (254231 / Real.log ((q : ℝ) * y) + 33643) *
          Real.log ((q : ℝ) * y) ^ (6 : ℕ) *
            (Real.log x * Real.exp ((alpha - 1) *
              (Real.log x - Real.log ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ))))) := by
      apply intervalIntegral.integral_mono_on ha (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
      intro alpha halpha
      have hb : alpha ≤ 1 := halpha.2.trans (sub_le_self _ (div_nonneg hc hz0.le))
      have hm := mul_le_mul_of_nonneg_left (sourceSeven_original_envelope hy hz hb)
        (show 0 ≤ alphaKernel x alpha from
          mul_nonneg (Real.rpow_nonneg hx0.le _) (Real.log_nonneg hx))
      apply hm.trans_eq
      unfold alphaKernel
      rw [Real.rpow_def_of_pos hx0]
      have he : Real.exp (Real.log x * (alpha - 1)) *
          Real.exp (Real.log ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)) * (1 - alpha)) =
          Real.exp ((alpha - 1) *
            (Real.log x - Real.log ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)))) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = ((254231 / Real.log ((q : ℝ) * y) + 33643) *
            Real.log ((q : ℝ) * y) ^ (6 : ℕ) * Real.log x) *
            (Real.exp (Real.log x * (alpha - 1)) *
              Real.exp (Real.log ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)) * (1 - alpha))) := by ring
        _ = _ := by rw [he]; ring
    _ ≤ _ := by
      rw [intervalIntegral.integral_const_mul]
      exact (mul_le_mul_of_nonneg_left
        (integral_exp_density_cap_le (sub_pos.mpr hgap) (Real.log_nonneg hx) a c
          (Real.log ((q : ℝ) * y))) (by positivity)).trans_eq (by ring)

theorem actual_high_alpha_inner {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y : ℝ} (hy : y ∈ Set.Icc (omegaCutoff N q) (middleUpper N q))
    (hseven : ∀ alpha : ℝ, 1 / 2 ≤ alpha → alpha < 1 →
      (familyCount q alpha y : ℝ) ≤ sourceSevenBound q alpha y) :
    (∫ alpha in (59 / 60 : ℝ)..stripLower q y,
      alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) ≤
      (254231 / Real.log ((q : ℝ) * y) + 33643) *
        Real.log ((q : ℝ) * y) ^ (6 : ℕ) * Real.exp (4 * 0.478) *
        ((sourceL N + Real.log 0.001) /
          (sourceL N + Real.log 0.001 - 4 * Real.log ((q : ℝ) * y))) *
        Real.exp (-0.478 * (sourceL N + Real.log 0.001) / Real.log ((q : ℝ) * y)) := by
  have hd := middle_log_domain hN hq hy
  have hn := natCast_pos_of_exp_le hN
  have hx : 0 < 0.001 * (N : ℝ) := by positivity
  have hz : 0 < Real.log ((q : ℝ) * y) := by linarith [hd.2.1]
  have hk (alpha : ℝ) : 0 ≤ alphaKernel (0.001 * (N : ℝ)) alpha :=
    mul_nonneg (Real.rpow_nonneg hx.le _) (Real.log_nonneg (window_base_ge_one hN))
  by_cases hab : (59 / 60 : ℝ) ≤ stripLower q y
  · apply le_trans _ (source_59_inner hN hq hy)
    have hy0 : 0 < y := by linarith [hd.1]
    have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
    have hf : Continuous (fun alpha : ℝ =>
        alphaKernel (0.001 * (N : ℝ)) alpha * sourceSevenBound q alpha y) := by
      have hxne := hx.ne'
      have hzne := hz.ne'
      have hb : (q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ) ≠ 0 := by positivity
      unfold alphaKernel sourceSevenBound
      fun_prop
    apply intervalIntegral.integral_mono_on hab (count_alpha_integrable hx hab y)
      (hf.intervalIntegrable _ _)
    intro alpha halpha
    have hb : stripLower q y < 1 := by
      unfold stripLower
      exact sub_lt_self _ (div_pos (by norm_num) hz)
    exact mul_le_mul_of_nonneg_left
      (hseven alpha (by linarith [halpha.1]) (halpha.2.trans_lt hb)) (hk alpha)
  · have hi := intervalIntegral.integral_nonneg_of_forall (μ := volume)
      (le_of_not_ge hab)
      (fun alpha => mul_nonneg (hk alpha) (Nat.cast_nonneg (familyCount q alpha y)))
    rw [intervalIntegral.integral_symm]
    apply (neg_nonpos.mpr hi).trans
    have hgap : 0 < sourceL N + Real.log 0.001 - 4 * Real.log ((q : ℝ) * y) := by
      rw [← log_window_eq (nat_pos_of_exp_le hN)]
      linarith [hd.2.2]
    have hH : 0 < sourceL N + Real.log 0.001 := by linarith [hd.2.1]
    positivity

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1
