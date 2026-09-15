import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.HighAlphaHeight

set_option autoImplicit false
noncomputable section
open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1

def siegelCutoff (q : ℕ) (y : ℝ) : ℝ :=
  1 - 1 / (9.645908801 * Real.log ((q : ℝ) * y))

theorem count_strip_le_constant {q : ℕ} [NeZero q] {x a b K y : ℝ}
    (hx : 1 ≤ x) (hab : a ≤ b)
    (hcount : ∀ alpha ∈ Set.Ioo a b, (familyCount q alpha y : ℝ) ≤ K) :
    (∫ alpha in a..b, alphaKernel x alpha * (familyCount q alpha y : ℝ)) ≤
      K * (x ^ (b - 1) - x ^ (a - 1)) := by
  have hx0 : 0 < x := by linarith
  calc
    _ ≤ ∫ alpha in a..b, K * alphaKernel x alpha := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo hab
        (count_alpha_integrable hx0 hab y)
        (((continuous_alphaKernel hx0).const_mul K).intervalIntegrable _ _)
      intro alpha halpha
      exact (mul_le_mul_of_nonneg_left (hcount alpha halpha)
        (show 0 ≤ alphaKernel x alpha from
          mul_nonneg (Real.rpow_nonneg hx0.le _) (Real.log_nonneg hx))).trans_eq (mul_comm _ _)
    _ = _ := by rw [intervalIntegral.integral_const_mul, integral_alphaKernel hx0]

theorem sparse_cutoff_order {q : ℕ} {y : ℝ}
    (hz : 1 ≤ Real.log ((q : ℝ) * y)) :
    1 / 2 ≤ stripUpper q y ∧ stripUpper q y ≤ siegelCutoff q y ∧
      siegelCutoff q y < 1 := by
  have hz0 : 0 < Real.log ((q : ℝ) * y) := by linarith
  have hs := div_le_self (by norm_num : (0 : ℝ) ≤ 0.2067) hz
  have hr := div_le_div_of_nonneg_right
    (by norm_num : (1 : ℝ) / 9.645908801 ≤ 0.2067) hz0.le
  unfold stripUpper siegelCutoff
  rw [show 1 / (9.645908801 * Real.log ((q : ℝ) * y)) =
    ((1 : ℝ) / 9.645908801) / Real.log ((q : ℝ) * y) by ring]
  exact ⟨by linarith, by linarith,
    sub_lt_self _ (div_pos (by norm_num) hz0)⟩

theorem siegelCutoff_continuous {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    ContinuousOn (siegelCutoff q) (Set.Icc (omegaCutoff N q) (middleUpper N q)) := by
  have hh := middle_height_domain hN hq
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hl : ContinuousOn (fun y : ℝ => Real.log ((q : ℝ) * y))
      (Set.Icc (omegaCutoff N q) (middleUpper N q)) :=
    (continuousOn_const.mul continuousOn_id).log
      (fun y hy => (mul_pos hq0 (hh.1.trans_le hy.1)).ne')
  apply continuousOn_const.sub (continuousOn_const.div (continuousOn_const.mul hl) ?_)
  intro y hy
  have hz : 0 < Real.log ((q : ℝ) * y) := by linarith [(middle_log_domain hN hq hy).2.1]
  change 9.645908801 * Real.log ((q : ℝ) * y) ≠ 0
  positivity

theorem actual_last_strip_inner {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y : ℝ} (hy : y ∈ Set.Icc (omegaCutoff N q) (middleUpper N q))
    (htwo : ∀ x : ℝ, 8000000000 ≤ x → (q : ℝ) ≤ x →
      ∀ alpha : ℝ, 1 - 0.2067 / Real.log x < alpha → alpha < 1 →
        (familyCount q alpha (x / q) : ℝ) ≤ 2) :
    (∫ alpha in stripUpper q y..siegelCutoff q y,
      alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) ≤
      2 * ∫ alpha in stripUpper q y..siegelCutoff q y,
        alphaKernel (0.001 * (N : ℝ)) alpha := by
  have hd := exact_scale_domain hN hq hy.1
  have ho := sparse_cutoff_order (middle_log_domain hN hq hy).2.1
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hn := natCast_pos_of_exp_le hN
  rw [integral_alphaKernel (by positivity : 0 < 0.001 * (N : ℝ))]
  apply count_strip_le_constant (window_base_ge_one hN) ho.2.1
  intro alpha halpha
  have hc := htwo ((q : ℝ) * y) (by linarith [hd.2.1])
    (le_mul_of_one_le_right hq0.le hd.1) alpha halpha.1 (halpha.2.trans ho.2.2)
  simpa only [mul_div_cancel_left₀ y hq0.ne'] using hc

theorem actual_last_strip_log_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (htwo : ∀ x : ℝ, 8000000000 ≤ x → (q : ℝ) ≤ x →
      ∀ alpha : ℝ, 1 - 0.2067 / Real.log x < alpha → alpha < 1 →
        (familyCount q alpha (x / q) : ℝ) ≤ 2) :
    (8 * (N : ℝ) * Real.sqrt q / q.totient) *
      (∫ y in (omegaCutoff N q)..middleUpper N q, heightKernel y *
        ∫ alpha in stripUpper q y..siegelCutoff q y,
          alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) ≤
      (16 * (N : ℝ)) * ((q : ℝ) / q.totient) *
        ∫ z in lowerLog (sourceL N)..upperLog (sourceL N),
          Real.exp (-z / 2) *
            (Real.exp (-((1 : ℝ) / 9.645908801) * (sourceL N + Real.log 0.001) / z) -
              Real.exp (-0.2067 * (sourceL N + Real.log 0.001) / z)) := by
  have hh := middle_height_domain hN hq
  have hn := natCast_pos_of_exp_le hN
  have hx : 0 < 0.001 * (N : ℝ) := by positivity
  have hs := (strip_bounds_continuous hN hq).2
  have ht := siegelCutoff_continuous hN hq
  have ho (y : ℝ) (hy : y ∈ Set.Icc (omegaCutoff N q) (middleUpper N q)) :=
    sparse_cutoff_order (middle_log_domain hN hq hy).2.1
  have hk : ContinuousOn heightKernel (Set.Icc (omegaCutoff N q) (middleUpper N q)) :=
    continuousOn_id.rpow_const (fun y hy => Or.inl (ne_of_gt (hh.1.trans_le hy.1)))
  have hi := moving_count_strip_integrable (q := q) hx hh.2.1 hs ht
    (fun y hy => (ho y hy).1) (fun y hy => (ho y hy).2.1)
  have hki := hi.mul_continuousOn
    (show ContinuousOn heightKernel (Set.uIcc (omegaCutoff N q) (middleUpper N q)) by
      rwa [Set.uIcc_of_le hh.2.1])
  have hg : ContinuousOn (fun y => (0.001 * (N : ℝ)) ^ (siegelCutoff q y - 1) -
      (0.001 * (N : ℝ)) ^ (stripUpper q y - 1))
      (Set.Icc (omegaCutoff N q) (middleUpper N q)) :=
    ((Real.continuous_const_rpow hx.ne').comp_continuousOn
      (ht.sub continuousOn_const)).sub
        ((Real.continuous_const_rpow hx.ne').comp_continuousOn (hs.sub continuousOn_const))
  have hkg : IntervalIntegrable (fun y => 2 * (heightKernel y *
      ∫ alpha in stripUpper q y..siegelCutoff q y, alphaKernel (0.001 * (N : ℝ)) alpha))
      volume (omegaCutoff N q) (middleUpper N q) := by
    simp_rw [integral_alphaKernel hx]
    exact ((hk.mul hg).const_mul 2).intervalIntegrable_of_Icc hh.2.1
  have hb : (∫ y in (omegaCutoff N q)..middleUpper N q, heightKernel y *
      ∫ alpha in stripUpper q y..siegelCutoff q y,
        alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) ≤
      2 * ∫ y in (omegaCutoff N q)..middleUpper N q, heightKernel y *
        ∫ alpha in stripUpper q y..siegelCutoff q y, alphaKernel (0.001 * (N : ℝ)) alpha := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hh.2.1
      (by simpa only [mul_comm] using hki) hkg
    intro y hy
    exact (mul_le_mul_of_nonneg_left (actual_last_strip_inner hN hq hy htwo)
      (heightKernel_nonneg (hh.1.le.trans hy.1))).trans_eq (by ring)
  have hm := mul_le_mul_of_nonneg_left hb
    (by positivity : 0 ≤ 8 * (N : ℝ) * Real.sqrt q / q.totient)
  rw [show (16 * (N : ℝ)) * ((q : ℝ) / q.totient) *
      (∫ z in lowerLog (sourceL N)..upperLog (sourceL N), Real.exp (-z / 2) *
        (Real.exp (-((1 : ℝ) / 9.645908801) * (sourceL N + Real.log 0.001) / z) -
          Real.exp (-0.2067 * (sourceL N + Real.log 0.001) / z))) =
      (16 * (N : ℝ)) * ((Real.sqrt q / q.totient) *
        (∫ y in (omegaCutoff N q)..middleUpper N q, heightKernel y *
          ∫ alpha in stripUpper q y..siegelCutoff q y,
            alphaKernel (0.001 * (N : ℝ)) alpha)) from
      (source_517_kernel_identity hN hq 9.645908801).symm]
  exact hm.trans_eq (by ring)

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1
