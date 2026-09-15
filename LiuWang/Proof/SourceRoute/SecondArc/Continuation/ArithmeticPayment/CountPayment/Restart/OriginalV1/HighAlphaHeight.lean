import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.HighAlphaInner
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.ScalarReduction

set_option autoImplicit false
noncomputable section
open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.DirichletZeroCount.Applications

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1

def densityCap (H z : ℝ) : ℝ :=
  (254231 / z + 33643) * z ^ (6 : ℕ) * Real.exp (4 * 0.478) *
    (H / (H - 4 * z)) * Real.exp (-0.478 * H / z)

theorem densityCap_nonneg {H z : ℝ} (hz : 0 < z) (hH : 4 * z < H) :
    0 ≤ densityCap H z := by
  have hgap : 0 < H - 4 * z := sub_pos.mpr hH
  have hH0 : 0 < H := by linarith
  unfold densityCap
  positivity

theorem densityCap_continuousOn {H : ℝ} {s : Set ℝ}
    (hz : ∀ z ∈ s, z ≠ 0) (hgap : ∀ z ∈ s, H - 4 * z ≠ 0) :
    ContinuousOn (densityCap H) s := by
  unfold densityCap
  exact (((((continuousOn_const.div continuousOn_id hz).add continuousOn_const).mul
    (continuousOn_id.pow 6)).mul continuousOn_const).mul
      (continuousOn_const.div (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)) hgap)).mul
        (Real.continuous_exp.comp_continuousOn (continuousOn_const.div continuousOn_id hz))

theorem densityCap_kernel (H z : ℝ) :
    Real.exp (-z / 2) * densityCap H z =
      Real.exp (4 * 0.478) * densityKernel H z := by
  unfold densityCap densityKernel
  have he : Real.exp (-z / 2 - 0.478 * H / z) =
      Real.exp (-z / 2) * Real.exp (-0.478 * H / z) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  ring

theorem moving_count_strip_integrable_unordered {q : ℕ} [NeZero q] {x u v : ℝ}
    {a b : ℝ → ℝ} (hx : 0 < x) (huv : u ≤ v)
    (ha : ContinuousOn a (Set.Icc u v)) (hb : ContinuousOn b (Set.Icc u v))
    (ha0 : ∀ y ∈ Set.Icc u v, 1 / 2 ≤ a y)
    (hb0 : ∀ y ∈ Set.Icc u v, 1 / 2 ≤ b y) :
    IntervalIntegrable (fun y => ∫ alpha in (a y)..(b y),
      alphaKernel x alpha * (familyCount q alpha y : ℝ)) volume u v := by
  have hi := (moving_count_strip_integrable (q := q) hx huv continuousOn_const hb
    (fun _ _ => le_rfl) hb0).sub
      (moving_count_strip_integrable (q := q) hx huv continuousOn_const ha
        (fun _ _ => le_rfl) ha0)
  apply hi.congr_ae
  apply ae_restrict_of_forall_mem measurableSet_uIoc
  intro y hy
  rw [Set.uIoc_of_le huv] at hy
  have hy' : y ∈ Set.Icc u v := ⟨hy.1.le, hy.2⟩
  exact intervalIntegral.integral_interval_sub_left
    (count_alpha_integrable hx (hb0 y hy') y) (count_alpha_integrable hx (ha0 y hy') y)

theorem actual_high_alpha_height_integrable {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    IntervalIntegrable (fun y => heightKernel y *
      ∫ alpha in (59 / 60 : ℝ)..stripLower q y,
        alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ))
      volume (omegaCutoff N q) (middleUpper N q) := by
  have hh := middle_height_domain hN hq
  have hn := natCast_pos_of_exp_le hN
  have hs := strip_bounds_continuous hN hq
  have hi := moving_count_strip_integrable_unordered (q := q)
    (by positivity : 0 < 0.001 * (N : ℝ)) hh.2.1 continuousOn_const hs.1
    (fun _ _ => by norm_num : ∀ y ∈ Set.Icc (omegaCutoff N q) (middleUpper N q),
      (1 / 2 : ℝ) ≤ 59 / 60) (by
        intro y hy
        have hd := middle_log_domain hN hq hy
        have hb := div_le_self (by norm_num : (0 : ℝ) ≤ 0.478) hd.2.1
        unfold stripLower
        linarith)
  have hk : ContinuousOn heightKernel (Set.uIcc (omegaCutoff N q) (middleUpper N q)) := by
    rw [Set.uIcc_of_le hh.2.1]
    exact continuousOn_id.rpow_const (fun y hy => Or.inl (ne_of_gt (hh.1.trans_le hy.1)))
  simpa only [mul_comm] using hi.mul_continuousOn hk

theorem densityCap_height_continuous {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    ContinuousOn (fun y => heightKernel y *
      densityCap (sourceL N + Real.log 0.001) (Real.log ((q : ℝ) * y)))
      (Set.Icc (omegaCutoff N q) (middleUpper N q)) := by
  have hh := middle_height_domain hN hq
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hl : ContinuousOn (fun y : ℝ => Real.log ((q : ℝ) * y))
      (Set.Icc (omegaCutoff N q) (middleUpper N q)) :=
    (continuousOn_const.mul continuousOn_id).log
      (fun y hy => (mul_pos hq0 (hh.1.trans_le hy.1)).ne')
  have hc : ContinuousOn (densityCap (sourceL N + Real.log 0.001))
      ((fun y : ℝ => Real.log ((q : ℝ) * y)) ''
        Set.Icc (omegaCutoff N q) (middleUpper N q)) := by
    apply densityCap_continuousOn
    · rintro z ⟨y, hy, rfl⟩
      exact ne_of_gt (by linarith [(middle_log_domain hN hq hy).2.1])
    · rintro z ⟨y, hy, rfl⟩
      rw [← log_window_eq (nat_pos_of_exp_le hN)]
      exact (sub_pos.mpr (middle_log_domain hN hq hy).2.2).ne'
  exact (continuousOn_id.rpow_const
    (fun y hy => Or.inl (ne_of_gt (hh.1.trans_le hy.1)))).mul
      (hc.comp hl (fun y hy => ⟨y, hy, rfl⟩))

theorem actual_high_alpha_height_le_original {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {u : ℝ} (hu : omegaCutoff N q ≤ u) (huv : u ≤ middleUpper N q)
    (hgate : densityGate q ≤ u)
    (hseven : ∀ y : ℝ, densityGate q ≤ y → ∀ alpha : ℝ,
      1 / 2 ≤ alpha → alpha < 1 →
        (familyCount q alpha y : ℝ) ≤ sourceSevenBound q alpha y)
    (hnu : (q : ℝ) / q.totient ≤ sourceNu (sourceP N)) :
    (8 * Real.sqrt q / q.totient) *
      (∫ y in u..middleUpper N q, heightKernel y *
        ∫ alpha in (59 / 60 : ℝ)..stripLower q y,
          alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) ≤
      originalDensityScalar (sourceL N) / sourceL N := by
  have hh := middle_height_domain hN hq
  have hL := sourceL_ge_3100 hN
  have hL0 : 0 < sourceL N := by linarith
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hi := actual_high_alpha_height_integrable hN hq
  have hc := (densityCap_height_continuous hN hq).intervalIntegrable_of_Icc (μ := volume) hh.2.1
  have hsub : Set.uIcc u (middleUpper N q) ⊆
      Set.uIcc (omegaCutoff N q) (middleUpper N q) := by
    rw [Set.uIcc_of_le huv, Set.uIcc_of_le hh.2.1]
    exact Set.Icc_subset_Icc hu le_rfl
  have hp (y : ℝ) (hy : y ∈ Set.Icc (omegaCutoff N q) (middleUpper N q)) :
      0 ≤ heightKernel y *
        densityCap (sourceL N + Real.log 0.001) (Real.log ((q : ℝ) * y)) := by
    have hd := middle_log_domain hN hq hy
    apply mul_nonneg (heightKernel_nonneg (hh.1.le.trans hy.1))
    apply densityCap_nonneg (by linarith [hd.2.1])
    rw [← log_window_eq (nat_pos_of_exp_le hN)]
    exact hd.2.2
  have hbound :
      (∫ y in u..middleUpper N q, heightKernel y *
        ∫ alpha in (59 / 60 : ℝ)..stripLower q y,
          alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) ≤
      ∫ y in (omegaCutoff N q)..middleUpper N q, heightKernel y *
        densityCap (sourceL N + Real.log 0.001) (Real.log ((q : ℝ) * y)) := by
    apply le_trans (intervalIntegral.integral_mono_on huv
      (hi.mono_set hsub) (hc.mono_set hsub) ?_)
    · exact intervalIntegral.integral_mono_interval hu huv le_rfl
        (ae_restrict_of_forall_mem measurableSet_Ioc (fun y hy => hp y ⟨hy.1.le, hy.2⟩)) hc
    · intro y hy
      exact mul_le_mul_of_nonneg_left
        (actual_high_alpha_inner hN hq ⟨hu.trans hy.1, hy.2⟩
          (hseven y (hgate.trans hy.1)))
        (heightKernel_nonneg (hh.1.le.trans (hu.trans hy.1)))
  have hJ := intervalIntegral.integral_nonneg (μ := volume) hh.2.1 hp
  rw [log_height_change hq0 hh.1 (hh.1.trans_le hh.2.1)] at hJ
  have hJ0 := nonneg_of_mul_nonneg_right hJ (Real.sqrt_pos.mpr hq0)
  have hnorm := normalized_log_height_change (phi := (q.totient : ℝ))
    hq0 hh.1 (hh.1.trans_le hh.2.1) (densityCap (sourceL N + Real.log 0.001))
  have hmul := mul_le_mul_of_nonneg_left hbound
    (by positivity : 0 ≤ 8 * Real.sqrt q / q.totient)
  calc
    _ ≤ 8 * ((Real.sqrt q / q.totient) *
        (∫ y in (omegaCutoff N q)..middleUpper N q, heightKernel y *
          densityCap (sourceL N + Real.log 0.001) (Real.log ((q : ℝ) * y)))) :=
      hmul.trans_eq (by ring)
    _ = 8 * (((q : ℝ) / q.totient) *
        ∫ z in Real.log ((q : ℝ) * omegaCutoff N q)..
          Real.log ((q : ℝ) * middleUpper N q),
            Real.exp (-z / 2) * densityCap (sourceL N + Real.log 0.001) z) := by rw [hnorm]
    _ ≤ 8 * (sourceNu (sourceP N) *
        ∫ z in Real.log ((q : ℝ) * omegaCutoff N q)..
          Real.log ((q : ℝ) * middleUpper N q),
            Real.exp (-z / 2) * densityCap (sourceL N + Real.log 0.001) z) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hnu hJ0) (by norm_num)
    _ = _ := by
      simp_rw [densityCap_kernel]
      rw [intervalIntegral.integral_const_mul,
        (source_log_endpoints (N := N) (q := q)).1,
        (source_log_endpoints (N := N) (q := q)).2]
      unfold originalDensityScalar lowerLog upperLog sourceP
      field_simp

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1
