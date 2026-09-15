import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536.Height
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536.Uniform

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536

theorem upper_eq (L : ℝ) : upper L = upperHeight L := by
  unfold upper upperHeight
  rw [← pow_add]

theorem height_bounds {L : ℝ} (hL : 3100 ≤ L) :
    0 < lower 3100 ∧ lower 3100 ≤ 60 ∧ lower 3100 ≤ lower L ∧
      lower L ≤ upper L ∧ 60 ≤ upper L := by
  have h := original_height_bounds hL
  have hbase : lower 3100 ≤ 60 := by
    change lowerHeight 3100 ≤ 60
    rw [lowerHeight_eq (by norm_num)]
    linarith [log_3100_bounds.2, Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3.36)]
  rw [upper_eq]
  exact ⟨h.1, hbase, h.2.2.1, h.2.2.2.1, by linarith [h.2.2.2.2]⟩

theorem integrand_integrable {f : ℝ → ℝ → ℝ}
    (hf : ∀ L, ContinuousOn (f L) (Set.Ioi 0)) (L : ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (integrand f L) volume a b := by
  unfold integrand
  simpa only [mul_assoc] using (log_integrable (hf L) ha hab).const_mul (L ^ 4)

theorem uniform_reduction {f : ℝ → ℝ → ℝ}
    (hf : ∀ L, ContinuousOn (f L) (Set.Ioi 0))
    (hpos : ∀ L s, 0 < L → 0 < s → 0 ≤ f L s)
    (hcore : ∀ L s, 3100 ≤ L → 0 < s → s ≤ 60 →
      integrand f L s ≤ integrand f 3100 s)
    (hpoly : ∀ L s, 0 < L → 0 < s →
      integrand f L s ≤ 100000000 * s ^ 4 * Real.exp (-s))
    {L : ℝ} (hL : 3100 ≤ L) :
    (∫ s in lower L..upper L, integrand f L s) ≤
      (∫ s in lower 3100..(60 : ℝ), integrand f 3100 s) + 1 / 10000000000 := by
  have hb := height_bounds hL
  have h0 : 0 < L := by linarith
  have hnon (x s : ℝ) (hx : 0 < x) (hs : 0 < s) : 0 ≤ integrand f x s :=
    mul_nonneg (by positivity) (hpos x s hx hs)
  have ht {b : ℝ} (hbt : 60 ≤ b) :
      (∫ s in (60 : ℝ)..b, integrand f L s) ≤ 1 / 10000000000 := by
    have hi : IntervalIntegrable (fun s : ℝ => 100000000 * s ^ 4 * Real.exp (-s))
        volume 60 b := by apply Continuous.intervalIntegrable; fun_prop
    exact (intervalIntegral.integral_mono_on hbt (integrand_integrable hf L (by norm_num) hbt)
      hi (fun s hs => hpoly _ _ h0 (by linarith [hs.1]))).trans (polynomial_tail60 hbt)
  have ha0 := hb.1.trans_le hb.2.2.1
  by_cases ha : lower L ≤ 60
  · rw [← intervalIntegral.integral_add_adjacent_intervals
      (integrand_integrable hf L ha0 ha)
      (integrand_integrable hf L (by norm_num) hb.2.2.2.2)]
    have hc := intervalIntegral.integral_mono_on ha
      (integrand_integrable hf L ha0 ha) (integrand_integrable hf 3100 ha0 ha)
      (fun s hs => hcore _ _ hL (ha0.trans_le hs.1) hs.2)
    have he := intervalIntegral.integral_mono_interval hb.2.2.1 ha le_rfl
      (ae_restrict_of_forall_mem measurableSet_Ioc (fun s hs =>
        hnon 3100 s (by norm_num) (hb.1.trans hs.1)))
      (integrand_integrable hf 3100 hb.1 hb.2.1)
    exact add_le_add (hc.trans he) (ht hb.2.2.2.2)
  · have ha' : 60 ≤ lower L := le_of_not_ge ha
    have he := intervalIntegral.integral_mono_interval ha' hb.2.2.2.1 le_rfl
      (ae_restrict_of_forall_mem measurableSet_Ioc (fun s hs =>
        hnon L s h0 (by linarith [hs.1])))
      (integrand_integrable hf L (by norm_num) hb.2.2.2.2)
    have hc : 0 ≤ ∫ s in lower 3100..(60 : ℝ), integrand f 3100 s :=
      intervalIntegral.integral_nonneg hb.2.1
        (fun s hs => hnon 3100 s (by norm_num) (hb.1.trans_le hs.1))
    exact (he.trans (ht hb.2.2.2.2)).trans (le_add_of_nonneg_left hc)

theorem source35_all_real_reduction {L : ℝ} (hL : 3100 ≤ L) :
    scalar35 L ≤
      (∫ s in lower 3100..(60 : ℝ), integrand profile35 3100 s) + 1 / 10000000000 :=
  uniform_reduction profile35_continuousOn (fun _ _ => profile35_nonneg)
    (fun _ _ => profile35_core) (fun _ _ => profile35_polynomial) hL

theorem source36_all_real_reduction {L : ℝ} (hL : 3100 ≤ L) :
    scalar36 L ≤
      (∫ s in lower 3100..(60 : ℝ), integrand profile36 3100 s) + 1 / 10000000000 :=
  uniform_reduction profile36_continuousOn (fun _ _ => profile36_nonneg)
    (fun _ _ => profile36_core) (fun _ _ => profile36_polynomial) hL

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536
