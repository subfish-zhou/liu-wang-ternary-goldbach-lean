import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source26Certificate.Tail

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source26Certificate

theorem scalar_eq_heights (L : ℝ) :
    scalar L = ∫ s in lowerHeight L..upperHeight L, integrand L s := by
  unfold scalar lowerHeight upperHeight
  rw [show L ^ (3 : ℕ) * L ^ (15 : ℕ) = L ^ (18 : ℕ) by ring]

theorem uniform_reduction {L : ℝ} (hL : 3100 ≤ L) :
    scalar L ≤ (∫ s in (25 : ℝ)..100, integrand 3100 s) + 1 / 1000000000000 := by
  have hb := original_height_bounds hL
  have ha0 := hb.1.trans_le hb.2.2.1
  have ha25 : (25 : ℝ) ≤ lowerHeight L :=
    (by norm_num : (25 : ℝ) ≤ 25329 / 1000).trans
      (rational_lowerHeight.trans hb.2.2.1)
  have hB : upperHeight L = 18 * Real.log L := by
    simp only [upperHeight, Real.log_pow, Nat.cast_ofNat]
  have hb0 : (100 : ℝ) ≤ 18 * Real.log (3100 : ℝ) := by linarith [log_3100_bounds.1]
  have hbase := integrand_integrable (L := 3100) (by norm_num) (by norm_num)
    (by norm_num : (25 : ℝ) ≤ 100) hb0
  have hnon (s : ℝ) (hs : s ∈ Set.Ioc (25 : ℝ) 100) : 0 ≤ integrand 3100 s :=
    integrand_nonneg (by norm_num) (by linarith [hs.1]) (hs.2.trans hb0)
  rw [scalar_eq_heights]
  by_cases ha : lowerHeight L ≤ 100
  · rw [← intervalIntegral.integral_add_adjacent_intervals
      (integrand_integrable hL ha0 ha (hb.2.2.2.2.trans hB.le))
      (integrand_integrable hL (by norm_num) hb.2.2.2.2 hB.le)]
    have hc := intervalIntegral.integral_mono_on ha
      (integrand_integrable hL ha0 ha (hb.2.2.2.2.trans hB.le))
      (integrand_integrable (by norm_num : (3100 : ℝ) ≤ 3100) ha0 ha hb0)
      (fun s hs => integrand_le_base hL (ha0.trans_le hs.1) hs.2)
    have hext := intervalIntegral.integral_mono_interval ha25 ha le_rfl
      (ae_restrict_of_forall_mem measurableSet_Ioc hnon) hbase
    exact add_le_add (hc.trans hext) (tail_integral hL hb.2.2.2.2 hB.le)
  · have ha' : 100 ≤ lowerHeight L := le_of_not_ge ha
    have hext := intervalIntegral.integral_mono_interval ha' hb.2.2.2.1 le_rfl
      (ae_restrict_of_forall_mem measurableSet_Ioc (fun s hs =>
        integrand_nonneg hL (by linarith [hs.1]) (hs.2.trans hB.le)))
      (integrand_integrable hL (by norm_num) hb.2.2.2.2 hB.le)
    have hbase0 : 0 ≤ ∫ s in (25 : ℝ)..100, integrand 3100 s :=
      intervalIntegral.integral_nonneg (by norm_num) (fun s hs =>
        integrand_nonneg (by norm_num) (by linarith [hs.1]) (hs.2.trans hb0))
    exact (hext.trans (tail_integral hL hb.2.2.2.2 hB.le)).trans (by linarith)

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source26Certificate
