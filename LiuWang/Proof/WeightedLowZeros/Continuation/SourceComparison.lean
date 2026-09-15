import LiuWang.Proof.WeightedLowZeros.Continuation.PaperSource

/-!
# The paper's change of scale, and a one-way R24 source comparison

This pays (2.9) for a fixed actual paper source. It does not assert the converse
R24 comparison, existence in the wider region, or the Table 1 repulsion bound.
-/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.ZeroRegionFamily
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.WeightedLowZeros.Continuation

theorem paper_gap_le_low_gap {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    1 / (9.645908801 * Real.log (sourceP N)) ≤ 0.11 / Real.log (lowScale N) := by
  have hP := sourceP_pos (exp_2000_le_of_exp_3100_le hN)
  have hlogP := (low_parameter_logs (q := 1) hN
    (by simpa only [Nat.cast_one] using one_le_sourceP (exp_2000_le_of_exp_3100_le hN))).1
  have hlogS : 25 ≤ Real.log (lowScale N) := (log_scale_bounds (sourceL_ge_3100 hN)).1
  have h336 : Real.log (3.36 : ℝ) ≤ 1.3 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    have ht := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.3) 6
    norm_num [Finset.sum_range_succ, Nat.factorial] at ht
    linarith
  have hid : Real.log (lowScale N) = Real.log 3.36 + Real.log (sourceP N) :=
    Real.log_mul (by norm_num) hP.ne'
  apply (div_le_div_iff₀ (by positivity) (by linarith)).mpr
  rw [hid]
  linarith

theorem paper_source_re_gt_low_011 {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e) :
    cap N 0.11 < e.re := by
  dsimp [cap]
  linarith [paper_gap_le_low_gap hN, hd.2.2.2.2]

theorem r24_source_is_paperSource {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : SourceAt (lowScale N) d e)
    (hdP : (d.modulus : ℝ) ≤ sourceP N) : PaperSource N d e := by
  have hP := sourceP_pos (exp_2000_le_of_exp_3100_le hN)
  have hlogP := (low_parameter_logs (q := 1) hN
    (by simpa only [Nat.cast_one] using one_le_sourceP (exp_2000_le_of_exp_3100_le hN))).1
  have hlog := Real.log_le_log hP (show sourceP N ≤ lowScale N by
    dsimp [lowScale]
    linarith)
  have hg : 1 / (24 * Real.log (lowScale N)) ≤
      1 / (9.645908801 * Real.log (sourceP N)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  refine ⟨hdP, hd.2.1, hd.2.2.1, hd.2.2.2.1, ?_⟩
  have hb := hd.2.2.2.2
  dsimp [regionCap] at hb
  linarith

theorem r24_source_is_paperSource_of_dvd {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : SourceAt (lowScale N) d e)
    (hdiv : d.modulus ∣ q) : PaperSource N d e :=
  r24_source_is_paperSource hN hd ((Nat.cast_le.mpr (Nat.le_of_dvd (NeZero.pos q) hdiv)).trans hq)

theorem exists_paper_source_of_r24_mem {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ}
    (hr : rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q))
    (hcap : regionCap (lowScale N) < rho.re) :
    ∃ d : PrimitiveQuadraticDatum, SourceAt (lowScale N) d rho ∧ PaperSource N d rho ∧
      d.modulus ∣ q ∧ inducedAt d q = chi := by
  obtain ⟨hx, hqx, he⟩ := lowScale_parameters hN hq
  have hr' := hr
  rw [← he] at hr'
  obtain ⟨d, hd⟩ := exists_source_of_mem hx hqx hr' hcap
  obtain ⟨hz, _, h1, hy, _⟩ := CompleteExpansion.mem_zeroValues.mp hr'
  have hp : chi ≠ 1 ∨ rho ≠ 1 := Or.inr (fun h => by simp [h] at h1)
  obtain ⟨_, _, hdiv, hc, _⟩ := source_controls hx hd q hqx chi rho ⟨hcap, hy⟩ hp hz
  exact ⟨d, hd, r24_source_is_paperSource_of_dvd hN hq hd hdiv, hdiv, hc⟩

end LiuWang.Proof.WeightedLowZeros.Continuation
