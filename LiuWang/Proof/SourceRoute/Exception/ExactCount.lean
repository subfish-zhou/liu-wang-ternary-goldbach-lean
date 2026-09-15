import LiuWang.Proof.SourceRoute.Exception.PaperWindow

set_option autoImplicit false
noncomputable section

open Complex
open scoped Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.WeightedLowZeros
open LiuWang.Proof.WeightedLowZeros.Continuation
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.SourceRoute.Exception

theorem paper_source_retainedCount_zero {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hdiv : d.modulus ∣ q) {alpha : ℝ} (ha : cap N 0.3221 ≤ alpha) :
    retainedCount q alpha (omegaCutoff N q) d e = 0 := by
  unfold retainedCount
  apply Finset.sum_eq_zero
  intro psi _
  have hfilter : (retainedValues psi (omegaCutoff N q) d e).filter
      (fun rho => alpha ≤ rho.re) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro rho hr
    obtain ⟨hr, hbound⟩ := Finset.mem_filter.mp hr
    exact (not_lt_of_ge (ha.trans hbound))
      (paper_source_retained_strict hN hq hd hdiv psi hr)
  rw [hfilter, Finset.sum_empty]

theorem repulsion_cap_ge_half {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    1 / 2 ≤ cap N 0.3221 := by
  have hlog : (25 : ℝ) ≤ Real.log (lowScale N) :=
    (log_scale_bounds (sourceL_ge_3100 hN)).1
  have hg : 0.3221 / Real.log (lowScale N) ≤ 1 / 2 :=
    (div_le_iff₀ (by linarith)).mpr (by linarith)
  change 1 / 2 ≤ 1 - 0.3221 / Real.log (lowScale N)
  linarith

theorem paper_source_familyCount_exact {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hdiv : d.modulus ∣ q) {alpha : ℝ} (ha : cap N 0.3221 ≤ alpha) :
    familyCount q alpha (omegaCutoff N q) = if alpha ≤ e.re then 1 else 0 := by
  have h := paper_source_count_split hN hq hd ((repulsion_cap_ge_half hN).trans ha)
  rw [paper_source_retainedCount_zero hN hq hd hdiv ha, zero_add] at h
  simpa only [hdiv, true_and] using h

theorem paper_source_closed_boundary_count_one {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hdiv : d.modulus ∣ q) :
    familyCount q (cap N 0.3221) (omegaCutoff N q) = 1 := by
  have hlog : 0 < Real.log (lowScale N) := by
    have h : (25 : ℝ) ≤ Real.log (lowScale N) :=
      (log_scale_bounds (sourceL_ge_3100 hN)).1
    linarith
  have hcmp : cap N 0.3221 ≤ cap N 0.11 := by
    have hh := div_le_div_of_nonneg_right (by norm_num : (0.11 : ℝ) ≤ 0.3221) hlog.le
    dsimp only [cap]
    linarith
  have he := hcmp.trans (paper_source_re_gt_low_011 hN hd).le
  rw [paper_source_familyCount_exact hN hq hd hdiv le_rfl, if_pos he]

end LiuWang.Proof.SourceRoute.Exception
