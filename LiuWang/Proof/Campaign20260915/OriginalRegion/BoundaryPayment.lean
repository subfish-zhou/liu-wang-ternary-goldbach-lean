import LiuWang.Proof.Campaign20260915.OriginalRegion.ClosedWindow
import LiuWang.Proof.Campaign20260915.OriginalRegion.SourceNoninducing

/-! A real boundary zero is paid in the ordinary cap, not falsely excluded by hshort. -/

set_option autoImplicit false
noncomputable section

open Complex
open scoped Classical
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.WeightedLowZeros LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.SourceRoute.LowSum
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart
open LiuWang.Proof.SourceRoute.MajorOrdinary

namespace LiuWang.Proof.Campaign20260915.OriginalRegion

theorem paperCap_le_original_low_cap {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    paperCap N ≤ cap N (1 / 9.645908801) := by
  have hp := sourceP_pos (exp_2000_le_of_exp_3100_le hN)
  have hlog := Real.log_le_log hp (show sourceP N ≤ lowScale N by
    change sourceP N ≤ 3.36 * sourceP N
    linarith)
  have hL : 0 < Real.log (sourceP N) :=
    Real.log_pos (by linarith [sourceP_original_scale hN])
  have hh := one_div_le_one_div_of_le
    (show 0 < 9.645908801 * Real.log (sourceP N) by positivity)
    (show 9.645908801 * Real.log (sourceP N) ≤
      9.645908801 * Real.log (lowScale N) by linarith)
  dsimp only [paperCap, cap]
  rw [div_div]
  linarith

theorem strict_source_of_real_high_zero {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ}
    (hr : rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q))
    (hi : rho.im = 0) (hb : paperCap N < rho.re) :
    ∃ d : PrimitiveQuadraticDatum, PaperSource N d rho ∧
      d.modulus ∣ q ∧ inducedAt d q = chi := by
  have ht : |rho.im| ≤ sourceP N / q := by
    rw [hi, abs_zero]
    exact div_nonneg (sourceP_pos (exp_2000_le_of_exp_3100_le hN)).le (Nat.cast_nonneg q)
  obtain ⟨d, hd, _, hdiv, hchi⟩ := closed_source_of_short_zero hN hq hr ht hb.le
  exact ⟨d, ⟨hd.1, hd.2.1, hi, hd.2.2.2.1, hb⟩, hdiv, hchi⟩

theorem no_strict_source_real_cap {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hnone : ¬ ∃ d e, PaperSource N d e)
    {chi : Character q} {rho : ℂ}
    (hr : rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q))
    (hi : rho.im = 0) : rho.re ≤ paperCap N := by
  by_contra hh
  obtain ⟨d, hd, _⟩ := strict_source_of_real_high_zero hN hq hr hi (lt_of_not_ge hh)
  exact hnone ⟨d, rho, hd⟩

theorem no_strict_source_original_cap {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hnone : ¬ ∃ d e, PaperSource N d e)
    {chi : Character q} {rho : ℂ}
    (hr : rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q)) :
    rho.re ≤ cap N (1 / 9.645908801) := by
  by_cases hi : rho.im = 0
  · exact (no_strict_source_real_cap hN hq hnone hr hi).trans (paperCap_le_original_low_cap hN)
  · exact source_free_nonreal_seed_cap hN hq hr hi

theorem no_strict_source_low_sum {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hnone : ¬ ∃ d e, PaperSource N d e) : lowSum N q ≤ 0.0194 / sourceL N :=
  original_low_sum_exhaustive hN hq (fun _ _ hr _ => no_strict_source_original_cap hN hq hnone hr)

theorem no_strict_source_low_weight {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hnone : ¬ ∃ d e, PaperSource N d e) : lowWeightSum N q ≤ 0.0194 / sourceL N := by
  rw [lowWeightSum_eq_lowSum hN]
  exact no_strict_source_low_sum hN hq hnone

theorem boundary_source_ordinary_payment {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : ClosedPaperSource N d e)
    (he : e.re = paperCap N) : lowWeightSum N q ≤ 0.0194 / sourceL N :=
  no_strict_source_low_weight hN hq (boundary_source_no_strict hN hd he)

theorem strict_source_or_ordinary_all_moduli {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∃ d e, PaperSource N d e ∧
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N →
        lowWeightSum N q - (if d.modulus ∣ q then weight N e.re else 0) ≤ 0.0194 / sourceL N) ∨
    ((¬ ∃ d e, PaperSource N d e) ∧
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N →
        lowWeightSum N q ≤ 0.0194 / sourceL N) := by
  by_cases hex : ∃ d e, PaperSource N d e
  · obtain ⟨d, e, hd⟩ := hex
    exact Or.inl ⟨d, e, hd, fun q _ hq => lowWeightSum_paper_source_bound (q := q) hN hq hd⟩
  · exact Or.inr ⟨hex, fun q _ hq => no_strict_source_low_weight (q := q) hN hq hex⟩

end LiuWang.Proof.Campaign20260915.OriginalRegion
