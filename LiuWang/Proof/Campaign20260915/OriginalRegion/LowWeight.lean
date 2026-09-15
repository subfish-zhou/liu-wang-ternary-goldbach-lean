import LiuWang.Proof.Campaign20260915.OriginalRegion.ShortWindow
import LiuWang.Proof.SourceRoute.LowSum.Continuation.InducedException
import LiuWang.Proof.SourceRoute.MajorOrdinary.PacketBounds
import LiuWang.Proof.WeightedLowZeros.Consumer

/-! The actual sourceT-truncated major-arc low sum, with ordinary multiplicities. -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.WeightedLowZeros LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.SourceRoute.LowSum
open LiuWang.Proof.SourceRoute.LowSum.Continuation
open LiuWang.Proof.SourceRoute.MajorOrdinary
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.Campaign20260915.OriginalRegion

theorem lowWeightSum_eq_lowSum {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    lowWeightSum N q = lowSum N q := by
  simp only [lowWeightSum, lowSum, weightedSum,
    values_low_eq_filter _ (omegaCutoff_le_sourceT (q := q) hN), zeroMultiplicity]

theorem lowWeightSum_source_split {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e) :
    lowWeightSum N q = retainedSum N q (omegaCutoff N q) d e +
      if d.modulus ∣ q then weight N e.re else 0 := by
  rw [lowWeightSum_eq_lowSum hN]
  exact paper_source_low_split hN hq hd

theorem lowWeightSum_induced_primed_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hdiv : d.modulus ∣ q) :
    lowWeightSum N q - weight N e.re ≤ 8.2e-10 / sourceL N := by
  rw [lowWeightSum_eq_lowSum hN]
  exact induced_original_weighted_bound hN hq hd hdiv

theorem induced_nonreal_seed_cap {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hdiv : d.modulus ∣ q) {chi : Character q} {rho : ℂ}
    (hr : rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q))
    (hi : rho.im ≠ 0) :
    rho.re ≤ cap N (1 / 9.645908801) := by
  have hret : rho ∈ retainedValues chi (omegaCutoff N q) d e := by
    refine Finset.mem_filter.mpr ⟨hr, ?_⟩
    refine Or.inr (fun he => hi ?_)
    rw [he]
    exact hd.2.2.1
  exact (SourceRoute.Exception.paper_source_retained_strict hN hq hd hdiv chi hret).le.trans
    (cap_order hN (by norm_num))

end LiuWang.Proof.Campaign20260915.OriginalRegion
