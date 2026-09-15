import LiuWang.Proof.SourceRoute.LowSum.Continuation.RowIntegrals
import LiuWang.Proof.SourceRoute.Exception.ExactCount

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.WeightedLowZeros LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.DirichletZeroCount
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation

theorem repulsion_cap_le_last_cap {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    cap N 0.3221 ≤ cap N 0.32 :=
  cap_order hN (by norm_num)

theorem induced_retained_last_count_zero {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hdiv : d.modulus ∣ q) :
    retainedCount q (cap N 0.32) (omegaCutoff N q) d e = 0 :=
  Exception.paper_source_retainedCount_zero hN hq hd hdiv (repulsion_cap_le_last_cap hN)

theorem induced_family_last_count_exact {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hdiv : d.modulus ∣ q) {alpha : ℝ} (ha : cap N 0.32 ≤ alpha) :
    familyCount q alpha (omegaCutoff N q) = if alpha ≤ e.re then 1 else 0 :=
  Exception.paper_source_familyCount_exact hN hq hd hdiv ((repulsion_cap_le_last_cap hN).trans ha)

theorem induced_original_213 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hdiv : d.modulus ∣ q) :
    (∫ alpha in bulkCap N..1,
      kernel N alpha * (retainedCount q alpha (omegaCutoff N q) d e : ℝ)) ≤ 6e-13 / sourceL N :=
  retained_213_of_zero hN hq d e (induced_retained_last_count_zero hN hq hd hdiv)

theorem induced_original_primed_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hdiv : d.modulus ∣ q) :
    lowSum N q - (if d.modulus ∣ q then weight N e.re else 0) ≤ 8.2e-10 / sourceL N :=
  exceptional_original_from_counts hN hq hd
    (fun _ hi => retained_nine_rows hN hq d e hi)
    (induced_retained_last_count_zero hN hq hd hdiv)

theorem induced_original_weighted_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hdiv : d.modulus ∣ q) :
    lowSum N q - weight N e.re ≤ 8.2e-10 / sourceL N := by
  simpa only [if_pos hdiv] using induced_original_primed_bound hN hq hd hdiv

theorem induced_retained_weighted_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hdiv : d.modulus ∣ q) :
    retainedSum N q (omegaCutoff N q) d e ≤ 8.2e-10 / sourceL N := by
  have h := induced_original_primed_bound hN hq hd hdiv
  rwa [paper_source_low_split hN hq hd, add_sub_cancel_right] at h

theorem induced_retained_Jrho_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hdiv : d.modulus ∣ q) (eta : ℝ) :
    (∑ chi : Character q, ∑ rho ∈ retainedValues chi (omegaCutoff N q) d e,
      (zeroMultiplicity chi rho : ℝ) * ‖Jrho N rho eta‖) ≤
        (N : ℝ) * (8.2e-10 / sourceL N) := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Character q)))
    (fun chi _ => subset_Jrho_le (nat_pos_of_exp_le hN) chi (omegaCutoff N q) eta
      (retainedValues chi (omegaCutoff N q) d e) (Finset.filter_subset _ _))
  rw [← Finset.mul_sum] at h
  exact h.trans (mul_le_mul_of_nonneg_left (induced_retained_weighted_bound hN hq hd hdiv)
    (Nat.cast_nonneg _))

end LiuWang.Proof.SourceRoute.LowSum.Continuation
