import LiuWang.Proof.SourceRoute.LowSum.BulkIntegral
import LiuWang.Proof.WeightedLowZeros.Continuation.PaperSource

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.WeightedLowZeros
open LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.DirichletZeroCount LiuWang.Proof.Parameters
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.SourceRoute.LowSum

theorem integral_density_le {N : ℕ} (hN : 0 < N) {a b D : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hD : 0 ≤ D) {F : ℝ → ℝ}
    (hF : IntervalIntegrable (fun alpha => kernel N alpha * F alpha) volume a b)
    (hbound : ∀ alpha ∈ Set.Icc a b, F alpha ≤ D) :
    (∫ alpha in a..b, kernel N alpha * F alpha) ≤
      D * coefficient a * ((N : ℝ) ^ (b - 1) - (N : ℝ) ^ (a - 1)) := by
  calc
    _ ≤ ∫ alpha in a..b, D * kernel N alpha := by
      apply intervalIntegral.integral_mono_on hab hF ((kernel_integrable hN ha hab).const_mul D)
      intro alpha halpha
      rw [mul_comm D]
      exact mul_le_mul_of_nonneg_left (hbound alpha halpha)
        (kernel_nonneg hN (ha.trans_le halpha.1))
    _ = D * ∫ alpha in a..b, kernel N alpha := intervalIntegral.integral_const_mul _ _
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (integral_kernel_le_endpoint_difference hN ha hab) hD

theorem countingFunction_le_full {q : ℕ} [NeZero q] {y alpha : ℝ}
    (ha : 1 / 2 ≤ alpha) (Z : Character q → Finset ℂ)
    (hZ : ∀ chi, Z chi ⊆ CompleteExpansion.zeroValues chi y) :
    countingFunction Z zeroMultiplicity alpha ≤ (familyCount q alpha y : ℝ) := by
  rw [← countingFunction_full y ha]
  unfold countingFunction
  apply Finset.sum_le_sum
  intro chi _
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset_filter _ (hZ chi)
  · exact fun _ _ _ => Nat.cast_nonneg _

theorem original_count_budget {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) (alpha : ℝ) :
    (familyCount q alpha (omegaCutoff N q) : ℝ) ≤
      8.82 * sourceP N * Real.log (sourceP N) := by
  have hy := omegaCutoff_pos (exp_2000_le_of_exp_3100_le hN) (NeZero.pos q)
  have hc : (familyCount q alpha (omegaCutoff N q) : ℝ) ≤
      countMother q (omegaCutoff N q) 1 :=
    familyCount_le_sharpened q alpha hy.le (by norm_num)
  apply (hc.trans (countMother_low_uniform hN hq 1)).trans
  have hP : 1 ≤ sourceP N := one_le_sourceP (exp_2000_le_of_exp_3100_le hN)
  have hlog : 0 ≤ Real.log (sourceP N) := Real.log_nonneg hP
  nlinarith

theorem subset_bulk_integral_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (Z : Character q → Finset ℂ)
    (hZ : ∀ chi, Z chi ⊆ CompleteExpansion.zeroValues chi (omegaCutoff N q)) :
    weight N (1 / 2) * countingFunction Z zeroMultiplicity (1 / 2) +
      (∫ alpha in (1 / 2 : ℝ)..bulkCap N,
        kernel N alpha * countingFunction Z zeroMultiplicity alpha) ≤ 8.1e-10 / sourceL N := by
  let M := 8.82 * sourceP N * Real.log (sourceP N)
  have hn := nat_pos_of_exp_le hN
  have hb := (bulkCap_bounds hN hq).1
  have hcount {alpha : ℝ} (ha : 1 / 2 ≤ alpha) :
      countingFunction Z zeroMultiplicity alpha ≤ M :=
    (countingFunction_le_full ha Z hZ).trans (original_count_budget hN hq alpha)
  have hi : (∫ alpha in (1 / 2 : ℝ)..bulkCap N,
      kernel N alpha * countingFunction Z zeroMultiplicity alpha) ≤
        M * ∫ alpha in (1 / 2 : ℝ)..bulkCap N, kernel N alpha := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hb
      (counting_integrand_integrable hn (by norm_num) hb Z zeroMultiplicity)
      ((kernel_integrable hn (by norm_num) hb).const_mul M)
    intro alpha halpha
    rw [mul_comm M]
    exact mul_le_mul_of_nonneg_left (hcount halpha.1) (kernel_nonneg hn (by linarith [halpha.1]))
  have hinit := mul_le_mul_of_nonneg_left (hcount le_rfl)
    (weight_nonneg N (by norm_num : (0 : ℝ) < 1 / 2))
  have hstep :
      weight N (1 / 2) * countingFunction Z zeroMultiplicity (1 / 2) +
        (∫ alpha in (1 / 2 : ℝ)..bulkCap N,
          kernel N alpha * countingFunction Z zeroMultiplicity alpha) ≤
      M * (weight N (1 / 2) + ∫ alpha in (1 / 2 : ℝ)..bulkCap N, kernel N alpha) := by
    nlinarith
  exact hstep.trans (original_bulk_integral_numeric hN)

theorem subset_original_reduction {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (Z : Character q → Finset ℂ)
    (hZ : ∀ chi, Z chi ⊆ CompleteExpansion.zeroValues chi (omegaCutoff N q)) :
    (∑ chi, ∑ rho ∈ Z chi, (zeroMultiplicity chi rho : ℝ) * weight N rho.re) ≤
      8.1e-10 / sourceL N +
        ∫ alpha in bulkCap N..1, kernel N alpha * countingFunction Z zeroMultiplicity alpha := by
  have hb := bulkCap_bounds hN hq
  have h := finite_partial_summation_split (nat_pos_of_exp_le hN)
    (by norm_num : (0 : ℝ) < 1 / 2) hb.1 hb.2.le Z zeroMultiplicity
    (fun chi rho hr => ⟨(CompleteExpansion.mem_zeroValues.mp (hZ chi hr)).2.2.2.2,
      (CompleteExpansion.mem_zeroValues.mp (hZ chi hr)).2.2.1.le⟩)
  exact h.trans (add_le_add (subset_bulk_integral_paid hN hq Z hZ) le_rfl)

theorem original_low_reduction {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    lowSum N q ≤ 8.1e-10 / sourceL N +
      ∫ alpha in bulkCap N..1, kernel N alpha * (familyCount q alpha (omegaCutoff N q) : ℝ) := by
  have h := subset_original_reduction hN hq
    (fun chi : Character q => CompleteExpansion.zeroValues chi (omegaCutoff N q))
    (fun _ _ hr => hr)
  have he : (∫ alpha in bulkCap N..1, kernel N alpha *
      countingFunction (fun chi : Character q => CompleteExpansion.zeroValues chi (omegaCutoff N q))
        zeroMultiplicity alpha) =
      ∫ alpha in bulkCap N..1, kernel N alpha * (familyCount q alpha (omegaCutoff N q) : ℝ) := by
    apply intervalIntegral.integral_congr
    intro alpha halpha
    rw [Set.uIcc_of_le (bulkCap_bounds hN hq).2.le] at halpha
    dsimp only
    rw [countingFunction_full _ ((bulkCap_bounds hN hq).1.trans halpha.1)]
  rw [he] at h
  exact h

theorem retained_original_reduction {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (d : PrimitiveQuadraticDatum) (e : ℂ) :
    retainedSum N q (omegaCutoff N q) d e ≤ 8.1e-10 / sourceL N +
      ∫ alpha in bulkCap N..1,
        kernel N alpha * (retainedCount q alpha (omegaCutoff N q) d e : ℝ) := by
  simpa only [retainedSum, countingFunction, retainedCount, Nat.cast_sum] using
    subset_original_reduction hN hq
      (fun chi : Character q => retainedValues chi (omegaCutoff N q) d e)
      (fun _ => Finset.filter_subset _ _)

theorem paper_primed_original_reduction {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e) :
    lowSum N q - (if d.modulus ∣ q then weight N e.re else 0) ≤ 8.1e-10 / sourceL N +
      ∫ alpha in bulkCap N..1,
        kernel N alpha * (retainedCount q alpha (omegaCutoff N q) d e : ℝ) := by
  rw [paper_source_low_split hN hq hd, add_sub_cancel_right]
  exact retained_original_reduction hN hq d e

end LiuWang.Proof.SourceRoute.LowSum
