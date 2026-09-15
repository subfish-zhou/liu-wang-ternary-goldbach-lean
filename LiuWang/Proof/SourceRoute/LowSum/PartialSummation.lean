import LiuWang.Proof.SourceRoute.LowSum.Kernel
import LiuWang.Proof.WeightedLowZeros.Continuation.RetainedDensity

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.WeightedLowZeros
open LiuWang.Proof.DirichletZeroCount
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.SourceRoute.LowSum

def countingFunction {ι : Type*} [Fintype ι] (Z : ι → Finset ℂ)
    (m : ι → ℂ → ℕ) (alpha : ℝ) : ℝ :=
  ∑ i, ∑ rho ∈ (Z i).filter (fun rho => alpha ≤ rho.re), (m i rho : ℝ)

theorem counting_integrand_eq {ι : Type*} [Fintype ι] (N : ℕ)
    (Z : ι → Finset ℂ) (m : ι → ℂ → ℕ) (alpha : ℝ) :
    kernel N alpha * countingFunction Z m alpha =
      ∑ i, ∑ rho ∈ Z i, (m i rho : ℝ) *
        (Set.Iic rho.re).indicator (kernel N) alpha := by
  simp only [countingFunction, Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro rho _
  by_cases ha : alpha ≤ rho.re
  · simp [Set.indicator_of_mem, Set.mem_Iic, ha, mul_comm]
  · simp [Set.indicator_of_notMem, Set.mem_Iic, ha]

theorem indicator_kernel_integrable {N : ℕ} (hN : 0 < N) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (beta : ℝ) :
    IntervalIntegrable ((Set.Iic beta).indicator (kernel N)) volume a b := by
  rw [intervalIntegrable_iff]
  exact (kernel_integrable hN ha hab).def'.indicator measurableSet_Iic

theorem character_integrand_integrable {N : ℕ} (hN : 0 < N) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (Z : Finset ℂ) (m : ℂ → ℕ) :
    IntervalIntegrable (fun alpha => ∑ rho ∈ Z,
      (m rho : ℝ) * (Set.Iic rho.re).indicator (kernel N) alpha) volume a b := by
  convert! IntervalIntegrable.sum Z (fun rho _ =>
    (indicator_kernel_integrable hN ha hab rho.re).const_mul (m rho : ℝ)) using 1
  ext alpha
  simp only [Finset.sum_apply]

theorem counting_integrand_integrable {ι : Type*} [Fintype ι] {N : ℕ}
    (hN : 0 < N) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (Z : ι → Finset ℂ) (m : ι → ℂ → ℕ) :
    IntervalIntegrable (fun alpha => kernel N alpha * countingFunction Z m alpha)
      volume a b := by
  simp_rw [counting_integrand_eq]
  convert! IntervalIntegrable.sum (Finset.univ : Finset ι)
    (fun i _ => character_integrand_integrable hN ha hab (Z i) (m i)) using 1
  ext alpha
  simp only [Finset.sum_apply]

theorem counting_integral_eq {ι : Type*} [Fintype ι] {N : ℕ}
    (hN : 0 < N) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (Z : ι → Finset ℂ) (m : ι → ℂ → ℕ)
    (hZ : ∀ i, ∀ rho ∈ Z i, rho.re ∈ Set.Icc a b) :
    (∫ alpha in a..b, kernel N alpha * countingFunction Z m alpha) =
      ∑ i, ∑ rho ∈ Z i, (m i rho : ℝ) * ∫ alpha in a..rho.re, kernel N alpha := by
  simp_rw [counting_integrand_eq]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro rho hr
      rw [intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_indicator (f := kernel N) (hZ i rho hr)]
      rfl
    · intro rho _
      exact (indicator_kernel_integrable hN ha hab rho.re).const_mul _
  · intro i _
    exact character_integrand_integrable hN ha hab (Z i) (m i)

theorem finite_partial_summation {ι : Type*} [Fintype ι] {N : ℕ}
    (hN : 0 < N) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (Z : ι → Finset ℂ) (m : ι → ℂ → ℕ)
    (hZ : ∀ i, ∀ rho ∈ Z i, rho.re ∈ Set.Icc a b) :
    (∑ i, ∑ rho ∈ Z i, (m i rho : ℝ) * weight N rho.re) ≤
      weight N a * countingFunction Z m a +
        ∫ alpha in a..b, kernel N alpha * countingFunction Z m alpha := by
  have hcount : countingFunction Z m a = ∑ i, ∑ rho ∈ Z i, (m i rho : ℝ) := by
    unfold countingFunction
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.filter_eq_self.mpr (fun rho hr => (hZ i rho hr).1)]
  rw [hcount, counting_integral_eq hN ha hab Z m hZ, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro rho hr
  have h := mul_le_mul_of_nonneg_left
    (weight_le_initial_add_integral hN ha (hZ i rho hr).1) (Nat.cast_nonneg (m i rho))
  simpa only [mul_add, mul_comm (weight N a)] using h

theorem finite_partial_summation_split {ι : Type*} [Fintype ι] {N : ℕ}
    (hN : 0 < N) {a c b : ℝ} (ha : 0 < a) (hac : a ≤ c) (hcb : c ≤ b)
    (Z : ι → Finset ℂ) (m : ι → ℂ → ℕ)
    (hZ : ∀ i, ∀ rho ∈ Z i, rho.re ∈ Set.Icc a b) :
    (∑ i, ∑ rho ∈ Z i, (m i rho : ℝ) * weight N rho.re) ≤
      weight N a * countingFunction Z m a +
        (∫ alpha in a..c, kernel N alpha * countingFunction Z m alpha) +
        ∫ alpha in c..b, kernel N alpha * countingFunction Z m alpha := by
  rw [add_assoc, intervalIntegral.integral_add_adjacent_intervals
    (counting_integrand_integrable hN ha hac Z m)
    (counting_integrand_integrable hN (ha.trans_le hac) hcb Z m)]
  exact finite_partial_summation hN ha (hac.trans hcb) Z m hZ

theorem countingFunction_full {q : ℕ} [NeZero q] (y : ℝ) {alpha : ℝ}
    (ha : 1 / 2 ≤ alpha) :
    countingFunction (fun chi : Character q => CompleteExpansion.zeroValues chi y)
      zeroMultiplicity alpha = (familyCount q alpha y : ℝ) := by
  rw [Applications.familyCount_eq_complete_filter q ha]
  simp only [countingFunction, zeroMultiplicity, Nat.cast_sum]

theorem original_partial_summation {N q : ℕ} [NeZero q] (hN : 0 < N)
    (y : ℝ) {c : ℝ} (hc : 1 / 2 ≤ c) (hc1 : c ≤ 1) :
    (∑ chi : Character q, weightedSum N chi y) ≤
      weight N (1 / 2) * (familyCount q (1 / 2) y : ℝ) +
        (∫ alpha in (1 / 2 : ℝ)..c, kernel N alpha * (familyCount q alpha y : ℝ)) +
        ∫ alpha in c..1, kernel N alpha * (familyCount q alpha y : ℝ) := by
  have h := finite_partial_summation_split hN (by norm_num : (0 : ℝ) < 1 / 2) hc hc1
    (fun chi : Character q => CompleteExpansion.zeroValues chi y) zeroMultiplicity
    (fun _ _ hr => ⟨(CompleteExpansion.mem_zeroValues.mp hr).2.2.2.2,
      (CompleteExpansion.mem_zeroValues.mp hr).2.2.1.le⟩)
  rw [countingFunction_full y le_rfl] at h
  have he {a b : ℝ} (ha : 1 / 2 ≤ a) (hab : a ≤ b) :
      (∫ alpha in a..b, kernel N alpha *
        countingFunction (fun chi : Character q => CompleteExpansion.zeroValues chi y)
          zeroMultiplicity alpha) =
      ∫ alpha in a..b, kernel N alpha * (familyCount q alpha y : ℝ) := by
    apply intervalIntegral.integral_congr
    intro alpha halpha
    rw [Set.uIcc_of_le hab] at halpha
    dsimp only
    rw [countingFunction_full y (ha.trans halpha.1)]
  rw [he le_rfl hc, he hc hc1] at h
  exact h

theorem original_low_partial_summation {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    lowSum N q ≤
      weight N (1 / 2) * (familyCount q (1 / 2) (omegaCutoff N q) : ℝ) +
        (∫ alpha in (1 / 2 : ℝ)..bulkCap N,
          kernel N alpha * (familyCount q alpha (omegaCutoff N q) : ℝ)) +
        ∫ alpha in bulkCap N..1,
          kernel N alpha * (familyCount q alpha (omegaCutoff N q) : ℝ) :=
  original_partial_summation (Parameters.nat_pos_of_exp_le hN) _
    (bulkCap_bounds hN hq).1 (bulkCap_bounds hN hq).2.le

theorem retained_partial_summation {N q : ℕ} [NeZero q] (hN : 0 < N)
    (y : ℝ) (d : PrimitiveQuadraticDatum) (e : ℂ)
    {c : ℝ} (hc : 1 / 2 ≤ c) (hc1 : c ≤ 1) :
    retainedSum N q y d e ≤
      weight N (1 / 2) * (Continuation.retainedCount q (1 / 2) y d e : ℝ) +
        (∫ alpha in (1 / 2 : ℝ)..c,
          kernel N alpha * (Continuation.retainedCount q alpha y d e : ℝ)) +
        ∫ alpha in c..1,
          kernel N alpha * (Continuation.retainedCount q alpha y d e : ℝ) := by
  have h := finite_partial_summation_split hN (by norm_num : (0 : ℝ) < 1 / 2) hc hc1
    (fun chi : Character q => retainedValues chi y d e) zeroMultiplicity
    (fun _ _ hr => ⟨(CompleteExpansion.mem_zeroValues.mp (Finset.mem_filter.mp hr).1).2.2.2.2,
      (CompleteExpansion.mem_zeroValues.mp (Finset.mem_filter.mp hr).1).2.2.1.le⟩)
  simpa only [retainedSum, countingFunction, Continuation.retainedCount, Nat.cast_sum] using h

end LiuWang.Proof.SourceRoute.LowSum
