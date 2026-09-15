import LiuWang.Proof.NearArcPayment.Continuation.Frontier.Regression
import LiuWang.Proof.NearOneDensity.Continuation.CountInterface

/-! 对原 frontier 的整段近一尾部实际应用已接回 0.478 表，而非追加实部上截口。 -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment

open Interfaces Parameters CompleteExpansion NearOneDensity

def densityScale (N : ℕ) : ℝ := sourceL N ^ 18

def densityAlpha (N : ℕ) : ℝ := 1 - 0.478 / Real.log (densityScale N)

theorem density_domain {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    100000000000 ≤ densityScale N ∧
      (q : ℝ) * max 1 (sourceT N) ≤ densityScale N := by
  constructor
  · exact (by norm_num : (100000000000 : ℝ) ≤ 2000 ^ 18).trans
      (pow_le_pow_left₀ (by norm_num) (sourceL_ge_2000 hN) 18)
  · have ht : 1 ≤ sourceT N := one_le_pow₀ (one_le_sourceL hN)
    rw [max_eq_right ht]
    simpa only [densityScale, sourceP, sourceT, ← pow_add] using
      mul_le_mul_of_nonneg_right hq (sourceT_pos hN).le

theorem densityAlpha_ge_nine_tenths {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    0.9 ≤ densityAlpha N := by
  have hscale : 100000000000 ≤ densityScale N :=
    (by norm_num : (100000000000 : ℝ) ≤ 2000 ^ 18).trans
      (pow_le_pow_left₀ (by norm_num) (sourceL_ge_2000 hN) 18)
  have hl := source_log_lower hscale
  unfold densityAlpha
  have hh : 0.478 / Real.log (densityScale N) ≤ 0.1 := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log (densityScale N))).mpr
    linarith
  linarith

def densityValues {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ)
    (positive : Bool) : Finset ℂ :=
  (tailValues chi N positive).filter (fun rho =>
    densityAlpha N ≤ rho.re ∧
      (sourceL N ^ 6 ≤ |rho.im| ∨
        (sourceL N ^ 4 ≤ |rho.im| ∧ if positive then 0 < rho.im else rho.im < 0)))

def residualValues {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ)
    (positive : Bool) : Finset ℂ :=
  (tailValues chi N positive).filter (fun rho =>
    ¬ (densityAlpha N ≤ rho.re ∧
      (sourceL N ^ 6 ≤ |rho.im| ∨
        (sourceL N ^ 4 ≤ |rho.im| ∧ if positive then 0 < rho.im else rho.im < 0))))

theorem densityValues_subset {N q : ℕ} [NeZero q]
    (chi : Character q) (positive : Bool) :
    densityValues chi N positive ⊆
      (CompleteExpansion.zeroValues chi (sourceT N)).filter (fun rho => densityAlpha N ≤ rho.re) := by
  intro rho hr
  obtain ⟨hr, ha, _⟩ := Finset.mem_filter.mp hr
  have hf := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1
  obtain ⟨hz, h0, h1, ht, hb, _⟩ := (finalValues_literal chi).mp hf
  exact Finset.mem_filter.mpr ⟨mem_zeroValues.mpr ⟨hz, h0, h1, ht, by linarith⟩, ha⟩

theorem density_count_le_row {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) (positive : Bool) :
    (∑ chi : Character q, ∑ rho ∈ densityValues chi N positive,
      (analyticOrderNatAt chi.LFunction rho : ℝ)) ≤ 14000 := by
  obtain ⟨hz, hqy⟩ := density_domain hN hq
  have hr := NearOneDensity.Continuation.complete_tail_count_row .r0478 hz hqy
    (alpha := densityAlpha N) (by rfl)
  have hc : (∑ chi : Character q,
      ∑ rho ∈ (CompleteExpansion.zeroValues chi (sourceT N)).filter
        (fun rho => densityAlpha N ≤ rho.re),
          (analyticOrderNatAt chi.LFunction rho : ℝ)) ≤ 14000 := by
    norm_num [rowBound, rowMultiplicity, rowSelectedBound] at hr
    exact_mod_cast hr
  apply le_trans _ hc
  apply Finset.sum_le_sum
  intro chi _
  exact Finset.sum_le_sum_of_subset_of_nonneg (densityValues_subset chi positive)
    (fun _ _ _ => Nat.cast_nonneg _)

end LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment
