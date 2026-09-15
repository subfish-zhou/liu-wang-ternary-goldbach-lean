import LiuWang.Proof.SourceRoute.LowSum.TailNumerics

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.WeightedLowZeros
open LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.Parameters
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.SourceRoute.LowSum

def breakpoint : ℕ → ℝ
  | 0 => 0.478 | 1 => 0.475 | 2 => 0.47 | 3 => 0.46 | 4 => 0.45
  | 5 => 0.42 | 6 => 0.39 | 7 => 0.36 | 8 => 0.33 | _ => 0.32

def rowCount : ℕ → ℕ
  | 0 => 14000 | 1 => 1668 | 2 => 664 | 3 => 292 | 4 => 182
  | 5 => 89 | 6 => 35 | 7 => 20 | _ => 13

def rowBudget : ℕ → ℝ
  | 0 => 2e-18 | 1 => 6e-19 | 2 => 2e-18 | 3 => 2e-18 | 4 => 6e-17
  | 5 => 6e-16 | 6 => 8e-15 | 7 => 2e-13 | _ => 3e-13

theorem row_parameters {i : ℕ} (hi : i < 9) :
    0.1 ≤ breakpoint (i + 1) ∧ breakpoint (i + 1) ≤ breakpoint i ∧ breakpoint i ≤ 0.478 := by
  interval_cases i <;> norm_num [breakpoint]

theorem original_row_payment {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    {i : ℕ} (hi : i < 9) :
    (∫ alpha in cap N (breakpoint i)..cap N (breakpoint (i + 1)),
      (rowCount i : ℝ) * kernel N alpha) ≤ rowBudget i / sourceL N := by
  interval_cases i
  · exact original_211 hN
  · exact original_212a hN
  · exact original_212b hN
  · exact original_212c hN
  · exact original_212d hN
  · exact original_212e hN
  · exact original_212f hN
  · exact original_212g hN
  · exact original_212h hN

theorem countingFunction_antitone {ι : Type*} [Fintype ι]
    (Z : ι → Finset ℂ) (m : ι → ℂ → ℕ) : Antitone (countingFunction Z m) := by
  intro a b hab
  unfold countingFunction
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro rho hr
    obtain ⟨hr, hb⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨hr, hab.trans hb⟩
  · exact fun _ _ _ => Nat.cast_nonneg _

theorem countingFunction_nonneg {ι : Type*} [Fintype ι]
    (Z : ι → Finset ℂ) (m : ι → ℂ → ℕ) (alpha : ℝ) : 0 ≤ countingFunction Z m alpha :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

theorem actual_row_payment {ι : Type*} [Fintype ι] {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (Z : ι → Finset ℂ) (m : ι → ℂ → ℕ)
    {i : ℕ} (hi : i < 9)
    (hcount : countingFunction Z m (cap N (breakpoint i)) ≤ rowCount i) :
    (∫ alpha in cap N (breakpoint i)..cap N (breakpoint (i + 1)),
      kernel N alpha * countingFunction Z m alpha) ≤ rowBudget i / sourceL N := by
  obtain ⟨_, hba, ha⟩ := row_parameters hi
  have hp : 0 < cap N (breakpoint i) := by linarith [cap_ge_098 hN ha]
  have hab := cap_order hN hba
  apply le_trans _ (original_row_payment hN hi)
  apply intervalIntegral.integral_mono_on hab
    (counting_integrand_integrable (nat_pos_of_exp_le hN) hp hab Z m)
    ((kernel_integrable (nat_pos_of_exp_le hN) hp hab).const_mul _)
  intro alpha halpha
  rw [mul_comm (rowCount i : ℝ)]
  exact mul_le_mul_of_nonneg_left
    ((countingFunction_antitone Z m halpha.1).trans hcount)
    (kernel_nonneg (nat_pos_of_exp_le hN) (hp.trans_le halpha.1))

theorem actual_rows_payment {ι : Type*} [Fintype ι] {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (Z : ι → Finset ℂ) (m : ι → ℂ → ℕ)
    {n : ℕ} (hn : n ≤ 9)
    (hrows : ∀ i < n, countingFunction Z m (cap N (breakpoint i)) ≤ rowCount i) :
    (∫ alpha in cap N 0.478..cap N (breakpoint n),
      kernel N alpha * countingFunction Z m alpha) ≤
        (∑ i ∈ Finset.range n, rowBudget i) / sourceL N := by
  have hint (i : ℕ) (hi : i < n) :
      IntervalIntegrable (fun alpha => kernel N alpha * countingFunction Z m alpha) volume
        (cap N (breakpoint i)) (cap N (breakpoint (i + 1))) := by
    obtain ⟨_, hba, ha⟩ := row_parameters (hi.trans_le hn)
    exact counting_integrand_integrable (nat_pos_of_exp_le hN)
      (by linarith [cap_ge_098 hN ha]) (cap_order hN hba) Z m
  have he := intervalIntegral.sum_integral_adjacent_intervals hint
  change (∑ i ∈ Finset.range n, ∫ alpha in cap N (breakpoint i)..cap N (breakpoint (i + 1)),
    kernel N alpha * countingFunction Z m alpha) =
      ∫ alpha in cap N 0.478..cap N (breakpoint n),
        kernel N alpha * countingFunction Z m alpha at he
  rw [← he, Finset.sum_div]
  exact Finset.sum_le_sum fun i hi =>
    actual_row_payment hN Z m ((Finset.mem_range.mp hi).trans_le hn) (hrows i (Finset.mem_range.mp hi))

theorem original_first_eight {ι : Type*} [Fintype ι] {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (Z : ι → Finset ℂ) (m : ι → ℂ → ℕ)
    (hrows : ∀ i < 8, countingFunction Z m (cap N (breakpoint i)) ≤ rowCount i) :
    (∫ alpha in cap N 0.478..cap N 0.33,
      kernel N alpha * countingFunction Z m alpha) ≤ 3e-13 / sourceL N := by
  apply (actual_rows_payment hN Z m (by norm_num : 8 ≤ 9) hrows).trans
  apply div_le_div_of_nonneg_right _ (by linarith [sourceL_ge_3100 hN])
  norm_num [Finset.sum_range_succ, rowBudget]

theorem original_first_nine {ι : Type*} [Fintype ι] {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (Z : ι → Finset ℂ) (m : ι → ℂ → ℕ)
    (hrows : ∀ i < 9, countingFunction Z m (cap N (breakpoint i)) ≤ rowCount i) :
    (∫ alpha in cap N 0.478..cap N 0.32,
      kernel N alpha * countingFunction Z m alpha) ≤ 6e-13 / sourceL N := by
  apply (actual_rows_payment hN Z m (by norm_num : 9 ≤ 9) hrows).trans
  apply div_le_div_of_nonneg_right _ (by linarith [sourceL_ge_3100 hN])
  norm_num [Finset.sum_range_succ, rowBudget]

theorem counting_integral_zero_tail {ι : Type*} [Fintype ι]
    (N : ℕ) (Z : ι → Finset ℂ) (m : ι → ℂ → ℕ) {a b : ℝ}
    (hab : a ≤ b) (hz : countingFunction Z m a = 0) :
    (∫ alpha in a..b, kernel N alpha * countingFunction Z m alpha) = 0 := by
  calc
    _ = ∫ _ in a..b, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro alpha halpha
      rw [Set.uIcc_of_le hab] at halpha
      have h : countingFunction Z m alpha = 0 :=
        le_antisymm (by simpa only [hz] using countingFunction_antitone Z m halpha.1)
          (countingFunction_nonneg Z m alpha)
      dsimp only
      rw [h, mul_zero]
    _ = 0 := intervalIntegral.integral_zero

theorem original_213_from_counts {ι : Type*} [Fintype ι] {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (Z : ι → Finset ℂ) (m : ι → ℂ → ℕ)
    (hrows : ∀ i < 9, countingFunction Z m (cap N (breakpoint i)) ≤ rowCount i)
    (hz : countingFunction Z m (cap N 0.32) = 0) :
    (∫ alpha in bulkCap N..1, kernel N alpha * countingFunction Z m alpha) ≤
      6e-13 / sourceL N := by
  have ha : 0 < cap N 0.478 := by linarith [cap_ge_098 hN (by norm_num : (0.478 : ℝ) ≤ 0.478)]
  have hb : 0 < cap N 0.32 := by linarith [cap_ge_098 hN (by norm_num : (0.32 : ℝ) ≤ 0.478)]
  have hbc : cap N 0.32 ≤ 1 := by
    have hl : 0 ≤ Real.log (lowScale N) := by
      linarith [show 25.3294 ≤ Real.log (lowScale N) from original_log_scale_lower (sourceL_ge_3100 hN)]
    dsimp [cap]
    have := div_nonneg (by norm_num : (0 : ℝ) ≤ 0.32) hl
    linarith
  change (∫ alpha in cap N 0.478..1, kernel N alpha * countingFunction Z m alpha) ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (counting_integrand_integrable (nat_pos_of_exp_le hN) ha (cap_order hN (by norm_num)) Z m)
    (counting_integrand_integrable (nat_pos_of_exp_le hN) hb hbc Z m),
    counting_integral_zero_tail N Z m hbc hz, add_zero]
  exact original_first_nine hN Z m hrows

theorem exceptional_original_from_counts {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hrows : ∀ i < 9, retainedCount q (cap N (breakpoint i)) (omegaCutoff N q) d e ≤ rowCount i)
    (hz : retainedCount q (cap N 0.32) (omegaCutoff N q) d e = 0) :
    lowSum N q - (if d.modulus ∣ q then weight N e.re else 0) ≤ 8.2e-10 / sourceL N := by
  have htail := original_213_from_counts hN
    (fun chi : Character q => retainedValues chi (omegaCutoff N q) d e) zeroMultiplicity
    (fun i hi => by
      have hc : (retainedCount q (cap N (breakpoint i)) (omegaCutoff N q) d e : ℝ) ≤ rowCount i :=
        by exact_mod_cast hrows i hi
      simpa only [countingFunction, retainedCount, Nat.cast_sum] using hc)
    (by
      have hc : (retainedCount q (cap N 0.32) (omegaCutoff N q) d e : ℝ) = 0 := by exact_mod_cast hz
      simpa only [countingFunction, retainedCount, Nat.cast_sum] using hc)
  have he : (fun alpha => countingFunction
      (fun chi : Character q => retainedValues chi (omegaCutoff N q) d e) zeroMultiplicity alpha) =
      fun alpha => (retainedCount q alpha (omegaCutoff N q) d e : ℝ) := by
    funext alpha
    simp only [countingFunction, retainedCount, Nat.cast_sum]
  simp_rw [show ∀ alpha, countingFunction
      (fun chi : Character q => retainedValues chi (omegaCutoff N q) d e) zeroMultiplicity alpha =
      (retainedCount q alpha (omegaCutoff N q) d e : ℝ) from fun alpha => congrFun he alpha] at htail
  have h := (paper_primed_original_reduction hN hq hd).trans (add_le_add le_rfl htail)
  apply h.trans
  rw [← add_div]
  exact div_le_div_of_nonneg_right (by norm_num) (by linarith [sourceL_ge_3100 hN])

end LiuWang.Proof.SourceRoute.LowSum
