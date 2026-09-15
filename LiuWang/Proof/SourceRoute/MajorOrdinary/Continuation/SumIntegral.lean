import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.Nu

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset MeasureTheory Set
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters LiuWang.Proof.SingularSeries

namespace LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation

theorem nuKernel_intervalIntegrable (s : ℝ) {a b : ℝ}
    (ha : 100000 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (nuKernel s) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  exact (nuKernel_continuousOn s).mono (fun _ h => ha.trans h.1)

theorem sum_Icc_shift (f : ℕ → ℝ) (m b : ℕ) :
    (∑ q ∈ Finset.Icc (m + 1) b, f q) = ∑ q ∈ Finset.Ico m b, f (q + 1) := by
  symm
  apply Finset.sum_bij (fun q _ => q + 1)
  · intro q hq
    exact Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Ico.mp hq).1; omega,
      by have := (Finset.mem_Ico.mp hq).2; omega⟩
  · intro q _ r _ h
    omega
  · intro q hq
    refine ⟨q - 1, Finset.mem_Ico.mpr ⟨?_, ?_⟩, ?_⟩ <;>
      have := Finset.mem_Icc.mp hq <;> omega
  · intros
    rfl

theorem nuKernel_sum_le_integral {s : ℝ} (hs : s ≤ 7 / 6)
    {m b : ℕ} (hm : 100000 ≤ m) (hmb : m ≤ b) :
    (∑ q ∈ Finset.Icc (m + 1) b, nuKernel s q) ≤
      ∫ x in (m : ℝ)..(b : ℝ), nuKernel s x := by
  rw [sum_Icc_shift]
  apply AntitoneOn.sum_le_integral_Ico hmb
  exact (nuKernel_antitoneOn hs).mono (fun _ h => (by exact_mod_cast hm : (100000 : ℝ) ≤ m).trans h.1)

theorem nuKernel_sum_le_integral_real {s P : ℝ} (hs : s ≤ 7 / 6)
    (hP : 100000 ≤ P) :
    (∑ q ∈ Finset.Icc 100001 ⌊P⌋₊, nuKernel s q) ≤
      ∫ x in (100000 : ℝ)..P, nuKernel s x := by
  have hfloor : 100000 ≤ ⌊P⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by exact_mod_cast hP)
  have hcast : (100000 : ℝ) ≤ (⌊P⌋₊ : ℝ) := by exact_mod_cast hfloor
  apply (nuKernel_sum_le_integral hs (by norm_num) hfloor).trans
  apply intervalIntegral.integral_mono_interval le_rfl hcast (Nat.floor_le (by linarith))
    _ (nuKernel_intervalIntegrable s le_rfl hP)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact nuKernel_nonneg (by linarith [hx.1]) s

theorem totient_term_le_nuKernel {q : ℕ} {s : ℝ} (hq : 100000 ≤ (q : ℝ))
    (hRS : (q : ℝ) / (q.totient : ℝ) ≤ nu q) :
    (q : ℝ) ^ s / (q.totient : ℝ) ^ 2 ≤ nuKernel s q := by
  have hq0 : 0 < (q : ℝ) := by linarith
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ (q : ℝ) / (q.totient : ℝ)) hRS 2
  calc
    _ = (q : ℝ) ^ (s - 2) * ((q : ℝ) / (q.totient : ℝ)) ^ 2 := by
      rw [Real.rpow_sub hq0, Real.rpow_ofNat, div_pow]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hq0.le _)

theorem totient_tail_le_source_integral {s P : ℝ} (hs : s ≤ 7 / 6)
    (hP : 100000 ≤ P)
    (hRS : ∀ q ∈ Finset.Icc 100001 ⌊P⌋₊, (q : ℝ) / (q.totient : ℝ) ≤ nu q) :
    (∑ q ∈ Finset.Icc 100001 ⌊P⌋₊, (q : ℝ) ^ s / (q.totient : ℝ) ^ 2) ≤
      ∫ x in (100000 : ℝ)..P, nuKernel s x := by
  apply (Finset.sum_le_sum (fun q hq => totient_term_le_nuKernel
    (by have := (Finset.mem_Icc.mp hq).1; exact_mod_cast (by omega : 100000 ≤ q))
    (hRS q hq))).trans
  exact nuKernel_sum_le_integral_real hs hP

theorem source_integral_split {s P : ℝ} (hP : 10000000000 ≤ P) :
    (∫ x in (100000 : ℝ)..P, nuKernel s x) =
      (∫ x in (100000 : ℝ)..10000000000, nuKernel s x) +
      ∫ x in (10000000000 : ℝ)..P, nuKernel s x :=
  (intervalIntegral.integral_add_adjacent_intervals
    (nuKernel_intervalIntegrable s le_rfl (by norm_num))
    (nuKernel_intervalIntegrable s (by norm_num) hP)).symm

theorem source419_comparison {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hRS : ∀ q ∈ Finset.Icc 100001 ⌊sourceP N⌋₊,
      (q : ℝ) / (q.totient : ℝ) ≤ nu q) :
    (∑ q ∈ Finset.Icc 100001 ⌊sourceP N⌋₊,
      (q : ℝ) ^ (1 / 6 : ℝ) / (q.totient : ℝ) ^ 2) ≤
      (∫ x in (100000 : ℝ)..10000000000, nuKernel (1 / 6) x) +
      ∫ x in (10000000000 : ℝ)..sourceP N, nuKernel (1 / 6) x := by
  rw [← source_integral_split (sourceP_ge_ten_billion hN)]
  exact totient_tail_le_source_integral (by norm_num)
    ((by norm_num : (100000 : ℝ) ≤ 10000000000).trans (sourceP_ge_ten_billion hN)) hRS

theorem source422_comparison {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hRS : ∀ q ∈ Finset.Icc 100001 ⌊sourceP N⌋₊,
      (q : ℝ) / (q.totient : ℝ) ≤ nu q) :
    (∑ q ∈ Finset.Icc 100001 ⌊sourceP N⌋₊,
      (q : ℝ) ^ (7 / 6 : ℝ) / (q.totient : ℝ) ^ 2) ≤
      (∫ x in (100000 : ℝ)..10000000000, nuKernel (7 / 6) x) +
      ∫ x in (10000000000 : ℝ)..sourceP N, nuKernel (7 / 6) x := by
  rw [← source_integral_split (sourceP_ge_ten_billion hN)]
  exact totient_tail_le_source_integral le_rfl
    ((by norm_num : (100000 : ℝ) ≤ 10000000000).trans (sourceP_ge_ten_billion hN)) hRS

end LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation
