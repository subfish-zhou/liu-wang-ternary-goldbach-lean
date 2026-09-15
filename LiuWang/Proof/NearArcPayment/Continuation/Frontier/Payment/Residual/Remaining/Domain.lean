import LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual.Regression

/-! 全模数原低高度余族；三段实部只用于已接计数，不留下实部缺口。 -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual.Remaining

open Interfaces Parameters ArcGeometry CompleteExpansion NearOneDensity

def outerAlpha (N : ℕ) : ℝ := 1 - 0.478 / Real.log (realScale N)

def innerWeight (N : ℕ) : ℝ := (0.001 * (N : ℝ)) ^ (realAlpha N - 1)

def outerWeight (N : ℕ) : ℝ := (0.001 * (N : ℝ)) ^ (outerAlpha N - 1)

def largeLowValues {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ) (positive : Bool) : Finset ℂ :=
  (restValues chi N positive).filter (fun rho => |rho.im| ≤ lowHeight N q)

def highValues {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ) (positive : Bool) : Finset ℂ :=
  (restValues chi N positive).filter (fun rho => lowHeight N q < |rho.im|)

def closeValues {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ) (positive : Bool) : Finset ℂ :=
  (largeLowValues chi N positive).filter (fun rho => realAlpha N ≤ rho.re)

def middleValues {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ) (positive : Bool) : Finset ℂ :=
  (largeLowValues chi N positive).filter (fun rho => rho.re < realAlpha N ∧ outerAlpha N ≤ rho.re)

def leftValues {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ) (positive : Bool) : Finset ℂ :=
  (largeLowValues chi N positive).filter (fun rho => rho.re < realAlpha N ∧ rho.re < outerAlpha N)

theorem largeLow_modulus {N q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    {chi : Character q} {positive : Bool} {rho : ℂ} (hr : rho ∈ largeLowValues chi N positive) :
    realModulusLimit N < (q : ℝ) := by
  obtain ⟨hr, ht⟩ := Finset.mem_filter.mp hr
  have hn := ((restValues_exact hN chi positive).mp hr).2
  exact lt_of_not_ge (fun hq => hn ⟨hq, ht⟩)

theorem largeLow_empty {N q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    (hq : (q : ℝ) ≤ realModulusLimit N) (chi : Character q) (positive : Bool) :
    largeLowValues chi N positive = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  exact fun _ hr => (not_lt_of_ge hq) (largeLow_modulus hN hr)

theorem largeLow_subset_zero {N q : ℕ} [NeZero q] (chi : Character q) (positive : Bool) :
    largeLowValues chi N positive ⊆ CompleteExpansion.zeroValues chi (lowHeight N q) := by
  intro rho hr
  obtain ⟨hr, ht⟩ := Finset.mem_filter.mp hr
  have hl := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1
  have hh := ((lastValues_exact chi positive).mp hl).1
  have hf := (Finset.mem_filter.mp (Finset.mem_filter.mp hh).1).1
  obtain ⟨hz, h0, h1, _, hb, _⟩ := (finalValues_literal chi).mp hf
  exact mem_zeroValues.mpr ⟨hz, h0, h1, ht, by linarith⟩

theorem full_modulus_density_domain {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    100000000000 ≤ realScale N ∧ (q : ℝ) * max 1 (lowHeight N q) ≤ realScale N := by
  have hN0 := exp_2000_le_of_exp_3100_le hN
  have hL := sourceL_pos hN0
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hp : sourceP N ≤ realScale N := by
    exact pow_le_pow_right₀ (one_le_sourceL hN0) (by norm_num : 3 ≤ 4)
  refine ⟨(real_domain hN0 (q := 0) (by simpa only [Nat.cast_zero] using hL.le)).1, ?_⟩
  rcases le_total (lowHeight N q) 1 with hy | hy
  · rw [max_eq_left hy, mul_one]
    exact hq.trans hp
  · rw [max_eq_right hy]
    have he : (q : ℝ) * lowHeight N q = (3.36 / 10000 : ℝ) * sourceP N := by
      unfold lowHeight omegaCutoff
      field_simp
    rw [he]
    exact (mul_le_of_le_one_left (sourceP_pos hN0).le (by norm_num)).trans hp

theorem close_count {N q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    (hq : (q : ℝ) ≤ sourceP N) (positive : Bool) :
    (∑ chi : Character q, ∑ rho ∈ closeValues chi N positive,
      (analyticOrderNatAt chi.LFunction rho : ℝ)) ≤ 7 := by
  obtain ⟨hz, hqy⟩ := full_modulus_density_domain hN hq
  have hr := NearOneDensity.Continuation.complete_tail_count_row .r027 hz hqy
    (alpha := realAlpha N) (by rfl)
  have hc : (∑ chi : Character q,
      ∑ rho ∈ (CompleteExpansion.zeroValues chi (lowHeight N q)).filter (fun rho => realAlpha N ≤ rho.re),
        (analyticOrderNatAt chi.LFunction rho : ℝ)) ≤ 7 := by
    norm_num [rowBound, rowMultiplicity, rowSelectedBound] at hr
    exact_mod_cast hr
  apply le_trans _ hc
  apply Finset.sum_le_sum
  intro chi _
  apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => Nat.cast_nonneg _)
  intro rho hr
  obtain ⟨hr, hb⟩ := Finset.mem_filter.mp hr
  exact Finset.mem_filter.mpr ⟨largeLow_subset_zero chi positive hr, hb⟩

theorem middle_count {N q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    (hq : (q : ℝ) ≤ sourceP N) (positive : Bool) :
    (∑ chi : Character q, ∑ rho ∈ middleValues chi N positive,
      (analyticOrderNatAt chi.LFunction rho : ℝ)) ≤ 14000 := by
  obtain ⟨hz, hqy⟩ := full_modulus_density_domain hN hq
  have hr := NearOneDensity.Continuation.complete_tail_count_row .r0478 hz hqy
    (alpha := outerAlpha N) (by rfl)
  have hc : (∑ chi : Character q,
      ∑ rho ∈ (CompleteExpansion.zeroValues chi (lowHeight N q)).filter (fun rho => outerAlpha N ≤ rho.re),
        (analyticOrderNatAt chi.LFunction rho : ℝ)) ≤ 14000 := by
    norm_num [rowBound, rowMultiplicity, rowSelectedBound] at hr
    exact_mod_cast hr
  apply le_trans _ hc
  apply Finset.sum_le_sum
  intro chi _
  apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => Nat.cast_nonneg _)
  intro rho hr
  obtain ⟨hr, _, hb⟩ := Finset.mem_filter.mp hr
  exact Finset.mem_filter.mpr ⟨largeLow_subset_zero chi positive hr, hb⟩

theorem left_count_sharp {N q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    (chi : Character q) (positive : Bool) :
    (∑ rho ∈ leftValues chi N positive, (analyticOrderNatAt chi.LFunction rho : ℝ)) ≤
      sharpCount chi (lowHeight N q) := by
  apply le_trans _ (complete_count_le_sharp chi (div_nonneg
    (omegaCutoff_pos (exp_2000_le_of_exp_3100_le hN) (NeZero.pos q)).le (by norm_num)))
  exact Finset.sum_le_sum_of_subset_of_nonneg
    ((Finset.filter_subset _ _).trans (largeLow_subset_zero chi positive))
    (fun _ _ _ => Nat.cast_nonneg _)

theorem innerWeight_le_log_cube {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    innerWeight N ≤ 1 / sourceL N ^ 3 := left_low_weight hN le_rfl

theorem outerWeight_le_log_fifth {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    outerWeight N ≤ 1 / sourceL N ^ 5 := by
  have hN0 := exp_2000_le_of_exp_3100_le hN
  have hL := sourceL_pos hN0
  have hl : 0 < Real.log (sourceL N) := Real.log_pos (by linarith [sourceL_ge_3100 hN])
  have hw := sourceWindow_gt_one hN0
  have hlw : 0 < Real.log (0.001 * (N : ℝ)) := Real.log_pos hw
  have hs := log_square_strong (sourceL_ge_3100 hN)
  have hprod : 20 * Real.log (sourceL N) ^ 2 ≤ 0.478 * Real.log (0.001 * (N : ℝ)) := by
    nlinarith [window_log_lower hN, sourceL_ge_3100 hN]
  have hd : 5 * Real.log (sourceL N) ≤
      0.478 * Real.log (0.001 * (N : ℝ)) / (4 * Real.log (sourceL N)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith only [hprod]
  unfold outerWeight outerAlpha realScale
  rw [Real.rpow_def_of_pos (by linarith : 0 < 0.001 * (N : ℝ)), Real.log_pow]
  simp only [Nat.cast_ofNat]
  have he : Real.log (0.001 * (N : ℝ)) * (1 - 0.478 / (4 * Real.log (sourceL N)) - 1) =
      -(0.478 * Real.log (0.001 * (N : ℝ)) / (4 * Real.log (sourceL N))) := by ring
  rw [he]
  calc
    _ ≤ Real.exp (-(5 * Real.log (sourceL N))) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by
      rw [Real.exp_neg, show 5 * Real.log (sourceL N) = Real.log (sourceL N ^ 5) by
        rw [Real.log_pow]; norm_num, Real.exp_log (pow_pos hL 5)]
      simp only [one_div]

end LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual.Remaining
