import LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual.FinalCost

/-! 原 lastValues 的整低高度范围消除、域外保留、精确有号费用和共享能量回归。 -/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual

open Interfaces Parameters ArcGeometry CompleteExpansion MajorArcApproximation MinorArcEnergy
open AnalyticNumberTheory.LargeSieve

theorem all_real_paid {N q : ℕ} [NeZero q] (chi : Character q) (positive : Bool)
    {rho : ℂ} (hr : rho ∈ lastValues chi N positive)
    (hq : (q : ℝ) ≤ realModulusLimit N) (hg : rho.im = 0) :
    rho ∈ allRealValues chi N positive ∧ rho ∉ restValues chi N positive := by
  constructor
  · exact Finset.mem_filter.mpr ⟨hr, hq, hg⟩
  · intro hh
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hh).1).2 ⟨hq, hg⟩

theorem all_low_nonreal_paid {N q : ℕ} [NeZero q] (chi : Character q) (positive : Bool)
    {rho : ℂ} (hr : rho ∈ lastValues chi N positive) (hq : (q : ℝ) ≤ realModulusLimit N)
    (hg : rho.im ≠ 0) (ht : |rho.im| ≤ lowHeight N q) :
    rho ∈ lowValues chi N positive ∧ rho ∉ restValues chi N positive := by
  constructor
  · exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hr, fun h => hg h.2⟩, hq, ht⟩
  · intro hh
    exact (Finset.mem_filter.mp hh).2 ⟨hq, ht⟩

theorem restValues_exact {N q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    (chi : Character q) (positive : Bool) {rho : ℂ} :
    rho ∈ restValues chi N positive ↔ rho ∈ lastValues chi N positive ∧
      ¬ ((q : ℝ) ≤ realModulusLimit N ∧ |rho.im| ≤ lowHeight N q) := by
  have ht : 0 ≤ lowHeight N q :=
    div_nonneg (omegaCutoff_pos (exp_2000_le_of_exp_3100_le hN) (NeZero.pos q)).le (by norm_num)
  constructor
  · intro hh
    exact ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hh).1).1, (Finset.mem_filter.mp hh).2⟩
  · rintro ⟨hr, hn⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hr, ?_⟩, hn⟩
    rintro ⟨hq, hg⟩
    exact hn ⟨hq, by simpa only [hg, abs_zero] using ht⟩

theorem whole_low_height_removed {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (chi : Character q) (positive : Bool)
    {rho : ℂ} (hq : (q : ℝ) ≤ realModulusLimit N) (ht : |rho.im| ≤ lowHeight N q) :
    rho ∉ restValues chi N positive := by
  intro hh
  exact ((restValues_exact hN chi positive).mp hh).2 ⟨hq, ht⟩

theorem outside_modulus_retained {N q : ℕ} [NeZero q] (chi : Character q) (positive : Bool)
    {rho : ℂ} (hq : realModulusLimit N < (q : ℝ)) :
    rho ∈ restValues chi N positive ↔ rho ∈ lastValues chi N positive := by
  simp only [restValues, afterRealValues, Finset.mem_filter, not_le_of_gt hq, false_and,
    not_false_eq_true, and_true]

theorem outside_height_retained {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (chi : Character q) (positive : Bool)
    {rho : ℂ} (ht : lowHeight N q < |rho.im|) :
    rho ∈ restValues chi N positive ↔ rho ∈ lastValues chi N positive := by
  rw [restValues_exact hN chi positive]
  simp only [not_le_of_gt ht, and_false, not_false_eq_true, and_true]

theorem original_small_moduli_included {N q : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hq : (q : ℝ) ≤ sourceL N) : (q : ℝ) ≤ realModulusLimit N := by
  unfold realModulusLimit
  nlinarith [sourceL_ge_3100 hN]

theorem last_values_partition {N q : ℕ} [NeZero q] (chi : Character q) (positive : Bool) :
    lastValues chi N positive =
      allRealValues chi N positive ∪ lowValues chi N positive ∪ restValues chi N positive := by
  ext rho
  simp only [allRealValues, lowValues, restValues, afterRealValues,
    Finset.mem_filter, Finset.mem_union]
  tauto

theorem paid_disjoint {N q : ℕ} [NeZero q] (chi : Character q) (positive : Bool) :
    Disjoint (allRealValues chi N positive) (lowValues chi N positive) := by
  apply Finset.disjoint_left.mpr
  intro rho hr hl
  exact low_nonreal hl (Finset.mem_filter.mp hr).2.2

theorem real_rest_disjoint {N q : ℕ} [NeZero q] (chi : Character q) (positive : Bool) :
    Disjoint (allRealValues chi N positive) (restValues chi N positive) := by
  apply Finset.disjoint_left.mpr
  intro rho hr hl
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hl).1).2 (Finset.mem_filter.mp hr).2

theorem low_rest_disjoint {N q : ℕ} [NeZero q] (chi : Character q) (positive : Bool) :
    Disjoint (lowValues chi N positive) (restValues chi N positive) := by
  apply Finset.disjoint_left.mpr
  intro rho hr hl
  exact (Finset.mem_filter.mp hl).2 (Finset.mem_filter.mp hr).2

theorem lastPacket_exact_three {q : ℕ} [NeZero q] (N a : ℕ) (positive : Bool) (eta : ℝ) :
    lastPacket q N a positive eta =
      realPacketOn q a (fun chi => allRealValues chi N positive) N eta +
        realPacketOn q a (fun chi => lowValues chi N positive) N eta +
          realPacketOn q a (fun chi => restValues chi N positive) N eta := by
  rw [lastPacket_eq_real_add_after, afterRealPacket_eq_low_add_rest, add_assoc]

theorem selectedRest_eq_values {q : ℕ} [NeZero q] (N a : ℕ) (eta : ℝ) :
    selectedRest N a q eta =
      (q.totient : ℂ)⁻¹ * ∑ chi : Character q, CharacterExpansion.G a chi *
        ∑ rho ∈ restValues chi N (if 0 ≤ eta then true else false),
          (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta := by
  by_cases he : 0 ≤ eta <;> simp [selectedRest, restPart_eq, realPacketOn, he]

theorem restShellCost_eq_values {q : ℕ} [NeZero q] (N a : ℕ) :
    restShellCost N a q =
      ∫ alpha in shell N a q,
        ‖(q.totient : ℂ)⁻¹ * ∑ chi : Character q, CharacterExpansion.G a chi *
          ∑ rho ∈ restValues chi N (if 0 ≤ alpha - rationalCenter a q then true else false),
            (analyticOrderNatAt chi.LFunction rho : ℂ) *
              Jrho N rho (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2 := by
  unfold restShellCost
  simp only [selectedRest_eq_values]

theorem lastCost_le_paid_shared_energy {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    lastCost N ≤ newFee N *
      ((∑ n ∈ windowFinset N, ArithmeticFunction.vonMangoldt n ^ 2) -
        (∫ alpha in M1 N, ‖S N alpha‖ ^ 2) -
        (∫ alpha in M3 N, ‖S N alpha‖ ^ 2) -
        (∫ alpha in M4 N, ‖S N alpha‖ ^ 2)) + restCost N := by
  have he := minor_energy_eq_source_sub_major (exp_2000_le_of_exp_3100_le hN)
  rw [source_energy_eq] at he
  have hh : (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) =
      (∑ n ∈ windowFinset N, ArithmeticFunction.vonMangoldt n ^ 2) -
        (∫ alpha in M1 N, ‖S N alpha‖ ^ 2) -
        (∫ alpha in M3 N, ‖S N alpha‖ ^ 2) -
        (∫ alpha in M4 N, ‖S N alpha‖ ^ 2) := by linarith
  rw [← hh]
  exact lastCost_le_full_paid_rest hN

theorem fullFee_le_old_decimal_plus_new {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    fullFee N ≤ 0.1156 * (N : ℝ) / sourceL N + newFee N := by
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  have h1 : (21 : ℝ) / sourceL N ≤ 21 / 3100 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (sourceL_ge_3100 hN)
  have h2 : (280000 : ℝ) / sourceL N ^ 2 ≤ 280000 / 3100 ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (pow_le_pow_left₀ (by norm_num) (sourceL_ge_3100 hN) 2)
  have hc : 0.0786 + 280000 / sourceL N ^ 2 + 21 / sourceL N ≤ (0.1156 : ℝ) := by
    linarith only [h1, h2]
  have hm := mul_le_mul_of_nonneg_right hc (div_nonneg (Nat.cast_nonneg N) hL.le)
  have he : fullFee N =
      (0.0786 + 280000 / sourceL N ^ 2 + 21 / sourceL N) * ((N : ℝ) / sourceL N) + newFee N := by
    unfold fullFee totalFee frontierFee newFee
    field_simp
    ring
  rw [he]
  simpa only [mul_div_assoc] using add_le_add hm (le_rfl : newFee N ≤ newFee N)

theorem M2_integral_le_4012_of_restCost {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hz : restCost N ≤ (0.0759 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2)) :
    ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
      (0.4012 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) := by
  apply (M2_integral_le_3253_rest hN).trans
  apply (add_le_add le_rfl hz).trans_eq
  ring

end LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual
