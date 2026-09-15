import LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.FinalCost

/-! 表有效域、全近一高尾、实零付款、符号分割与共同能量的实际回归。 -/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment

open Interfaces Parameters ArcGeometry CompleteExpansion
open MajorArcApproximation MinorArcEnergy

theorem density_nonreal {N q : ℕ} [NeZero q] (hN : Real.exp 2000 ≤ (N : ℝ))
    {chi : Character q} {rho : ℂ} {positive : Bool} (hr : rho ∈ densityValues chi N positive) :
    rho.im ≠ 0 := by
  rcases (Finset.mem_filter.mp hr).2.2 with hh | ⟨hh, _⟩
  · exact abs_pos.mp ((pow_pos (sourceL_pos hN) 6).trans_le hh)
  · exact abs_pos.mp ((pow_pos (sourceL_pos hN) 4).trans_le hh)

theorem densityAlpha_lt_one {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    densityAlpha N < 1 := by
  have hl : 0 < Real.log (densityScale N) := by
    rw [densityScale, Real.log_pow]
    have hh : 0 < Real.log (sourceL N) := Real.log_pos (by linarith [sourceL_ge_2000 hN])
    positivity
  unfold densityAlpha
  have hp : 0 < 0.478 / Real.log (densityScale N) := by positivity
  linarith

theorem entire_high_near_one_paid {N q : ℕ} [NeZero q]
    (chi : Character q) (positive : Bool) {rho : ℂ} (hr : rho ∈ tailValues chi N positive)
    (hb : densityAlpha N ≤ rho.re) (hh : sourceL N ^ 6 ≤ |rho.im|) :
    rho ∈ densityValues chi N positive ∧ rho ∉ lastValues chi N positive := by
  constructor
  · exact Finset.mem_filter.mpr ⟨hr, hb, Or.inl hh⟩
  · intro hu
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).2 ⟨hb, Or.inl hh⟩

theorem actual_real_family_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (chi : Character q) (positive : Bool)
    {rho : ℂ} (hr : rho ∈ tailValues chi N positive) (hq : (q : ℝ) ≤ sourceL N)
    (hg : rho.im = 0) (hb : realAlpha N ≤ rho.re) :
    rho ∈ realValues chi N positive ∧ rho ∉ lastValues chi N positive := by
  have hd : rho ∉ densityValues chi N positive := fun h => density_nonreal hN h hg
  have hn : ¬ (densityAlpha N ≤ rho.re ∧
      (sourceL N ^ 6 ≤ |rho.im| ∨
        (sourceL N ^ 4 ≤ |rho.im| ∧ if positive then 0 < rho.im else rho.im < 0))) :=
    fun hh => hd (Finset.mem_filter.mpr ⟨hr, hh⟩)
  have hm : rho ∈ residualValues chi N positive := Finset.mem_filter.mpr ⟨hr, hn⟩
  constructor
  · exact Finset.mem_filter.mpr ⟨hm, hq, hg, hb⟩
  · intro hh
    exact (Finset.mem_filter.mp hh).2 ⟨hq, hg, hb⟩

theorem real_outside_range_retained {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (chi : Character q) (positive : Bool)
    {rho : ℂ} (hg : rho.im = 0) (hq : sourceL N < (q : ℝ) ∨ rho.re < realAlpha N) :
    rho ∈ lastValues chi N positive ↔ rho ∈ tailValues chi N positive := by
  constructor
  · intro hh
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hh).1).1
  · intro ht
    have hd : rho ∉ densityValues chi N positive := fun h => density_nonreal hN h hg
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨ht, ?_⟩, ?_⟩
    · exact fun hh => hd (Finset.mem_filter.mpr ⟨ht, hh⟩)
    · intro hh
      rcases hq with hq | hq
      · exact (not_le_of_gt hq) hh.1
      · exact (not_le_of_gt hq) hh.2.2

theorem tail_values_partition {N q : ℕ} [NeZero q]
    (chi : Character q) (positive : Bool) :
    tailValues chi N positive =
      densityValues chi N positive ∪ realValues chi N positive ∪ lastValues chi N positive := by
  ext rho
  simp only [densityValues, residualValues, realValues, lastValues,
    Finset.mem_filter, Finset.mem_union]
  tauto

theorem density_real_disjoint {N q : ℕ} [NeZero q]
    (chi : Character q) (positive : Bool) :
    Disjoint (densityValues chi N positive) (realValues chi N positive) := by
  apply Finset.disjoint_left.mpr
  intro rho hd hr
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2 (Finset.mem_filter.mp hd).2

theorem real_last_disjoint {N q : ℕ} [NeZero q]
    (chi : Character q) (positive : Bool) :
    Disjoint (realValues chi N positive) (lastValues chi N positive) := by
  apply Finset.disjoint_left.mpr
  intro rho hr hl
  exact (Finset.mem_filter.mp hl).2 (Finset.mem_filter.mp hr).2

theorem density_last_disjoint {N q : ℕ} [NeZero q]
    (chi : Character q) (positive : Bool) :
    Disjoint (densityValues chi N positive) (lastValues chi N positive) := by
  apply Finset.disjoint_left.mpr
  intro rho hd hl
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hl).1).2 (Finset.mem_filter.mp hd).2

theorem lastValues_exact {N q : ℕ} [NeZero q]
    (chi : Character q) (positive : Bool) {rho : ℂ} :
    rho ∈ lastValues chi N positive ↔ rho ∈ tailValues chi N positive ∧
      ¬ (densityAlpha N ≤ rho.re ∧
        (sourceL N ^ 6 ≤ |rho.im| ∨
          (sourceL N ^ 4 ≤ |rho.im| ∧ if positive then 0 < rho.im else rho.im < 0))) ∧
      ¬ ((q : ℝ) ≤ sourceL N ∧ rho.im = 0 ∧ realAlpha N ≤ rho.re) := by
  simp only [lastValues, residualValues, Finset.mem_filter]
  tauto

theorem selectedLast_eq_values {q : ℕ} [NeZero q] (N a : ℕ) (eta : ℝ) :
    selectedLast N a q eta =
      (q.totient : ℂ)⁻¹ * ∑ chi : Character q, CharacterExpansion.G a chi *
        ∑ rho ∈ lastValues chi N (if 0 ≤ eta then true else false),
          (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta := by
  by_cases he : 0 ≤ eta <;> simp [selectedLast, lastPart_eq, lastPacket, he]

theorem lastShellCost_eq_values {q : ℕ} [NeZero q] (N a : ℕ) :
    lastShellCost N a q =
      ∫ alpha in shell N a q,
        ‖(q.totient : ℂ)⁻¹ * ∑ chi : Character q, CharacterExpansion.G a chi *
          ∑ rho ∈ lastValues chi N (if 0 ≤ alpha - rationalCenter a q then true else false),
            (analyticOrderNatAt chi.LFunction rho : ℂ) *
              Jrho N rho (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2 := by
  unfold lastShellCost
  simp only [selectedLast_eq_values]

theorem zero_height_domain_not_qy (q : ℕ) :
    (q : ℝ) * max 1 (0 : ℝ) = q := by norm_num

theorem frontierCost_le_paid_shared_energy {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    frontierCost N ≤ (0.037 * (N : ℝ) / sourceL N) *
      ((∑ n ∈ windowFinset N, ArithmeticFunction.vonMangoldt n ^ 2) -
        (∫ alpha in M1 N, ‖S N alpha‖ ^ 2) -
        (∫ alpha in M3 N, ‖S N alpha‖ ^ 2) -
        (∫ alpha in M4 N, ‖S N alpha‖ ^ 2)) + lastCost N := by
  have he := minor_energy_eq_source_sub_major (exp_2000_le_of_exp_3100_le hN)
  rw [source_energy_eq] at he
  have hh : (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) =
      (∑ n ∈ windowFinset N, ArithmeticFunction.vonMangoldt n ^ 2) -
        (∫ alpha in M1 N, ‖S N alpha‖ ^ 2) -
        (∫ alpha in M3 N, ‖S N alpha‖ ^ 2) -
        (∫ alpha in M4 N, ‖S N alpha‖ ^ 2) := by linarith
  rw [← hh]
  exact frontierCost_le_density_real_paid hN

end LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment
