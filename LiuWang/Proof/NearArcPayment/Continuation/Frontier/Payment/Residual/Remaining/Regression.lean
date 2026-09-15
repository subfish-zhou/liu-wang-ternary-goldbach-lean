import LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual.Remaining.Consumer

/-! 所有模数的低高度/实零消除，剩余严格非实；层费用与精确原对象的边界回归。 -/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual.Remaining

open Interfaces Parameters ArcGeometry CompleteExpansion MajorArcApproximation MinorArcEnergy
open AnalyticNumberTheory.LargeSieve

theorem highValues_exact {N q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    (chi : Character q) (positive : Bool) {rho : ℂ} :
    rho ∈ highValues chi N positive ↔ rho ∈ lastValues chi N positive ∧ lowHeight N q < |rho.im| := by
  simp only [highValues, Finset.mem_filter, restValues_exact hN chi positive]
  constructor
  · rintro ⟨⟨hr, _⟩, ht⟩
    exact ⟨hr, ht⟩
  · rintro ⟨hr, ht⟩
    exact ⟨⟨hr, fun h => (not_le_of_gt ht) h.2⟩, ht⟩

theorem largeLow_exact {N q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    (chi : Character q) (positive : Bool) {rho : ℂ} :
    rho ∈ largeLowValues chi N positive ↔ rho ∈ lastValues chi N positive ∧
      realModulusLimit N < (q : ℝ) ∧ |rho.im| ≤ lowHeight N q := by
  constructor
  · intro hr
    have hh := Finset.mem_filter.mp hr
    exact ⟨((restValues_exact hN chi positive).mp hh.1).1, largeLow_modulus hN hr, hh.2⟩
  · rintro ⟨hr, hq, ht⟩
    exact Finset.mem_filter.mpr ⟨(restValues_exact hN chi positive).mpr
      ⟨hr, fun h => (not_le_of_gt hq) h.1⟩, ht⟩

theorem high_nonreal {N q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    {chi : Character q} {positive : Bool} {rho : ℂ} (hr : rho ∈ highValues chi N positive) :
    rho.im ≠ 0 := by
  have hy : 0 < lowHeight N q :=
    div_pos (omegaCutoff_pos (exp_2000_le_of_exp_3100_le hN) (NeZero.pos q)) (by norm_num)
  exact abs_pos.mp (hy.trans (Finset.mem_filter.mp hr).2)

theorem all_real_removed {N q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    (chi : Character q) (positive : Bool) {rho : ℂ} (hg : rho.im = 0) :
    rho ∉ highValues chi N positive := fun hr => high_nonreal hN hr hg

theorem full_low_closed_endpoint_removed {N q : ℕ} [NeZero q]
    (chi : Character q) (positive : Bool) {rho : ℂ} (ht : |rho.im| ≤ lowHeight N q) :
    rho ∉ highValues chi N positive := fun hr => (not_lt_of_ge ht) (Finset.mem_filter.mp hr).2

theorem above_height_retained {N q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    (chi : Character q) (positive : Bool) {rho : ℂ} (ht : lowHeight N q < |rho.im|) :
    rho ∈ highValues chi N positive ↔ rho ∈ lastValues chi N positive := by
  rw [highValues_exact hN chi positive]
  simp only [ht, and_true]

theorem rest_partition {N q : ℕ} [NeZero q] (chi : Character q) (positive : Bool) :
    restValues chi N positive = largeLowValues chi N positive ∪ highValues chi N positive := by
  ext rho
  simp only [largeLowValues, highValues, Finset.mem_filter, Finset.mem_union]
  constructor
  · intro hr
    rcases le_total |rho.im| (lowHeight N q) with ht | ht
    · exact Or.inl ⟨hr, ht⟩
    · by_cases he : |rho.im| = lowHeight N q
      · exact Or.inl ⟨hr, he.le⟩
      · exact Or.inr ⟨hr, lt_of_le_of_ne ht (Ne.symm he)⟩
  · rintro (h | h) <;> exact h.1

theorem rest_partition_disjoint {N q : ℕ} [NeZero q] (chi : Character q) (positive : Bool) :
    Disjoint (largeLowValues chi N positive) (highValues chi N positive) := by
  apply Finset.disjoint_left.mpr
  intro rho hl hh
  exact (not_lt_of_ge (Finset.mem_filter.mp hl).2) (Finset.mem_filter.mp hh).2

theorem selectedHigh_eq_values {q : ℕ} [NeZero q] (N a : ℕ) (eta : ℝ) :
    selectedHigh N a q eta =
      (q.totient : ℂ)⁻¹ * ∑ chi : Character q, CharacterExpansion.G a chi *
        ∑ rho ∈ highValues chi N (if 0 ≤ eta then true else false),
          (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta := by
  by_cases he : 0 ≤ eta <;> simp [selectedHigh, highPart_eq, realPacketOn, he]

theorem highShellCost_eq_values {q : ℕ} [NeZero q] (N a : ℕ) :
    highShellCost N a q =
      ∫ alpha in shell N a q,
        ‖(q.totient : ℂ)⁻¹ * ∑ chi : Character q, CharacterExpansion.G a chi *
          ∑ rho ∈ highValues chi N (if 0 ≤ alpha - rationalCenter a q then true else false),
            (analyticOrderNatAt chi.LFunction rho : ℂ) *
              Jrho N rho (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2 := by
  unfold highShellCost
  simp only [selectedHigh_eq_values]

theorem packetFee_literal {q : ℕ} [NeZero q] (N a : ℕ) :
    packetFee N a q =
      (9 * (q : ℝ) * (N : ℝ) / sourceL N ^ 3) *
        ((min (Real.sqrt (q : ℝ)) (q.totient : ℝ) / (q.totient : ℝ)) *
          (7 + 14000 * (0.001 * (N : ℝ)) ^ (realAlpha N - 1)) +
          (0.001 * (N : ℝ)) ^ (outerAlpha N - 1) *
            ((q.totient : ℝ)⁻¹ * ∑ chi : Character q, ‖CharacterExpansion.G a chi‖ *
              sharpCount chi (lowHeight N q))) := rfl

theorem packetFee_nonneg {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (a : ℕ) : 0 ≤ packetFee N a q := by
  have hP := sourceP_pos (exp_2000_le_of_exp_3100_le hN)
  have hy : 0 ≤ lowHeight N q := div_nonneg
    (omegaCutoff_pos (exp_2000_le_of_exp_3100_le hN) (NeZero.pos q)).le (by norm_num)
  have hs : 0 ≤ sharpGaussMass q a (lowHeight N q) := by
    unfold sharpGaussMass
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro chi _
    apply mul_nonneg (norm_nonneg _)
    exact (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)).trans (complete_count_le_sharp chi hy)
  unfold packetFee lowKernel innerWeight outerWeight gaussCap
  positivity

theorem layerCost_nonneg {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) : 0 ≤ layerCost N := by
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg _ (integral_nonneg (fun _ => sq_nonneg _))
  unfold layerFee
  split_ifs with hq
  · exact le_rfl
  · let : NeZero i.1 := ⟨hq⟩
    exact packetFee_nonneg hN i.2
  · exact le_rfl

theorem gauss_cap_improves_same_packet_mother {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    packetFee N a q ≤ lowKernel N q *
      ((7 + 14000 * innerWeight N) + outerWeight N * sharpGaussMass q a (lowHeight N q)) := by
  have hP := sourceP_pos (exp_2000_le_of_exp_3100_le hN)
  unfold packetFee
  apply mul_le_mul_of_nonneg_left _ (by unfold lowKernel; positivity)
  apply add_le_add _ le_rfl
  exact (mul_le_mul_of_nonneg_right cap_ratio_le_one (by unfold innerWeight; positivity)).trans_eq (one_mul _)

theorem large_energy_shared {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    smallEnergy N + largeEnergy N =
      (∑ n ∈ windowFinset N, ArithmeticFunction.vonMangoldt n ^ 2) -
        (∫ alpha in M1 N, ‖S N alpha‖ ^ 2) -
        (∫ alpha in M3 N, ‖S N alpha‖ ^ 2) -
        (∫ alpha in M4 N, ‖S N alpha‖ ^ 2) := by
  have he := minor_energy_eq_source_sub_major (exp_2000_le_of_exp_3100_le hN)
  rw [source_energy_eq] at he
  rw [energy_partition hN]
  linarith

theorem M2_integral_le_4012_of_paid_high {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hz : paidCost N + highCost N ≤
      (0.4012 * (N : ℝ) / sourceL N - fullFee N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2)) :
    ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
      (0.4012 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) := by
  have hh := M2_integral_le_mothers_paid_high hN
  rw [sub_mul] at hz
  linarith only [hh, hz]

end LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual.Remaining
