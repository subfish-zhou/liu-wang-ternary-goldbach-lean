import LiuWang.Proof.DirichletZeroCount.Applications.LowAlpha
import LiuWang.Proof.DirichletZeroCount.Consumer
import LiuWang.Proof.CompleteExpansion.Values

/-! # Exact transport to the complete-S zero values, with actual multiplicities -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.DirichletZeroCount.Applications

theorem half_values_eq_complete {q : ℕ} [NeZero q] (chi : Character q) (y : ℝ) :
    zeroValues chi (1 / 2) y = CompleteExpansion.zeroValues chi y := by
  by_cases hc : chi = 1
  · subst chi
    simpa only [CompleteExpansion.zeroValues, ↓reduceIte] using half_principal_values_eq q y
  · simpa only [CompleteExpansion.zeroValues, if_neg hc] using half_nonprincipal_values_eq hc y

theorem values_eq_complete_filter {q : ℕ} [NeZero q] (chi : Character q)
    {alpha : ℝ} (halpha : 1 / 2 ≤ alpha) (y : ℝ) :
    zeroValues chi alpha y =
      (CompleteExpansion.zeroValues chi y).filter (fun rho => alpha ≤ rho.re) := by
  ext rho
  constructor
  · intro hrho
    obtain ⟨hz, ⟨h0, h1, hy⟩, ha⟩ := mem_zeroValues.mp hrho
    exact Finset.mem_filter.mpr
      ⟨CompleteExpansion.mem_zeroValues.mpr ⟨hz, h0, h1, hy, halpha.trans ha⟩, ha⟩
  · intro hrho
    obtain ⟨hrho, ha⟩ := Finset.mem_filter.mp hrho
    obtain ⟨hz, h0, h1, hy, _⟩ := CompleteExpansion.mem_zeroValues.mp hrho
    exact mem_zeroValues.mpr ⟨hz, ⟨h0, h1, hy⟩, ha⟩

theorem count_half_eq_complete {q : ℕ} [NeZero q] (chi : Character q) (y : ℝ) :
    count chi (1 / 2) y =
      ∑ rho ∈ CompleteExpansion.zeroValues chi y, analyticOrderNatAt chi.LFunction rho := by
  rw [count, half_values_eq_complete]

theorem familyCount_half_eq_complete (q : ℕ) [NeZero q] (y : ℝ) :
    familyCount q (1 / 2) y =
      ∑ chi : Character q, ∑ rho ∈ CompleteExpansion.zeroValues chi y,
        analyticOrderNatAt chi.LFunction rho := by
  simp only [familyCount, count_half_eq_complete]

theorem familyCount_eq_complete_filter (q : ℕ) [NeZero q] {alpha : ℝ}
    (halpha : 1 / 2 ≤ alpha) (y : ℝ) :
    familyCount q alpha y =
      ∑ chi : Character q,
        ∑ rho ∈ (CompleteExpansion.zeroValues chi y).filter (fun rho => alpha ≤ rho.re),
          analyticOrderNatAt chi.LFunction rho := by
  simp only [familyCount, count, values_eq_complete_filter _ halpha]

theorem complete_family_le_sourceSeven_low (q : ℕ) [NeZero q] {alpha y : ℝ}
    (hy : 10000 ≤ y) (halpha : 1 / 2 ≤ alpha) (halpha' : alpha ≤ 2 / 3) :
    (∑ chi : Character q,
      ∑ rho ∈ (CompleteExpansion.zeroValues chi y).filter (fun rho => alpha ≤ rho.re),
        (analyticOrderNatAt chi.LFunction rho : ℝ)) ≤ sourceSevenBound q alpha y := by
  simpa only [sourceSevenBound, familyCount_eq_complete_filter q halpha, Nat.cast_sum] using
    familyCount_le_sourceSeven_low q hy halpha halpha'

theorem complete_family_le_sourceSeven_original_low (q : ℕ) [NeZero q] {alpha y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (halpha : 1 / 2 ≤ alpha) (halpha' : alpha ≤ 1 / 2 + 2 * sourceDelta y) :
    (∑ chi : Character q,
      ∑ rho ∈ (CompleteExpansion.zeroValues chi y).filter (fun rho => alpha ≤ rho.re),
        (analyticOrderNatAt chi.LFunction rho : ℝ)) ≤ sourceSevenBound q alpha y := by
  have hy' := source_height_ge_ten_thousand hy
  exact complete_family_le_sourceSeven_low q hy' halpha
    (by linarith [sourceDelta_le_twelfth hy'])

theorem zeroValueSum_eq_count_values {q : ℕ} [NeZero q] (chi : Character q)
    (N : ℕ) (y eta : ℝ) :
    CompleteExpansion.zeroValueSum chi N y eta =
      ∑ rho ∈ zeroValues chi (1 / 2) y,
        (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta := by
  rw [CompleteExpansion.zeroValueSum, half_values_eq_complete]

theorem zeroPacket_eq_count_values {q : ℕ} [NeZero q] (N a : ℕ) (eta : ℝ)
    (haq : Nat.Coprime a q) :
    CompleteExpansion.zeroPacket q N a eta =
      (q.totient : ℂ)⁻¹ * ∑ chi : Character q,
        CharacterExpansion.G a chi * ∑ rho ∈ zeroValues chi (1 / 2) (sourceT N),
          (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta := by
  rw [CompleteExpansion.zeroPacket_eq_all_values N a eta haq]
  simp only [zeroValueSum_eq_count_values]

theorem complete_inverse_band_le {q : ℕ} [NeZero q] (chi : Character q)
    {u y a : ℝ} (hu : 0 < u) (hy : 0 ≤ y) (ha : 0 < a) :
    (∑ rho ∈ (CompleteExpansion.zeroValues chi y).filter (fun rho => u ≤ |rho.im|),
      (analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im|) ≤ sharpenedBound chi y a / u := by
  simpa only [bandValues, half_values_eq_complete] using
    band_inverse_sum_le chi (1 / 2) hu hy ha

theorem complete_inverse_sqrt_band_le {q : ℕ} [NeZero q] (chi : Character q)
    {u y a : ℝ} (hu : 0 < u) (hy : 0 ≤ y) (ha : 0 < a) :
    (∑ rho ∈ (CompleteExpansion.zeroValues chi y).filter (fun rho => u ≤ |rho.im|),
      (analyticOrderNatAt chi.LFunction rho : ℝ) / Real.sqrt |rho.im|) ≤
        sharpenedBound chi y a / Real.sqrt u := by
  simpa only [bandValues, half_values_eq_complete] using
    band_inverse_sqrt_sum_le chi (1 / 2) hu hy ha

theorem normalized_complete_inverse_band_le (q : ℕ) [NeZero q]
    {u y a : ℝ} (hu : 0 < u) (hy : 0 ≤ y) (ha : 0 < a) :
    (∑ chi : Character q,
      ∑ rho ∈ (CompleteExpansion.zeroValues chi y).filter (fun rho => u ≤ |rho.im|),
        (analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im|) / q.totient ≤
          (∑ chi : Character q, sharpenedBound chi y a) / (u * q.totient) := by
  simpa only [bandValues, half_values_eq_complete] using
    normalized_family_inverse_sum_le q (1 / 2) hu hy ha

theorem normalized_complete_inverse_sqrt_band_le (q : ℕ) [NeZero q]
    {u y a : ℝ} (hu : 0 < u) (hy : 0 ≤ y) (ha : 0 < a) :
    (∑ chi : Character q,
      ∑ rho ∈ (CompleteExpansion.zeroValues chi y).filter (fun rho => u ≤ |rho.im|),
        (analyticOrderNatAt chi.LFunction rho : ℝ) / Real.sqrt |rho.im|) / q.totient ≤
          (∑ chi : Character q, sharpenedBound chi y a) / (Real.sqrt u * q.totient) := by
  simpa only [bandValues, half_values_eq_complete] using
    normalized_family_inverse_sqrt_sum_le q (1 / 2) hu hy ha

end LiuWang.Proof.DirichletZeroCount.Applications
