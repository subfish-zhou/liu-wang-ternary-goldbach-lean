import LiuWang.Proof.SourceRoute.Density.ReflectedJensen

/-! Close the analytic counting chain down to actual disk energies, not a density hypothesis. -/

set_option autoImplicit false

noncomputable section

open Complex Set
open LiuWang.Proof.NonprincipalDensityAdvance
open LiuWang.Proof.NonprincipalDensityMeans (nonprincipalRatio)
open LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.PVContinuation

namespace LiuWang.Proof.SourceRoute.Density

def horizontalEnergyCost (q : ℕ) [NeZero q] (X a U R : ℝ) : ℝ :=
  (2 - a) * Real.pi *
    ((∑ chi ∈ nonprincipalCharacters q,
      ((Real.log (2 / (2 - 8 / (X - 1) ^ 2)) + diskEnergy chi X U R) /
          Real.log (R / (2 - a)) +
        (Real.log (2 / (2 - 8 / (X - 1) ^ 2)) + diskEnergy chi X (-U) R) /
          Real.log (R / (2 - a)) + 3)) / q.totient)

theorem horizontalDifference_le_energy (q : ℕ) [NeZero q] {X a U R : ℝ}
    (hX : 5 ≤ X) (ha : a < 2) (hU : 0 ≤ U) (hR : 2 - a < R)
    (hb : ∀ chi ∈ nonprincipalCharacters q,
      ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), H chi X s ≠ 0) :
    horizontalDifference q X a U ≤ horizontalEnergyCost q X a U R := by
  apply (family_horizontal_card_bound q hX ha.le hU hb).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (2 - a) * Real.pi)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro chi hchi
  have hc := (mem_nonprincipalCharacters chi).mp hchi
  exact add_le_add (add_le_add
    (reflected_jensen_energy hc hX (by linarith) hR (h := U))
    (reflected_jensen_energy hc hX (by linarith) hR (h := -U))) le_rfl

theorem closed_count_energy (q : ℕ) [NeZero q] {X alpha T a U d R : ℝ}
    (hX : 5 ≤ X) {M : ℕ} (hNM : ⌈X⌉₊ ≤ M) (hqN : q ≤ ⌈X⌉₊)
    (ha : a ∈ Icc (1 / 2) 1) (hU : 0 ≤ U) (hTU : T ≤ U)
    (hd : 0 ≤ d) (hgap : a + d ≤ alpha) (hR : 2 - a < R)
    (hb : ∀ chi ∈ nonprincipalCharacters q,
      ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), H chi X s ≠ 0) :
    2 * Real.pi * d * ((nonprincipalCount q alpha T : ℝ) / q.totient) ≤
      pvBudget q X M a U + nonprincipalRatio q * (16 * U / (X - 1) ^ 2) +
        horizontalEnergyCost q X a U R :=
  (closed_count_PV q hX hNM hqN ha hU hTU hd hgap hb).trans
    (add_le_add le_rfl (horizontalDifference_le_energy q hX (by linarith [ha.2]) hU hR hb))

theorem produced_closed_count_energy (q : ℕ) [NeZero q] {X alpha T d e : ℝ}
    (hX : 5 ≤ X) {M : ℕ} (hNM : ⌈X⌉₊ ≤ M) (hqN : q ≤ ⌈X⌉₊)
    (halpha : alpha ≤ 1) (hleft : 1 / 2 ≤ alpha - d - e)
    (hT : 0 ≤ T) (hd : 0 < d) (he : 0 < e) :
    ∃ a ∈ Ioo (alpha - d - e) (alpha - d), ∃ U ∈ Ioo T (T + e),
      (∀ chi ∈ nonprincipalCharacters q,
        ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), H chi X s ≠ 0) ∧
      2 * Real.pi * d * ((nonprincipalCount q alpha T : ℝ) / q.totient) ≤
        pvBudget q X M a U + nonprincipalRatio q * (16 * U / (X - 1) ^ 2) +
          horizontalEnergyCost q X a U (2 - a + d / 2) := by
  obtain ⟨a, ha, U, hU, hb⟩ :=
    family_boundary_perturbation q (by linarith : 3 < X) he (a := alpha - d) (T := T)
  refine ⟨a, ha, U, hU, hb, ?_⟩
  exact closed_count_energy q hX hNM hqN ⟨by linarith [ha.1], by linarith [ha.2]⟩
    (by linarith [hU.1]) hU.1.le hd.le (by linarith [ha.2]) (by linarith) hb

theorem produced_closed_count_energy_unnormalized (q : ℕ) [NeZero q] {X alpha T d e : ℝ}
    (hX : 5 ≤ X) {M : ℕ} (hNM : ⌈X⌉₊ ≤ M) (hqN : q ≤ ⌈X⌉₊)
    (halpha : alpha ≤ 1) (hleft : 1 / 2 ≤ alpha - d - e)
    (hT : 0 ≤ T) (hd : 0 < d) (he : 0 < e) :
    ∃ a ∈ Ioo (alpha - d - e) (alpha - d), ∃ U ∈ Ioo T (T + e),
      (∀ chi ∈ nonprincipalCharacters q,
        ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), H chi X s ≠ 0) ∧
      2 * Real.pi * d * (nonprincipalCount q alpha T : ℝ) ≤
        (q.totient : ℝ) *
          (pvBudget q X M a U + nonprincipalRatio q * (16 * U / (X - 1) ^ 2) +
            horizontalEnergyCost q X a U (2 - a + d / 2)) := by
  obtain ⟨a, ha, U, hU, hb, h⟩ :=
    produced_closed_count_energy q hX hNM hqN halpha hleft hT hd he
  refine ⟨a, ha, U, hU, hb, ?_⟩
  have hp : (0 : ℝ) < q.totient :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  rw [← mul_div_assoc] at h
  exact ((div_le_iff₀ hp).mp h).trans_eq (mul_comm _ _)

@[simp] theorem horizontalEnergyCost_one (X a U R : ℝ) :
    horizontalEnergyCost 1 X a U R = 0 := by simp [horizontalEnergyCost]

@[simp] theorem horizontalEnergyCost_two (X a U R : ℝ) :
    horizontalEnergyCost 2 X a U R = 0 := by simp [horizontalEnergyCost]

end LiuWang.Proof.SourceRoute.Density
