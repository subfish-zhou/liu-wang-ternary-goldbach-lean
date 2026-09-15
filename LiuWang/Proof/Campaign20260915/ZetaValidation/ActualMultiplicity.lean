import LiuWang.Proof.DirichletZeroCount.Principal
import LiuWang.Proof.Campaign20260915.ZetaValidation.Zeta16Endpoint

set_option autoImplicit false
noncomputable section

open Complex
open scoped ComplexConjugate
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def zetaClosedValues (y : ℝ) : Finset ℂ := zeroValues (1 : Character 1) 0 y

def zetaClosedCount (y : ℝ) : ℕ :=
  ∑ z ∈ zetaClosedValues y, analyticOrderNatAt riemannZeta z

theorem mem_zetaClosedValues {y : ℝ} {z : ℂ} :
    z ∈ zetaClosedValues y ↔
      riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ y := by
  simp only [zetaClosedValues, mem_zeroValues, DirichletCharacter.LFunction_modOne_eq]
  constructor
  · exact fun h => ⟨h.1, h.2.1⟩
  · exact fun h => ⟨h.1, h.2, h.2.1.le⟩

theorem zetaClosedCount_eq_principal (y : ℝ) :
    zetaClosedCount y = count (1 : Character 1) 0 y := by
  simp only [zetaClosedCount, count, zetaClosedValues, DirichletCharacter.LFunction_modOne_eq]

theorem zeta_order_positive_of_mem {y : ℝ} {z : ℂ} (hz : z ∈ zetaClosedValues y) :
    0 < analyticOrderNatAt riemannZeta z := by
  have hp : z ∈ principalValues 1 0 y := by
    simpa only [zetaClosedValues, zeroValues, ↓reduceIte] using hz
  obtain ⟨p, hp, he⟩ := Finset.mem_image.mp hp
  have hf := principal_fiber_card (q := 1) (alpha := 0) (y := y)
    (Finset.mem_image.mpr ⟨p, hp, he⟩)
  rw [DirichletCharacter.LFunction_modOne_eq] at hf
  rw [← hf]
  exact Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, he⟩⟩

theorem zetaClosedValues_card_le_count (y : ℝ) :
    (zetaClosedValues y).card ≤ zetaClosedCount y := by
  calc
    _ = ∑ _z ∈ zetaClosedValues y, (1 : ℕ) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun z hz => zeta_order_positive_of_mem hz)

theorem zetaClosedCount_one : zetaClosedCount 1 = 0 := by
  rw [zetaClosedCount_eq_principal]
  exact count_principal_low 1 0 (by norm_num) le_rfl

theorem zeta_ne_zero_closed_height_one {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1)
    (ht : |z.im| ≤ 1) : riemannZeta z ≠ 0 := by
  intro hz
  have hm := mem_zetaClosedValues.mpr ⟨hz, h0, h1, ht⟩
  have hp := (Finset.card_pos.mpr ⟨z, hm⟩).trans_le (zetaClosedValues_card_le_count 1)
  rw [zetaClosedCount_one] at hp
  omega

theorem zetaClosedCount_sixteen_lower : 2 ≤ zetaClosedCount 16 := by
  classical
  obtain ⟨t, ht, hz⟩ := exists_nontrivial_zero_below_sixteen
  have ht0 : 0 < t := by linarith [ht.1]
  have hp : criticalPoint t ∈ zetaClosedValues 16 :=
    mem_zetaClosedValues.mpr ⟨hz, by norm_num [criticalPoint],
      by norm_num [criticalPoint], by simpa [criticalPoint, abs_of_pos ht0] using ht.2.le⟩
  have hc : conj (criticalPoint t) ∈ zetaClosedValues 16 := by
    apply mem_zetaClosedValues.mpr
    refine ⟨?_, by norm_num [criticalPoint], by norm_num [criticalPoint], ?_⟩
    · rw [riemannZeta_conj, hz, map_zero]
    · simpa [criticalPoint, abs_of_pos ht0] using ht.2.le
  have hne : criticalPoint t ≠ conj (criticalPoint t) := by
    intro he
    have hi := congrArg Complex.im he
    simp only [criticalPoint, conj_im] at hi
    linarith
  have hsub : {criticalPoint t, conj (criticalPoint t)} ⊆ zetaClosedValues 16 := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  have h := (Finset.card_le_card hsub).trans (zetaClosedValues_card_le_count 16)
  simpa only [Finset.card_pair hne] using h

theorem zetaClosedCount_sixteen_coarse_upper : zetaClosedCount 16 ≤ 170 := by
  have h := count_principal_quadratic 1 0 (y := 16) (by norm_num)
  rw [← zetaClosedCount_eq_principal] at h
  have hlt : (zetaClosedCount 16 : ℝ) < 171 := by norm_num at h; linarith
  have hn : zetaClosedCount 16 < 171 := by exact_mod_cast hlt
  omega

#print axioms zetaClosedCount_one
#print axioms zeta_ne_zero_closed_height_one
#print axioms zetaClosedCount_sixteen_lower
#print axioms zetaClosedCount_sixteen_coarse_upper

end LiuWang.Proof.Campaign20260915.ZetaValidation
