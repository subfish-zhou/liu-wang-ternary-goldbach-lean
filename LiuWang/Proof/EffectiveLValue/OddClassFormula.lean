import LiuWang.Proof.EffectiveLValue.GaussField
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
# The actual class-number residue formula for the odd Gauss field

This pays the signature, regulator, and positive class number using the
constructed field. It is a Dedekind-zeta formula, not yet a Dirichlet-L formula:
the discriminant and torsion order have deliberately not been replaced by
the conductor and `2`.
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.EffectiveLValue

open NumberField NumberField.InfinitePlace NumberField.Units
open Filter Topology

variable {r : ℕ} [NeZero r] (χ : OddRealPrimitiveCharacter r) [Fact (1 < r)]

theorem oddCharacterField_no_real_embedding (f : oddCharacterField χ →+* ℝ) : False := by
  have hs := congrArg f (oddCharacterGenerator_sq χ Fact.out)
  simp only [map_pow, map_neg, map_natCast] at hs
  have hr : (0 : ℝ) < r := by exact_mod_cast (NeZero.pos r)
  nlinarith [sq_nonneg (f (oddCharacterGenerator χ))]

instance oddCharacterField_totallyComplex : IsTotallyComplex (oddCharacterField χ) where
  isComplex w := by
    apply not_isReal_iff_isComplex.mp
    rintro ⟨φ, hφ, _⟩
    exact oddCharacterField_no_real_embedding χ hφ.embedding

theorem oddCharacterField_nrRealPlaces :
    nrRealPlaces (oddCharacterField χ) = 0 :=
  IsTotallyComplex.nrRealPlaces_eq_zero _

theorem oddCharacterField_nrComplexPlaces :
    nrComplexPlaces (oddCharacterField χ) = 1 := by
  have h := IsTotallyComplex.finrank (oddCharacterField χ)
  rw [oddCharacterField_finrank χ Fact.out] at h
  omega

theorem oddCharacterField_unitRank :
    Units.rank (oddCharacterField χ) = 0 := by
  rw [Units.rank, card_eq_nrRealPlaces_add_nrComplexPlaces,
    oddCharacterField_nrRealPlaces, oddCharacterField_nrComplexPlaces]

theorem oddCharacterField_regulator :
    regulator (oddCharacterField χ) = 1 := by
  classical
  have hempty : IsEmpty (Fin (Units.rank (oddCharacterField χ))) := by
    rw [oddCharacterField_unitRank]
    infer_instance
  have : IsEmpty {w : InfinitePlace (oddCharacterField χ) //
      w ≠ Units.dirichletUnitTheorem.w₀} :=
    (equivFinRank (oddCharacterField χ)).symm.isEmpty
  rw [regulator_eq_det', Matrix.det_isEmpty, abs_one]

theorem oddCharacterField_residue :
    dedekindZeta_residue (oddCharacterField χ) =
      (2 * Real.pi * classNumber (oddCharacterField χ)) /
        (torsionOrder (oddCharacterField χ) * Real.sqrt |discr (oddCharacterField χ)|) := by
  simp [dedekindZeta_residue,
    oddCharacterField_nrComplexPlaces, oddCharacterField_regulator]

theorem oddCharacterField_residue_lower :
    (2 * Real.pi) /
        (torsionOrder (oddCharacterField χ) * Real.sqrt |discr (oddCharacterField χ)|) ≤
      dedekindZeta_residue (oddCharacterField χ) := by
  rw [oddCharacterField_residue]
  apply div_le_div_of_nonneg_right
  · have hh : (1 : ℝ) ≤ classNumber (oddCharacterField χ) := by
      exact_mod_cast oddCharacterField_classNumber_ge_one χ
    nlinarith [Real.pi_pos]
  · positivity

theorem oddCharacterField_classNumber_formula :
    Tendsto (fun s : ℝ ↦ (s - 1) * dedekindZeta (oddCharacterField χ) s)
      (𝓝[>] 1)
      (𝓝 (((2 * Real.pi * classNumber (oddCharacterField χ)) /
        (torsionOrder (oddCharacterField χ) *
          Real.sqrt |discr (oddCharacterField χ)|) : ℝ) : ℂ)) := by
  rw [← oddCharacterField_residue]
  exact tendsto_sub_one_mul_dedekindZeta_nhdsGT _

omit [Fact (1 < r)] in
theorem oddCharacter_LFunction_residue :
    Tendsto (fun s : ℝ ↦ ((s : ℂ) - 1) * riemannZeta s * χ.1.LFunction s)
      (𝓝[>] 1) (𝓝 (χ.1.LFunction 1)) := by
  have hne : χ.1 ≠ 1 := by
    intro h
    have ho := χ.2.2.2
    rw [DirichletCharacter.Odd, h] at ho
    have he : (1 : Interfaces.Character r) (-1) = 1 :=
      MulChar.one_apply_coe (-1 : (ZMod r)ˣ)
    rw [he] at ho
    norm_num at ho
  have hcoe : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hpunctured :
      Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hcoe, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hsne : (s : ℂ) ≠ 1 := by exact_mod_cast ne_of_gt hs
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hsne
  simpa only [Function.comp_apply, one_mul] using
    (riemannZeta_residue_one.comp hpunctured).mul
      ((χ.1.differentiableAt_LFunction 1 (.inr hne)).continuousAt.tendsto.comp hcoe)

end LiuWang.Proof.EffectiveLValue
