import LiuWang.Proof.EffectiveLValue.Main

set_option autoImplicit false

noncomputable section

open LiuWang.Proof.EffectiveLValue
open NumberField NumberField.InfinitePlace NumberField.Units Filter Topology

namespace LiuWang.Proof.EffectiveLValue.Consumer

variable {r : ℕ} [NeZero r]

example (χ : Interfaces.Character r) :
    χ ^ 2 = 1 ↔ ∀ a : ZMod r, (χ a).im = 0 :=
  character_sq_eq_one_iff_real χ

example (χ : Interfaces.Character r) (hq : χ ^ 2 = 1) :
    star (characterGaussSum χ) = χ (-1) * characterGaussSum χ :=
  characterGaussSum_conj χ hq

variable (χ : OddRealPrimitiveCharacter r) [Fact (1 < r)]

example : characterGaussSum χ.1 ^ 2 = -(r : ℂ) :=
  odd_characterGaussSum_sq χ Fact.out

example : characterGaussSum χ.1 ∉ (algebraMap ℚ ℂ).range :=
  odd_characterGaussSum_not_rat χ Fact.out

example : IsIntegral ℚ (characterGaussSum χ.1) :=
  odd_characterGaussSum_integral χ Fact.out

example : oddCharacterGenerator χ ^ 2 = -(r : oddCharacterField χ) :=
  oddCharacterGenerator_sq χ Fact.out

example : Module.finrank ℚ (oddCharacterField χ) = 2 :=
  oddCharacterField_finrank χ Fact.out

example : NumberField (oddCharacterField χ) :=
  oddCharacterField_numberField χ

example : Algebra.IsQuadraticExtension ℚ (oddCharacterField χ) :=
  oddCharacterField_quadratic χ

example : 1 ≤ classNumber (oddCharacterField χ) :=
  oddCharacterField_classNumber_ge_one χ

example (f : oddCharacterField χ →+* ℝ) : False :=
  oddCharacterField_no_real_embedding χ f

example : IsTotallyComplex (oddCharacterField χ) :=
  oddCharacterField_totallyComplex χ

example : nrRealPlaces (oddCharacterField χ) = 0 :=
  oddCharacterField_nrRealPlaces χ

example : nrComplexPlaces (oddCharacterField χ) = 1 :=
  oddCharacterField_nrComplexPlaces χ

example : Units.rank (oddCharacterField χ) = 0 :=
  oddCharacterField_unitRank χ

example : regulator (oddCharacterField χ) = 1 :=
  oddCharacterField_regulator χ

example :
    dedekindZeta_residue (oddCharacterField χ) =
      (2 * Real.pi * classNumber (oddCharacterField χ)) /
        (torsionOrder (oddCharacterField χ) * Real.sqrt |discr (oddCharacterField χ)|) :=
  oddCharacterField_residue χ

example :
    (2 * Real.pi) /
        (torsionOrder (oddCharacterField χ) * Real.sqrt |discr (oddCharacterField χ)|) ≤
      dedekindZeta_residue (oddCharacterField χ) :=
  oddCharacterField_residue_lower χ

example :
    Tendsto (fun s : ℝ ↦ (s - 1) * dedekindZeta (oddCharacterField χ) s)
      (𝓝[>] 1)
      (𝓝 (((2 * Real.pi * classNumber (oddCharacterField χ)) /
        (torsionOrder (oddCharacterField χ) *
          Real.sqrt |discr (oddCharacterField χ)|) : ℝ) : ℂ)) :=
  oddCharacterField_classNumber_formula χ

example :
    Tendsto (fun s : ℝ ↦ ((s : ℂ) - 1) * riemannZeta s * χ.1.LFunction s)
      (𝓝[>] 1) (𝓝 (χ.1.LFunction 1)) :=
  oddCharacter_LFunction_residue χ

omit [Fact (1 < r)] in
example (hr : 987 ≤ r) (ψ : Interfaces.Character r) (hprim : ψ.IsPrimitive)
    (hreal : ∀ a : ZMod r, (ψ a).im = 0) (hodd : ψ.Odd) :
    ∃ K : IntermediateField ℚ ℂ, Module.finrank ℚ K = 2 ∧
      ∀ _ : K →+* ℝ, False := by
  let η : OddRealPrimitiveCharacter r :=
    ⟨ψ, hprim, (character_sq_eq_one_iff_real ψ).mpr hreal, hodd⟩
  have : Fact (1 < r) := ⟨by omega⟩
  exact ⟨oddCharacterField η, oddCharacterField_finrank η Fact.out,
    oddCharacterField_no_real_embedding η⟩

example {d : ℝ} (hd : 0 ≤ d) {v u : ℤ}
    (hv : 0 < v) (hu : 0 < u) (hp : (v : ℝ) ^ 2 - d * (u : ℝ) ^ 2 = 4) :
    sourceUnitLower d ≤ ((v : ℝ) + (u : ℝ) * Real.sqrt d) / 2 :=
  sourceUnitLower_le_pellUnit hd hv hu hp

example {d : ℝ} (hd : 987 ≤ d) : Real.pi < Real.log (sourceUnitLower d) :=
  pi_lt_log_sourceUnitLower hd

example {d : ℝ} (hd : 987 ≤ d) {v u : ℤ}
    (hv : 0 < v) (hu : 0 < u) (hp : (v : ℝ) ^ 2 - d * (u : ℝ) ^ 2 = 4) :
    Real.pi < Real.log (((v : ℝ) + (u : ℝ) * Real.sqrt d) / 2) :=
  pi_lt_log_pellUnit hd hv hu hp

example {d : ℝ} (hd : 987 ≤ d) :
    min (Real.pi / Real.sqrt d) (Real.log (sourceUnitLower d) / Real.sqrt d) =
      Real.pi / Real.sqrt d :=
  source_minimum_eq_pi_div_sqrt hd

example : Real.pi < Real.log (sourceUnitLower 987) :=
  pi_lt_log_sourceUnitLower (by norm_num)

example (hr : 987 ≤ r) {v u : ℤ} (hv : 0 < v) (hu : 0 < u)
    (hp : v ^ 2 - (r : ℤ) * u ^ 2 = 4) :
    Real.pi < Real.log (((v : ℝ) + (u : ℝ) * Real.sqrt r) / 2) := by
  apply pi_lt_log_pellUnit (by exact_mod_cast hr) hv hu
  exact_mod_cast hp

end LiuWang.Proof.EffectiveLValue.Consumer
