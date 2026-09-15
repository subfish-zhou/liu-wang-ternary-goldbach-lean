import LiuWang.Proof.EffectiveLValue.OddHelpers.IntegerSum
import Mathlib.Data.Nat.Factors

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.EffectiveLValue

open Finset

variable {r : ℕ} [NeZero r]

omit [NeZero r] in
theorem oddCharacterInt_unit [NeZero r] (χ : OddRealPrimitiveCharacter r) (u : (ZMod r)ˣ) :
    oddCharacterInt χ u = 1 ∨ oddCharacterInt χ u = -1 := by
  have h := MulChar.isQuadratic_iff_sq_eq_one.mpr χ.2.2.1 u
  rcases h with h | h | h
  · exact False.elim ((u.isUnit.map χ.1).ne_zero h)
  · left
    apply Int.cast_injective (α := ℂ)
    simpa using h
  · right
    apply Int.cast_injective (α := ℂ)
    simpa using h

theorem oddCharacter_kernel_witness (χ : OddRealPrimitiveCharacter r)
    {m : ℕ} (hm : m ∣ r) (hlt : m < r) :
    ∃ u : (ZMod r)ˣ, ZMod.unitsMap hm u = 1 ∧ χ.1 u ≠ 1 := by
  by_contra h
  push Not at h
  have hf : χ.1.FactorsThrough m :=
    (DirichletCharacter.factorsThrough_iff_ker_unitsMap hm).mpr (by
      intro u hu
      change χ.1.toUnitHom u = 1
      apply Units.ext
      exact h u hu)
  have hc : χ.1.conductor ≤ m := Nat.sInf_le hf
  rw [χ.2.1] at hc
  omega

theorem oddCharacterMoment_proper_dvd (χ : OddRealPrimitiveCharacter r)
    {m : ℕ} (hm : m ∣ r) (hlt : m < r) :
    (m : ℤ) ∣ oddCharacterMoment χ := by
  classical
  have : NeZero m := ⟨fun h ↦ NeZero.ne r (Nat.eq_zero_of_zero_dvd (h ▸ hm))⟩
  obtain ⟨u, hu, hχu⟩ := oddCharacter_kernel_witness χ hm hlt
  have huval : ZMod.castHom hm (ZMod m) (u : ZMod r) = 1 := by
    simpa [ZMod.unitsMap_def] using congrArg Units.val hu
  have hsign : oddCharacterInt χ u = -1 := by
    rcases oddCharacterInt_unit χ u with h | h
    · have hh := congrArg (fun z : ℤ ↦ (z : ℂ)) h
      exact False.elim (hχu (by simpa using hh))
    · exact h
  let f : ZMod r → ℤ := fun a ↦
    oddCharacterInt χ a * (ZMod.castHom hm (ZMod m) a).val
  have hf : ∑ a, f a = 0 := by
    have hh := Equiv.sum_comp u.mulLeft f
    have he (a : ZMod r) : f (u.mulLeft a) = -f a := by
      change oddCharacterInt χ ((u : ZMod r) * a) *
        (ZMod.castHom hm (ZMod m) ((u : ZMod r) * a)).val = -f a
      rw [oddCharacterInt_mul, hsign, map_mul, huval, one_mul]
      dsimp [f]
      ring
    simp_rw [he, sum_neg_distrib] at hh
    omega
  have he : oddCharacterMoment χ =
      ∑ a : ZMod r, oddCharacterInt χ a *
        ((a.val : ℤ) - (ZMod.castHom hm (ZMod m) a).val) := by
    simp only [mul_sub, sum_sub_distrib]
    change oddCharacterMoment χ = oddCharacterMoment χ - ∑ a, f a
    rw [hf, sub_zero]
  rw [he]
  apply dvd_sum
  intro a _
  apply dvd_mul_of_dvd_right
  apply (CharP.intCast_eq_zero_iff (ZMod m) m _).mp
  simp only [Int.cast_sub, Int.cast_natCast]
  rw [sub_eq_zero]
  simp

def oddMomentResidue (χ : OddRealPrimitiveCharacter r) : ZMod r :=
  (oddCharacterMoment χ : ZMod r)

theorem oddMomentResidue_sum (χ : OddRealPrimitiveCharacter r) :
    oddMomentResidue χ = ∑ a : ZMod r, (oddCharacterInt χ a : ZMod r) * a := by
  simp [oddMomentResidue, oddCharacterMoment]

theorem oddMomentResidue_unit_mul (χ : OddRealPrimitiveCharacter r) (u : (ZMod r)ˣ) :
    (u : ZMod r) * oddMomentResidue χ =
      (oddCharacterInt χ u : ZMod r) * oddMomentResidue χ := by
  have hh := Equiv.sum_comp u.mulLeft
    (fun a : ZMod r ↦ (oddCharacterInt χ a : ZMod r) * a)
  change (∑ a : ZMod r, (oddCharacterInt χ ((u : ZMod r) * a) : ZMod r) *
    ((u : ZMod r) * a)) = _ at hh
  simp_rw [oddCharacterInt_mul, Int.cast_mul] at hh
  have he : (∑ a : ZMod r, (oddCharacterInt χ u : ZMod r) *
      (oddCharacterInt χ a : ZMod r) * ((u : ZMod r) * a)) =
      (oddCharacterInt χ u : ZMod r) * u * oddMomentResidue χ := by
    rw [oddMomentResidue_sum, mul_sum]
    apply sum_congr rfl
    intro a _
    ring
  rw [he, ← oddMomentResidue_sum] at hh
  rcases oddCharacterInt_unit χ u with h | h <;> rw [h] at hh ⊢ <;>
    norm_num at hh ⊢
  · exact hh
  · linear_combination -hh

theorem oddMomentOrder_dvd (χ : OddRealPrimitiveCharacter r) :
    addOrderOf (oddMomentResidue χ) ∣ r := by
  simpa [ZMod.card] using (addOrderOf_dvd_card (x := oddMomentResidue χ))

theorem oddMomentOrder_smul_zero (χ : OddRealPrimitiveCharacter r)
    {n : ℤ} (h : (n : ZMod (addOrderOf (oddMomentResidue χ))) = 0) :
    (n : ZMod r) * oddMomentResidue χ = 0 := by
  rw [← zsmul_eq_mul]
  exact addOrderOf_dvd_iff_zsmul_eq_zero.mp
    ((CharP.intCast_eq_zero_iff _ _ n).mp h)

theorem oddCharacter_factors_momentOrder (χ : OddRealPrimitiveCharacter r)
    (horder : ¬addOrderOf (oddMomentResidue χ) ∣ 2) :
    χ.1.FactorsThrough (addOrderOf (oddMomentResidue χ)) := by
  apply (DirichletCharacter.factorsThrough_iff_ker_unitsMap (oddMomentOrder_dvd χ)).mpr
  intro u hu
  have hcast : ZMod.castHom (oddMomentOrder_dvd χ)
      (ZMod (addOrderOf (oddMomentResidue χ))) (u : ZMod r) = 1 := by
    simpa [ZMod.unitsMap_def] using congrArg Units.val hu
  have hz : ((((u : ZMod r).val : ℤ) - 1 : ℤ) :
      ZMod (addOrderOf (oddMomentResidue χ))) = 0 := by
    simpa using sub_eq_zero.mpr hcast
  have he := oddMomentOrder_smul_zero χ hz
  simp only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val,
    Int.cast_one, sub_mul, one_mul, sub_eq_zero] at he
  have huχ : oddCharacterInt χ u = 1 := by
    rcases oddCharacterInt_unit χ u with h | h
    · exact h
    · have hh := oddMomentResidue_unit_mul χ u
      rw [h, he] at hh
      have htwo : 2 • oddMomentResidue χ = 0 := by
        simp only [Int.cast_neg, Int.cast_one, neg_one_mul] at hh
        simpa only [two_nsmul] using eq_neg_iff_add_eq_zero.mp hh
      exact False.elim (horder (addOrderOf_dvd_iff_nsmul_eq_zero.mpr htwo))
  change χ.1.toUnitHom u = 1
  apply Units.ext
  have hh := congrArg (fun z : ℤ ↦ (z : ℂ)) huχ
  simpa using hh

end LiuWang.Proof.EffectiveLValue
