import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.SmallConductors

theorem factorsThrough_of_totient_eq {R : Type*} [CommMonoidWithZero R]
    {q d : ℕ} [NeZero q] [NeZero d] (chi : DirichletCharacter R q)
    (hd : d ∣ q) (hphi : q.totient = d.totient) :
    chi.FactorsThrough d := by
  have hinj : Function.Injective (ZMod.unitsMap hd) := by
    apply ((Fintype.bijective_iff_surjective_and_card _).mpr
      ⟨ZMod.unitsMap_surjective hd, ?_⟩).1
    simpa only [ZMod.card_units_eq_totient] using hphi
  apply (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd).mpr
  intro u hu
  have hu1 : u = 1 := hinj (hu.trans (map_one _).symm)
  change chi.toUnitHom u = 1
  rw [hu1, map_one]

theorem factorsThrough_of_twice_odd {R : Type*} [CommMonoidWithZero R]
    {n : ℕ} [NeZero n] (hn : Odd n) (chi : DirichletCharacter R (2 * n)) :
    chi.FactorsThrough n :=
  factorsThrough_of_totient_eq chi (dvd_mul_left n 2) (Nat.totient_two_mul_of_odd hn)

theorem not_primitive_twice_odd {R : Type*} [CommMonoidWithZero R]
    {n : ℕ} [NeZero n] (hn : Odd n) (chi : DirichletCharacter R (2 * n)) :
    ¬chi.IsPrimitive := by
  intro hp
  have hc : chi.conductor ≤ n := Nat.sInf_le (factorsThrough_of_twice_odd hn chi)
  rw [hp] at hc
  have hn0 := NeZero.pos n
  omega

theorem primitive_mod_four_ne_two {R : Type*} [CommMonoidWithZero R]
    {q : ℕ} [NeZero q] (chi : DirichletCharacter R q) (hp : chi.IsPrimitive) :
    q % 4 ≠ 2 := by
  intro hq
  have he : q = 2 * (2 * (q / 4) + 1) := by omega
  generalize hm : 2 * (q / 4) + 1 = m at he
  have hm0 : 0 < m := by omega
  have hmOdd : Odd m := ⟨q / 4, by omega⟩
  let : NeZero m := ⟨by omega⟩
  subst q
  exact not_primitive_twice_odd hmOdd chi hp

theorem conductor_mod_four_ne_two {R : Type*} [CommMonoidWithZero R]
    {q : ℕ} [NeZero q] (chi : DirichletCharacter R q) :
    chi.conductor % 4 ≠ 2 := by
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  exact primitive_mod_four_ne_two chi.primitiveCharacter chi.primitiveCharacter_isPrimitive

#print axioms conductor_mod_four_ne_two

end LiuWang.Proof.Campaign20260915.SmallConductors
