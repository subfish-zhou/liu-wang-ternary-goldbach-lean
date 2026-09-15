import LiuWang.Proof.EffectiveLValue.OddHelpers.SmallUnits

/-!
# Square factors of a primitive quadratic conductor

An odd prime square in the level makes the kernel of reduction consist of
squares. A quadratic character therefore descends, contradicting primitivity.
The argument includes composite levels and uses no parity assumption.
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.EffectiveLValue

theorem quadratic_factors_div_of_odd_prime_sq_dvd {r p : ℕ} [NeZero r]
    (χ : Interfaces.Character r) (hχ : χ ^ 2 = 1)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpr : p ^ 2 ∣ r) :
    χ.FactorsThrough (r / p) := by
  obtain ⟨k, hk⟩ := hpr
  have hkpos : 0 < k := by
    by_contra h
    have : k = 0 := by omega
    simp [this] at hk
    exact NeZero.ne r hk
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨t, ht⟩ := hpodd
  have hhalf : r / p = p * k := by
    rw [hk, pow_two, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
  have hd : p * k ∣ r := ⟨p, by rw [hk]; ring⟩
  rw [hhalf]
  apply (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd).mpr
  intro u hu
  have hcast : ZMod.castHom hd (ZMod (p * k)) (u : ZMod r) = 1 := by
    simpa [ZMod.unitsMap_def] using congrArg Units.val hu
  have hmpos : 1 < p * k := by nlinarith [hp.two_le]
  have : NeZero (p * k) := ⟨by omega⟩
  have : Fact (1 < p * k) := ⟨hmpos⟩
  have hmod : (u : ZMod r).val % (p * k) = 1 := by
    rw [← ZMod.natCast_zmod_val (u : ZMod r), map_natCast] at hcast
    simpa only [ZMod.val_natCast, ZMod.val_one] using congrArg ZMod.val hcast
  let j := (u : ZMod r).val / (p * k)
  have hv : (u : ZMod r).val = 1 + p * k * j := by
    have h := Nat.mod_add_div (u : ZMod r).val (p * k)
    rw [hmod] at h
    exact h.symm
  have hz : (p : ZMod r) ^ 2 * k = 0 := by
    have h : ((p ^ 2 * k : ℕ) : ZMod r) = 0 := by
      rw [← hk]
      exact ZMod.natCast_self r
    simpa only [Nat.cast_mul, Nat.cast_pow] using h
  let a : ZMod r := 1 + (t + 1) * p * k * j
  have ht' : (2 : ZMod r) * (t + 1) = p + 1 := by
    have h : 2 * (t + 1) = p + 1 := by omega
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using
      congrArg (fun n : ℕ ↦ (n : ZMod r)) h
  have hs : a ^ 2 = (u : ZMod r) := by
    rw [← ZMod.natCast_zmod_val (u : ZMod r), hv]
    push_cast
    calc
      a ^ 2 = 1 + 2 * ((t : ZMod r) + 1) * p * k * j +
          ((p : ZMod r) ^ 2 * k) * (((t : ZMod r) + 1) ^ 2 * k * j ^ 2) := by
        dsimp [a]; ring
      _ = 1 + (p : ZMod r) * k * j + ((p : ZMod r) ^ 2 * k) *
          (j + ((t : ZMod r) + 1) ^ 2 * k * j ^ 2) := by rw [ht']; ring
      _ = _ := by rw [hz]; ring
  change χ.toUnitHom u = 1
  apply Units.ext
  change χ (u : ZMod r) = 1
  have hnonzero : χ (u : ZMod r) ≠ 0 := (u.isUnit.map χ).ne_zero
  rw [← hs, map_pow] at hnonzero ⊢
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ a with h | h | h
  · simp [h] at hnonzero
  · simp [h]
  · simp [h]

theorem primitive_quadratic_not_odd_prime_sq_dvd {r p : ℕ} [NeZero r]
    (χ : Interfaces.Character r) (hprimitive : χ.IsPrimitive) (hχ : χ ^ 2 = 1)
    (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ^ 2 ∣ r := by
  intro hpr
  have hf := quadratic_factors_div_of_odd_prime_sq_dvd χ hχ hp hp2 hpr
  have hc : χ.conductor ≤ r / p := Nat.sInf_le hf
  rw [hprimitive] at hc
  have hlt := Nat.div_lt_self (NeZero.pos r) hp.one_lt
  omega

theorem primitive_quadratic_not_sixteen_dvd {r : ℕ} [NeZero r]
    (χ : Interfaces.Character r) (hprimitive : χ.IsPrimitive) (hχ : χ ^ 2 = 1) :
    ¬ 16 ∣ r := by
  intro hr
  have hf := quadratic_factors_half_of_sixteen_dvd χ hχ hr
  have hc : χ.conductor ≤ r / 2 := Nat.sInf_le hf
  rw [hprimitive] at hc
  have hlt := Nat.div_lt_self (NeZero.pos r) (by decide : 1 < 2)
  omega

end LiuWang.Proof.EffectiveLValue
