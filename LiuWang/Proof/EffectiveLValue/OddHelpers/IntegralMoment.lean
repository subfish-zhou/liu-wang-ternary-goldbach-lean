import LiuWang.Proof.EffectiveLValue.OddHelpers.MomentDivisibility
import LiuWang.Proof.EffectiveLValue.OddHelpers.SmallUnits

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.EffectiveLValue

variable {r : ℕ} [NeZero r]

theorem oddMomentOrder_dvd_two (χ : OddRealPrimitiveCharacter r) (hr : 6 < r) :
    addOrderOf (oddMomentResidue χ) ∣ 2 := by
  by_contra h
  have hf := oddCharacter_factors_momentOrder χ h
  have hle : χ.1.conductor ≤ addOrderOf (oddMomentResidue χ) := Nat.sInf_le hf
  rw [χ.2.1] at hle
  have he : addOrderOf (oddMomentResidue χ) = r :=
    le_antisymm (Nat.le_of_dvd (NeZero.pos r) (oddMomentOrder_dvd χ)) hle
  obtain ⟨u, hu, hu'⟩ := exists_unit_not_sign hr
  have hz : (((u : ZMod r).val : ℤ) - oddCharacterInt χ u) • oddMomentResidue χ = 0 := by
    rw [zsmul_eq_mul, Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val,
      sub_mul, sub_eq_zero]
    exact oddMomentResidue_unit_mul χ u
  have hd := addOrderOf_dvd_iff_zsmul_eq_zero.mpr hz
  rw [he] at hd
  have hh := (CharP.intCast_eq_zero_iff (ZMod r) r _).mpr hd
  simp only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val,
    sub_eq_zero] at hh
  rcases oddCharacterInt_unit χ u with hs | hs
  · exact hu (by simpa [hs] using hh)
  · exact hu' (by simpa [hs] using hh)

theorem oddCharacterMoment_dvd (χ : OddRealPrimitiveCharacter r) (hr : 8 < r) :
    (r : ℤ) ∣ oddCharacterMoment χ := by
  have ho := oddMomentOrder_dvd_two χ (by omega)
  rcases (Nat.dvd_prime Nat.prime_two).mp ho with hone | htwo
  · apply (CharP.intCast_eq_zero_iff (ZMod r) r _).mp
    exact AddMonoid.addOrderOf_eq_one_iff.mp hone
  · have hprime : ∀ {p : ℕ}, p.Prime → p ∣ r → p = 2 := by
      intro p hp hpr
      have hm : r / p ∣ r := Nat.div_dvd_of_dvd hpr
      have hmlt : r / p < r := Nat.div_lt_self (NeZero.pos r) hp.one_lt
      obtain ⟨z, hz⟩ := oddCharacterMoment_proper_dvd χ hm hmlt
      have hzero : p • oddMomentResidue χ = 0 := by
        rw [nsmul_eq_mul, oddMomentResidue, hz]
        simp only [Int.cast_mul, Int.cast_natCast]
        calc
          (p : ZMod r) * ((r / p : ℕ) * (z : ZMod r)) =
              ((p * (r / p) : ℕ) : ZMod r) * (z : ZMod r) := by push_cast; ring
          _ = 0 := by rw [Nat.mul_div_cancel' hpr, ZMod.natCast_self, zero_mul]
      have hdp := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hzero
      rw [htwo] at hdp
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hdp).symm
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd (NeZero.ne r) hprime
    have hk : 4 ≤ r.primeFactorsList.length := by
      by_contra hn
      have hlen : r.primeFactorsList.length ≤ 3 := by omega
      have hb := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hlen
      norm_num at hb
      omega
    have h16 : 16 ∣ r := by
      rw [hpow]
      exact pow_dvd_pow 2 hk
    have hf := quadratic_factors_half_of_sixteen_dvd χ.1 χ.2.2.1 h16
    have hc : χ.1.conductor ≤ r / 2 := Nat.sInf_le hf
    rw [χ.2.1] at hc
    have hlt := Nat.div_lt_self (NeZero.pos r) (by decide : 1 < 2)
    omega

end LiuWang.Proof.EffectiveLValue
