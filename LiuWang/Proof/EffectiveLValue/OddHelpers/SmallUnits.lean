import LiuWang.Proof.EffectiveLValue.GaussField

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.EffectiveLValue

theorem odd_modulus_le_three_of_units_sign {n : ℕ} [NeZero n] (hn : Odd n)
    (h : ∀ u : (ZMod n)ˣ, (u : ZMod n) = 1 ∨ (u : ZMod n) = -1) :
    n ≤ 3 := by
  let u := ZMod.unitOfCoprime 2 hn.coprime_two_left
  rcases h u with hu | hu
  · have hz : (1 : ZMod n) = 0 := by
      change (2 : ZMod n) = 1 at hu
      linear_combination hu
    have hd : n ∣ 1 := (ZMod.natCast_eq_zero_iff 1 n).mp (by simpa using hz)
    exact (Nat.le_of_dvd (by decide) hd).trans (by decide)
  · have hz : (3 : ZMod n) = 0 := by
      change (2 : ZMod n) = -1 at hu
      linear_combination hu
    exact Nat.le_of_dvd (by decide) ((ZMod.natCast_eq_zero_iff 3 n).mp hz)

theorem exists_unit_not_sign {r : ℕ} [NeZero r] (hr : 6 < r) :
    ∃ u : (ZMod r)ˣ, (u : ZMod r) ≠ 1 ∧ (u : ZMod r) ≠ -1 := by
  by_contra h
  push Not at h
  have hall (u : (ZMod r)ˣ) : (u : ZMod r) = 1 ∨ (u : ZMod r) = -1 := by
    by_cases hu : (u : ZMod r) = 1
    · exact Or.inl hu
    · exact Or.inr (h u hu)
  rcases Nat.even_or_odd r with he | ho
  · obtain ⟨m, hm⟩ := he
    have hrm : r = 2 * m := by omega
    have hmpos : 0 < m := by omega
    have : NeZero m := ⟨by omega⟩
    rcases Nat.even_or_odd m with he' | ho'
    · obtain ⟨k, hk⟩ := he'
      have hrk : r = 4 * k := by omega
      have hk2 : 2 ≤ k := by omega
      have hz : ((4 * k : ℕ) : ZMod r) = 0 := by
        rw [← hrk]
        exact ZMod.natCast_self r
      let a : ZMod r := 1 + 2 * k
      have hs : a * a = 1 := by
        calc
          a * a = 1 + (4 * (k : ZMod r)) * (k + 1) := by dsimp [a]; ring
          _ = 1 := by simpa using congrArg (fun z : ZMod r ↦ 1 + z * (k + 1)) hz
      let u : (ZMod r)ˣ := ⟨a, a, hs, hs⟩
      rcases hall u with hu | hu
      · have hh : ((2 * k : ℕ) : ZMod r) = 0 := by
          change 1 + 2 * (k : ZMod r) = 1 at hu
          push_cast
          linear_combination hu
        have hd := Nat.le_of_dvd (by omega : 0 < 2 * k)
          ((ZMod.natCast_eq_zero_iff (2 * k) r).mp hh)
        omega
      · have hh : ((2 * k + 2 : ℕ) : ZMod r) = 0 := by
          change 1 + 2 * (k : ZMod r) = -1 at hu
          push_cast
          linear_combination hu
        have hd := Nat.le_of_dvd (by omega : 0 < 2 * k + 2)
          ((ZMod.natCast_eq_zero_iff (2 * k + 2) r).mp hh)
        omega
    · have hd : m ∣ r := ⟨2, by omega⟩
      have hm3 := odd_modulus_le_three_of_units_sign ho' (fun u ↦ by
        obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective hd u
        have hv' : ZMod.castHom hd (ZMod m) (v : ZMod r) = u := by
          simpa [ZMod.unitsMap_def] using congrArg Units.val hv
        rcases hall v with h | h
        · left
          rw [← hv', h, map_one]
        · right
          rw [← hv', h, map_neg, map_one])
      omega
  · have := odd_modulus_le_three_of_units_sign ho hall
    omega

theorem quadratic_factors_half_of_sixteen_dvd {r : ℕ} [NeZero r]
    (χ : Interfaces.Character r) (hχ : χ ^ 2 = 1) (hr : 16 ∣ r) :
    χ.FactorsThrough (r / 2) := by
  obtain ⟨k, hk⟩ := hr
  have hkpos : 0 < k := by
    have := NeZero.pos r
    omega
  have hhalf : r / 2 = 8 * k := by omega
  have hd : 8 * k ∣ r := ⟨2, by omega⟩
  rw [hhalf]
  apply (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd).mpr
  intro u hu
  have hcast : ZMod.castHom hd (ZMod (8 * k)) (u : ZMod r) = 1 := by
    simpa [ZMod.unitsMap_def] using congrArg Units.val hu
  have : NeZero (8 * k) := ⟨by omega⟩
  have : Fact (1 < 8 * k) := ⟨by omega⟩
  have hmod : (u : ZMod r).val % (8 * k) = 1 := by
    rw [← ZMod.natCast_zmod_val (u : ZMod r), map_natCast] at hcast
    have hh := congrArg ZMod.val hcast
    simpa only [ZMod.val_natCast, ZMod.val_one] using hh
  have hvlt := (u : ZMod r).val_lt
  have hv : (u : ZMod r).val = 1 ∨ (u : ZMod r).val = 8 * k + 1 := by
    by_cases hlt : (u : ZMod r).val < 8 * k
    · exact Or.inl (by rwa [Nat.mod_eq_of_lt hlt] at hmod)
    · have he : (u : ZMod r).val = ((u : ZMod r).val - 8 * k) + 8 * k := by omega
      have hs : (u : ZMod r).val - 8 * k < 8 * k := by omega
      conv_lhs at hmod => rw [he]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt hs] at hmod
      right
      omega
  change χ.toUnitHom u = 1
  apply Units.ext
  change χ (u : ZMod r) = 1
  rcases hv with hv | hv
  · have he : (u : ZMod r) = 1 := by
      rw [← ZMod.natCast_zmod_val (u : ZMod r), hv, Nat.cast_one]
    rw [he, map_one]
  · let a : ZMod r := 1 + 4 * k
    have hz : (16 * (k : ZMod r)) = 0 := by
      have hh : ((16 * k : ℕ) : ZMod r) = 0 := by
        rw [← hk]
        exact ZMod.natCast_self r
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hh
    have hs : a ^ 2 = (u : ZMod r) := by
      rw [← ZMod.natCast_zmod_val (u : ZMod r), hv]
      push_cast
      calc
        a ^ 2 = 8 * k + 1 + (16 * (k : ZMod r)) * k := by dsimp [a]; ring
        _ = _ := by rw [hz, zero_mul, add_zero]
    have hnonzero : χ (u : ZMod r) ≠ 0 := (u.isUnit.map χ).ne_zero
    rw [← hs, map_pow] at hnonzero ⊢
    rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ a with h | h | h
    · simp [h] at hnonzero
    · simp [h]
    · simp [h]

end LiuWang.Proof.EffectiveLValue
