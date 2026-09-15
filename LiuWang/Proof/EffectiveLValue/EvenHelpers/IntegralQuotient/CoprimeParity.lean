import LiuWang.Proof.EffectiveLValue.EvenHelpers.IntegralQuotient.Conductor
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# Local factors of a primitive quadratic character

The Chinese remainder decomposition preserves primitivity of both factors.
This supplies the parity information needed at the prime two.
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.EffectiveLValue

def coprimeUnitsEquiv {a b : ℕ} (h : a.Coprime b) :
    (ZMod (a * b))ˣ ≃* (ZMod a)ˣ × (ZMod b)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits

theorem coprimeUnitsEquiv_fst {a b : ℕ} (h : a.Coprime b) (u : (ZMod (a * b))ˣ) :
    (coprimeUnitsEquiv h u).1 = ZMod.unitsMap (dvd_mul_right a b) u := by
  apply Units.ext
  change ((ZMod.chineseRemainder h) (u : ZMod (a * b))).1 =
    ZMod.castHom (dvd_mul_right a b) (ZMod a) (u : ZMod (a * b))
  exact congrArg (fun f : ZMod (a * b) →+* ZMod a ↦ f (u : ZMod (a * b)))
    (Subsingleton.elim
      ((RingHom.fst (ZMod a) (ZMod b)).comp (ZMod.chineseRemainder h).toRingHom)
      (ZMod.castHom (dvd_mul_right a b) (ZMod a)))

theorem coprimeUnitsEquiv_snd {a b : ℕ} (h : a.Coprime b) (u : (ZMod (a * b))ˣ) :
    (coprimeUnitsEquiv h u).2 = ZMod.unitsMap (dvd_mul_left b a) u := by
  apply Units.ext
  change ((ZMod.chineseRemainder h) (u : ZMod (a * b))).2 =
    ZMod.castHom (dvd_mul_left b a) (ZMod b) (u : ZMod (a * b))
  exact congrArg (fun f : ZMod (a * b) →+* ZMod b ↦ f (u : ZMod (a * b)))
    (Subsingleton.elim
      ((RingHom.snd (ZMod a) (ZMod b)).comp (ZMod.chineseRemainder h).toRingHom)
      (ZMod.castHom (dvd_mul_left b a) (ZMod b)))

theorem primitive_quadratic_coprime_factors {a b : ℕ} [NeZero a] [NeZero b]
    (h : a.Coprime b) (χ : Interfaces.Character (a * b))
    (hprimitive : χ.IsPrimitive) (hχ : χ ^ 2 = 1) :
    ∃ (χa : Interfaces.Character a) (χb : Interfaces.Character b),
      χa.IsPrimitive ∧ χb.IsPrimitive ∧ χa ^ 2 = 1 ∧ χb ^ 2 = 1 ∧
      χ (-1) = χa (-1) * χb (-1) := by
  let e := coprimeUnitsEquiv h
  let f := χ.toUnitHom.comp e.symm.toMonoidHom
  let χa : Interfaces.Character a := MulChar.ofUnitHom
    (f.comp (MonoidHom.inl (ZMod a)ˣ (ZMod b)ˣ))
  let χb : Interfaces.Character b := MulChar.ofUnitHom
    (f.comp (MonoidHom.inr (ZMod a)ˣ (ZMod b)ˣ))
  have ha (u : (ZMod a)ˣ) : χa u = χ (e.symm (u, 1)) := by
    simp [χa, f]
  have hb (u : (ZMod b)ˣ) : χb u = χ (e.symm (1, u)) := by
    simp [χb, f]
  have hval (u : (ZMod (a * b))ˣ) :
      χ u = χa (e u).1 * χb (e u).2 := by
    rw [ha, hb, ← map_mul, ← Units.val_mul, ← map_mul]
    simp
  have hprod : χ =
      DirichletCharacter.changeLevel (dvd_mul_right a b) χa *
      DirichletCharacter.changeLevel (dvd_mul_left b a) χb := by
    apply MulChar.ext
    intro u
    rw [MulChar.mul_apply, DirichletCharacter.changeLevel_eq_cast_of_dvd,
      DirichletCharacter.changeLevel_eq_cast_of_dvd, hval]
    congr 1
    · exact congrArg χa (congrArg Units.val (coprimeUnitsEquiv_fst h u))
    · exact congrArg χb (congrArg Units.val (coprimeUnitsEquiv_snd h u))
  have hc : a * b ∣ χa.conductor.lcm χb.conductor := by
    have hd := DirichletCharacter.conductor_mul_dvd_lcm_conductor
      (DirichletCharacter.changeLevel (dvd_mul_right a b) χa)
      (DirichletCharacter.changeLevel (dvd_mul_left b a) χb)
    rw [← hprod, hprimitive, DirichletCharacter.conductor_changeLevel,
      DirichletCharacter.conductor_changeLevel] at hd
    exact hd
  have hpa : χa.IsPrimitive := by
    apply le_antisymm (Nat.le_of_dvd (NeZero.pos a) χa.conductor_dvd_level)
    have hd : a * b ∣ χa.conductor * b := hc.trans
      (Nat.lcm_dvd (dvd_mul_right _ _)
        (dvd_mul_of_dvd_right χb.conductor_dvd_level _))
    have hpos : 0 < χa.conductor * b :=
      Nat.mul_pos (Nat.pos_of_ne_zero χa.conductor_ne_zero) (NeZero.pos b)
    exact (Nat.mul_le_mul_right_iff (NeZero.pos b)).mp (Nat.le_of_dvd hpos hd)
  have hpb : χb.IsPrimitive := by
    apply le_antisymm (Nat.le_of_dvd (NeZero.pos b) χb.conductor_dvd_level)
    have hd : a * b ∣ a * χb.conductor := hc.trans
      (Nat.lcm_dvd (dvd_mul_of_dvd_left χa.conductor_dvd_level _)
        (dvd_mul_left _ _))
    have hpos : 0 < a * χb.conductor :=
      Nat.mul_pos (NeZero.pos a) (Nat.pos_of_ne_zero χb.conductor_ne_zero)
    exact (Nat.mul_le_mul_left_iff (NeZero.pos a)).mp (Nat.le_of_dvd hpos hd)
  refine ⟨χa, χb, hpa, hpb, ?_, ?_, ?_⟩
  · apply MulChar.ext
    intro u
    rw [MulChar.pow_apply_coe, ha, ← MulChar.pow_apply_coe, hχ,
      MulChar.one_apply_coe, MulChar.one_apply_coe]
  · apply MulChar.ext
    intro u
    rw [MulChar.pow_apply_coe, hb, ← MulChar.pow_apply_coe, hχ,
      MulChar.one_apply_coe, MulChar.one_apply_coe]
  · have hm := hval (-1)
    rw [coprimeUnitsEquiv_fst, coprimeUnitsEquiv_snd] at hm
    simpa [ZMod.unitsMap_def] using hm

theorem quadratic_cyclic_eq {n : ℕ} [IsCyclic (ZMod n)ˣ]
    (χ ψ : Interfaces.Character n) (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1)
    (hχne : χ ≠ 1) (hψne : ψ ≠ 1) : χ = ψ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := (ZMod n)ˣ)
  have hgen (φ : Interfaces.Character n) (hφ : φ ^ 2 = 1) (hne : φ ≠ 1) :
      φ g = -1 := by
    rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hφ g with hz | ho | hn
    · exact False.elim ((g.isUnit.map φ).ne_zero hz)
    · exfalso
      apply hne
      apply MulChar.ext
      intro u
      obtain ⟨k, hk⟩ := hg u
      rw [MulChar.one_apply_coe, ← hk, Units.val_pow_eq_pow_val, map_pow, ho, one_pow]
    · exact hn
  apply MulChar.ext
  intro u
  obtain ⟨k, hk⟩ := hg u
  rw [← hk, Units.val_pow_eq_pow_val, map_pow, map_pow, hgen χ hχ hχne,
    hgen ψ hψ hψne]

theorem primitive_quadratic_prime_neg_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (χ : Interfaces.Character p) (hprimitive : χ.IsPrimitive) (hχ : χ ^ 2 = 1) :
    χ (-1) = (ZMod.χ₄ p : ℂ) := by
  have : Fact p.Prime := ⟨hp⟩
  have hchar : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  let ψ : Interfaces.Character p := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)
  have hψ : ψ ^ 2 = 1 :=
    ((quadraticChar_isQuadratic (ZMod p)).comp (Int.castRingHom ℂ)).sq_eq_one
  have hψne : ψ ≠ 1 := (MulChar.ringHomComp_ne_one_iff (Int.cast_injective)).mpr
    (quadraticChar_ne_one hchar)
  have hχne : χ ≠ 1 := by
    intro heq
    rw [DirichletCharacter.IsPrimitive, heq, DirichletCharacter.conductor_one] at hprimitive
    exact hp.ne_one hprimitive.symm
  have heq := quadratic_cyclic_eq χ ψ hχ hψ hχne hψne
  rw [heq]
  change ((quadraticChar (ZMod p) (-1) : ℤ) : ℂ) = _
  rw [quadraticChar_neg_one hchar, ZMod.card]

theorem primitive_quadratic_odd_level_neg_one :
    ∀ (r : ℕ) [NeZero r] (χ : Interfaces.Character r),
      χ.IsPrimitive → χ ^ 2 = 1 → Odd r → χ (-1) = (ZMod.χ₄ r : ℂ) := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro inst χ hprimitive hχ hodd
    by_cases hr1 : r = 1
    · subst r
      have he : (-1 : ZMod 1) = 1 := Subsingleton.elim _ _
      simp [he]
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hr1
    obtain ⟨m, hm⟩ := hpd
    have hp2 : p ≠ 2 := by
      intro he
      exact hodd.not_two_dvd_nat (he ▸ ⟨m, hm⟩)
    have hcop : p.Coprime m := hp.coprime_iff_not_dvd.mpr (by
      intro hpm
      apply primitive_quadratic_not_odd_prime_sq_dvd χ hprimitive hχ hp hp2
      obtain ⟨k, hk⟩ := hpm
      exact ⟨k, by rw [hm, hk]; ring⟩)
    have hmpos : 0 < m := by
      have := NeZero.pos r
      nlinarith [hp.pos]
    have : NeZero p := ⟨hp.ne_zero⟩
    have : NeZero m := ⟨by omega⟩
    have hmlt : m < r := by nlinarith [hp.two_le]
    subst r
    obtain ⟨χp, χm, hpp, hmp, hpχ, hmχ, he⟩ :=
      primitive_quadratic_coprime_factors hcop χ hprimitive hχ
    rw [he, primitive_quadratic_prime_neg_one hp hp2 χp hpp hpχ,
      ih m hmlt χm hmp hmχ (Nat.Odd.of_mul_right hodd)]
    simp [Nat.cast_mul, map_mul]

theorem primitive_four_odd (χ : Interfaces.Character 4) (hprimitive : χ.IsPrimitive) :
    χ.Odd := by
  rcases χ.even_or_odd with heven | hodd
  · exfalso
    have hχ : χ = 1 := by
      apply MulChar.ext
      intro u
      have hall : ∀ u : (ZMod 4)ˣ, (u : ZMod 4) = 1 ∨ (u : ZMod 4) = -1 := by decide
      rw [MulChar.one_apply_coe]
      rcases hall u with hu | hu
      · rw [hu, map_one]
      · rw [hu]
        exact heven
    rw [DirichletCharacter.IsPrimitive, hχ, DirichletCharacter.conductor_one] at hprimitive
    norm_num at hprimitive
  · exact hodd

theorem primitive_even_quadratic_not_four_mul_one_mod_four {m : ℕ} [NeZero m]
    (χ : Interfaces.Character (4 * m)) (hprimitive : χ.IsPrimitive)
    (hχ : χ ^ 2 = 1) (heven : χ.Even) (hm : m % 4 = 1) : False := by
  have hodd : Odd m := Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_one hm)
  have hcop : Nat.Coprime 4 m := by
    exact hodd.coprime_two_left.pow_left 2
  obtain ⟨χ4, χm, hp4, hpm, _, hqm, he⟩ :=
    primitive_quadratic_coprime_factors hcop χ hprimitive hχ
  have h4 := primitive_four_odd χ4 hp4
  have hmval := primitive_quadratic_odd_level_neg_one m χm hpm hqm hodd
  rw [ZMod.χ₄_nat_one_mod_four hm, Int.cast_one] at hmval
  change χ4 (-1) = -1 at h4
  rw [h4, hmval, mul_one] at he
  exact DirichletCharacter.Even.not_odd χ heven he

end LiuWang.Proof.EffectiveLValue
