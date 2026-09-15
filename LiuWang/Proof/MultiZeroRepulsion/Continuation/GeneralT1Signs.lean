import LiuWang.Proof.MultiZeroRepulsion.Continuation.GeneralT1TriplePrincipal

/-! The four signed ordinary sources use the same primitive Euler functions and multiplicities. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.NearOneDensity.Continuation

namespace LiuWang.Proof.MultiZeroRepulsion.Continuation

theorem t1_primitive_self_coeff {d : ℕ} [NeZero d] (chi : DirichletCharacter ℂ d)
    (hp : chi.IsPrimitive) (n : ℕ) : chi.primitiveCharacter n = chi n := by
  by_cases hn : n.Coprime d
  · simpa only [Int.cast_natCast] using
      chi.primitiveCharacter_apply_of_isCoprime (Nat.isCoprime_iff_coprime.mpr hn)
  · have h1 : ¬ IsUnit (n : ZMod d) := by rwa [ZMod.isUnit_iff_coprime]
    have h2 : ¬ IsUnit (n : ZMod chi.conductor) := by
      rw [ZMod.isUnit_iff_coprime]
      change chi.conductor = d at hp
      rwa [hp]
    rw [MulChar.map_nonunit chi.primitiveCharacter h2, MulChar.map_nonunit chi h1]

theorem t1_primitive_source_coeff {d q : ℕ} [NeZero d] [NeZero q]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ q) (hd : d ∣ q)
    (hp : chi.IsPrimitive) (hlift : chi.changeLevel hd = psi) (n : ℕ) :
    psi.primitiveCharacter n = chi n := by
  have hh := DirichletCharacter.primitiveCharacter_changeLevel_apply hd chi (n : ℤ)
  rw [hlift] at hh
  have hh' : psi.primitiveCharacter n = chi.primitiveCharacter n := by
    simpa only [Int.cast_natCast] using hh
  exact hh'.trans (t1_primitive_self_coeff chi hp n)

theorem t1G_congr_coefficients {d e f d' e' f' : ℕ}
    [NeZero d] [NeZero e] [NeZero f] [NeZero d'] [NeZero e'] [NeZero f']
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e) (eta : DirichletCharacter ℂ f)
    (chi' : DirichletCharacter ℂ d') (psi' : DirichletCharacter ℂ e') (eta' : DirichletCharacter ℂ f')
    (hc : ∀ n : ℕ, chi n = chi' n) (hp : ∀ n : ℕ, psi n = psi' n)
    (he : ∀ n : ℕ, eta n = eta' n) {sigma : ℝ} (hs : 1 < sigma) (t u v : ℝ) :
    t1G chi psi eta sigma t u v = t1G chi' psi' eta' sigma t u v := by
  have hcp (n : ℕ) : t1Product chi psi n = t1Product chi' psi' n := by
    simp only [t1Product_apply, hc n, hp n]
  have hce (n : ℕ) : t1Product chi eta n = t1Product chi' eta' n := by
    simp only [t1Product_apply, hc n, he n]
  have hpe (n : ℕ) : t1Product psi eta n = t1Product psi' eta' n := by
    simp only [t1Product_apply, hp n, he n]
  have htr (n : ℕ) : t1Product (t1Product chi psi) eta n = t1Product (t1Product chi' psi') eta' n := by
    simp only [t1Product_apply, hc n, hp n, he n]
  unfold t1G
  rw [general_damped_eq_of_nat_values _ _ hc hs, general_damped_eq_of_nat_values _ _ hp hs,
    general_damped_eq_of_nat_values _ _ he hs, general_damped_eq_of_nat_values _ _ hcp hs,
    general_damped_eq_of_nat_values _ _ hce hs, general_damped_eq_of_nat_values _ _ hpe hs,
    general_damped_eq_of_nat_values _ _ htr hs]

def t1SourceG {q : ℕ} [NeZero q] (chi psi eta : DirichletCharacter ℂ q)
    (sigma t u v : ℝ) : ℝ :=
  @t1G chi.conductor psi.conductor eta.conductor ⟨chi.conductor_ne_zero⟩
    ⟨psi.conductor_ne_zero⟩ ⟨eta.conductor_ne_zero⟩
    chi.primitiveCharacter psi.primitiveCharacter eta.primitiveCharacter sigma t u v

def t1OrientSlot {q : ℕ} [NeZero q] {alpha y : ℝ} (p : ZeroSlots q alpha y) (b : Bool) :
    ZeroSlots q alpha y := if b then conjugateSlot p else p

theorem t1OrientSlot_character {q : ℕ} [NeZero q] {alpha y : ℝ}
    (p : ZeroSlots q alpha y) (b : Bool) :
    (t1OrientSlot p b).character = t1Orient p.character b := by
  cases b <;> simp [t1OrientSlot, t1Orient, conjugateSlot_character]

theorem t1OrientSlot_value {q : ℕ} [NeZero q] {alpha y : ℝ}
    (p : ZeroSlots q alpha y) (b : Bool) : (t1OrientSlot p b).value = t1OrientValue p.value b := by
  cases b <;> simp [t1OrientSlot, t1OrientValue, conjugateSlot_value]

theorem t1SourceG_orient {q : ℕ} [NeZero q] (chi psi eta : DirichletCharacter ℂ q)
    [NeZero chi.conductor] [NeZero psi.conductor] [NeZero eta.conductor]
    (b c : Bool) {sigma : ℝ} (hs : 1 < sigma) (t u v : ℝ) :
    t1SourceG chi (t1Orient psi b) (t1Orient eta c) sigma t u v =
      t1G chi.primitiveCharacter (t1Orient psi.primitiveCharacter b)
        (t1Orient eta.primitiveCharacter c) sigma t u v := by
  have hcoeff (psi : DirichletCharacter ℂ q) [NeZero psi.conductor] (b : Bool) (n : ℕ) :
      (t1Orient psi b).primitiveCharacter n = t1Orient psi.primitiveCharacter b n := by
    apply t1_primitive_source_coeff _ _ psi.conductor_dvd_level
      (t1Orient_primitive psi.primitiveCharacter_isPrimitive b)
    rw [t1Orient_changeLevel, DirichletCharacter.changeLevel_primitiveCharacter]
  let : NeZero (t1Orient psi b).conductor := ⟨(t1Orient psi b).conductor_ne_zero⟩
  let : NeZero (t1Orient eta c).conductor := ⟨(t1Orient eta c).conductor_ne_zero⟩
  unfold t1SourceG
  exact t1G_congr_coefficients _ _ _ _ _ _ (fun _ => rfl) (hcoeff psi b) (hcoeff eta c) hs t u v

theorem t1SourceG_four_nonneg {q : ℕ} [NeZero q] {alpha y sigma : ℝ}
    (p r s : ZeroSlots q alpha y) (hs : 1 < sigma) :
    0 ≤ t1SourceG p.character r.character s.character sigma p.value.im r.value.im s.value.im +
      t1SourceG p.character (conjugateSlot r).character s.character
        sigma p.value.im (conjugateSlot r).value.im s.value.im +
      t1SourceG p.character r.character (conjugateSlot s).character
        sigma p.value.im r.value.im (conjugateSlot s).value.im +
      t1SourceG p.character (conjugateSlot r).character (conjugateSlot s).character
        sigma p.value.im (conjugateSlot r).value.im (conjugateSlot s).value.im := by
  let : NeZero p.character.conductor := ⟨p.character.conductor_ne_zero⟩
  let : NeZero r.character.conductor := ⟨r.character.conductor_ne_zero⟩
  let : NeZero s.character.conductor := ⟨s.character.conductor_ne_zero⟩
  have h1 := t1SourceG_orient p.character r.character s.character false false hs
    p.value.im r.value.im s.value.im
  have h2 := t1SourceG_orient p.character r.character s.character true false hs
    p.value.im (-r.value.im) s.value.im
  have h3 := t1SourceG_orient p.character r.character s.character false true hs
    p.value.im r.value.im (-s.value.im)
  have h4 := t1SourceG_orient p.character r.character s.character true true hs
    p.value.im (-r.value.im) (-s.value.im)
  simp only [t1Orient, Bool.false_eq_true, if_false, if_true] at h1 h2 h3 h4
  simp only [conjugateSlot_character, conjugateSlot_value, conj_im]
  rw [h1, h2, h3, h4]
  exact t1_euler_nonneg _ _ _ hs _ _ _

end LiuWang.Proof.MultiZeroRepulsion.Continuation
