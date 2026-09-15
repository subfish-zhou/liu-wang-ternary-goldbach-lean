import LiuWang.Proof.MultiZeroRepulsion.Continuation.GeneralT1Pole

/-! Arbitrarily many actual multiplicity slots selected simultaneously, without a distinct-value assumption. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.MultiZeroRepulsion.Continuation

def t1FixedSlotsEquiv {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (alpha y : ℝ) :
    {p : ZeroSlots q alpha y // p.character = chi} ≃
      Σ rho : {rho : ℂ // rho ∈ strictZeroValues chi alpha y},
        Fin (analyticOrderNatAt chi.LFunction rho.val) where
  toFun p := ⟨⟨p.val.value, by simpa only [p.property] using p.val.zero_mem⟩,
    ⟨p.val.index, by simpa only [p.property] using p.val.index_lt⟩⟩
  invFun p := ⟨⟨chi, p.1.val, p.2.val, p.1.property, p.2.isLt⟩, rfl⟩
  left_inv p := by
    apply Subtype.ext
    exact zeroSlots_ext p.property.symm rfl rfl
  right_inv p := by rcases p with ⟨⟨rho, hr⟩, ⟨k, hk⟩⟩; rfl

theorem t1_fixed_slots_sum {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (alpha y sigma t : ℝ) :
    (∑ p : {p : ZeroSlots q alpha y // p.character = chi}, reflectedKernel sigma t p.val.value) =
      ordinaryMass chi sigma t (strictZeroValues chi alpha y) := by
  rw [Fintype.sum_equiv (t1FixedSlotsEquiv chi alpha y) (fun p => reflectedKernel sigma t p.val.value)
    (fun p => reflectedKernel sigma t p.1.val) (fun _ => rfl)]
  simp only [Fintype.sum_sigma, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ordinaryMass]
  exact (Finset.sum_subtype (strictZeroValues chi alpha y) (fun _ => Iff.rfl)
    (fun z => (analyticOrderNatAt chi.LFunction z : ℝ) * reflectedKernel sigma t z)).symm

theorem t1_slots_mass_le {q : ℕ} [NeZero q] {alpha y sigma : ℝ}
    (chi : DirichletCharacter ℂ q) (hs : 1 < sigma) (t : ℝ)
    (s : Finset (ZeroSlots q alpha y)) (hc : ∀ p ∈ s, p.character = chi) :
    (∑ p ∈ s, reflectedKernel sigma t p.value) ≤
      ordinaryMass chi sigma t (strictZeroValues chi alpha y) := by
  let f : {p // p ∈ s} → {p : ZeroSlots q alpha y // p.character = chi} :=
    fun p => ⟨p.val, hc p.val p.property⟩
  have hinj : Function.Injective f := by
    intro p r he
    have hh := congrArg Subtype.val he
    apply Subtype.ext
    exact hh
  have he : (∑ p ∈ s.attach.image f, reflectedKernel sigma t p.val.value) =
      ∑ p ∈ s, reflectedKernel sigma t p.value := by
    rw [Finset.sum_image (fun a _ b _ h => hinj h)]
    change (∑ p ∈ s.attach, reflectedKernel sigma t p.val.value) = _
    exact Finset.sum_attach s (fun p : ZeroSlots q alpha y => reflectedKernel sigma t p.value)
  rw [← he, ← t1_fixed_slots_sum chi alpha y sigma t]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro p _ _
  have hz := mem_strictZeroValues.mp p.val.zero_mem
  exact dampedZeroKernel_pair_nonneg hs t ⟨hz.2.1.le, hz.2.2.2.1.le⟩

theorem t1_source_slots_bound {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    [NeZero chi.conductor] (hchi : chi ≠ 1) {alpha y sigma : ℝ}
    (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (ha : 1 / 2 ≤ alpha)
    (t : ℝ) (s : Finset (ZeroSlots q alpha y)) (hc : ∀ p ∈ s, p.character = chi) :
    dampedLogDeriv chi.primitiveCharacter sigma (stechkinSigma sigma) stechkinK t +
      (∑ p ∈ s, reflectedKernel sigma t p.value) ≤
      stechkinConductorCoeff * (Real.log chi.conductor + Real.log (max 1 |t|) - Real.log Real.pi) +
        4 / 15 := by
  have hp := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hchi
  have hm := primitive_ordinary_mass_le hp chi.primitiveCharacter_isPrimitive hs t
    (strictZeroValues chi alpha y) (fun z hz => ha.trans_lt (mem_strictZeroValues.mp hz).2.2.1)
  have he : (∑ z ∈ strictZeroValues chi alpha y,
      (analyticOrderNatAt chi.primitiveCharacter.LFunction z : ℝ) * reflectedKernel sigma t z) =
      ordinaryMass chi sigma t (strictZeroValues chi alpha y) := by
    apply Finset.sum_congr rfl
    intro z hz
    rw [analyticOrderNatAt_LFunction_eq_primitive chi hchi (mem_strictZeroValues.mp hz).2.1]
  rw [he] at hm
  have hh := primitive_full_zero_sum_bound hp chi.primitiveCharacter_isPrimitive hs hs1 t
  linarith [t1_slots_mass_le chi hs t s hc]

theorem t1_principal_slots_bound {q : ℕ} [NeZero q] {alpha y sigma : ℝ}
    (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (ha : 1 / 2 ≤ alpha)
    (t : ℝ) (s : Finset (ZeroSlots q alpha y)) (hc : ∀ p ∈ s, p.character = 1) :
    zetaDamped sigma t + (∑ p ∈ s, reflectedKernel sigma t p.value) ≤
      poleDifference sigma t +
      stechkinConductorCoeff * (Real.log (max 1 |t|) - Real.log Real.pi) +
        23 / 40 - 11 * stechkinK / 30 := by
  have hm := principal_ordinary_mass_le q hs t
    (strictZeroValues (1 : DirichletCharacter ℂ q) alpha y)
    (fun z hz => ⟨ha.trans_lt (mem_strictZeroValues.mp hz).2.2.1,
      (mem_strictZeroValues.mp hz).2.2.2.1⟩)
  change ordinaryMass (1 : DirichletCharacter ℂ q) sigma t _ ≤ _ at hm
  have hh := zeta_full_zero_sum_identity hs t
  have hg := shiftedGamma_all_height hs hs1 t
  linarith [t1_slots_mass_le (1 : DirichletCharacter ℂ q) hs t s hc]

theorem t1_three_slots_mass_le {q : ℕ} [NeZero q] {alpha y sigma : ℝ}
    (hs : 1 < sigma) (p r s : ZeroSlots q alpha y) (t : ℝ)
    (hpr : p ≠ r) (hps : p ≠ s) (hrs : r ≠ s)
    (hcr : r.character = p.character) (hcs : s.character = p.character) :
    reflectedKernel sigma t p.value + reflectedKernel sigma t r.value + reflectedKernel sigma t s.value ≤
      ordinaryMass p.character sigma t (strictZeroValues p.character alpha y) := by
  have hh := t1_slots_mass_le p.character hs t {p, r, s} (by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · rfl
    · exact hcr
    · exact hcs)
  simpa only [Finset.sum_insert (show p ∉ ({r, s} : Finset _) by simp [hpr, hps]),
    Finset.sum_insert (show r ∉ ({s} : Finset _) by simp [hrs]), Finset.sum_singleton, add_assoc] using hh

end LiuWang.Proof.MultiZeroRepulsion.Continuation
