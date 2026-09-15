import LiuWang.Proof.MultiZeroRepulsion.Continuation.GeneralMother

/-! Principal ordinary slots transported to zeta, with actual multiplicities and no low-zero table. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.MultiZeroRepulsion.Continuation

theorem general_principal_slot_height {q : ℕ} [NeZero q] {alpha y : ℝ}
    (p : ZeroSlots q alpha y) (hp : p.character = 1) : 1 < |p.value.im| := by
  by_contra hn
  have hz := mem_strictZeroValues.mp p.zero_mem
  have hm : p.value ∈ DirichletZeroCount.zeroValues (1 : DirichletCharacter ℂ q) 0 1 := by
    apply DirichletZeroCount.mem_zeroValues.mpr
    exact ⟨hp ▸ hz.1, ⟨hz.2.1, hz.2.2.2.1, le_of_not_gt hn⟩, hz.2.1.le⟩
  have hh := Finset.single_le_sum (f := fun z =>
    analyticOrderNatAt (1 : DirichletCharacter ℂ q).LFunction z) (fun _ _ => Nat.zero_le _) hm
  change _ ≤ DirichletZeroCount.count (1 : DirichletCharacter ℂ q) 0 1 at hh
  rw [DirichletZeroCount.count_principal_low q 0 (by norm_num) le_rfl] at hh
  have hi := p.index_lt
  rw [hp] at hi
  omega

def general_principal_slot {q : ℕ} [NeZero q] {alpha x : ℝ} (hx : 0 ≤ x)
    (p : ZeroSlots q alpha (x / q)) (hp : p.character = 1) :
    ZeroSlots 1 alpha (x / 1) where
  character := 1
  value := p.value
  index := p.index
  zero_mem := by
    have hz := mem_strictZeroValues.mp p.zero_mem
    have hm : p.value ∈ DirichletZeroCount.zeroValues (1 : DirichletCharacter ℂ q) alpha (x / q) := by
      rw [← hp]
      exact (Finset.mem_filter.mp p.zero_mem).1
    rw [DirichletZeroCount.zeroValues_principal_eq_zeta q] at hm
    have hh := DirichletZeroCount.mem_zeroValues.mp hm
    apply mem_strictZeroValues.mpr
    refine ⟨hh.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2.trans ?_⟩
    exact div_le_div_of_nonneg_left hx (by norm_num) (by exact_mod_cast NeZero.pos q)
  index_lt := by
    have hz := mem_strictZeroValues.mp p.zero_mem
    have h1 : p.value ≠ 1 := by intro h; simp [h] at hz
    have hi := p.index_lt
    rw [hp, PrincipalPsi.analyticOrderNatAt_principal_eq_zeta hz.2.1 h1] at hi
    simpa only [DirichletCharacter.LFunction_modOne_eq] using hi

theorem general_zeta_two_slots {alpha y sigma : ℝ}
    (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (ha : 1 / 2 ≤ alpha)
    (p r : ZeroSlots 1 alpha y) (hp : p.character = 1) (hr : r.character = 1)
    (hne : p ≠ r) (t : ℝ) :
    dampedLogDeriv (1 : DirichletCharacter ℂ 1) sigma (stechkinSigma sigma) stechkinK t +
      reflectedKernel sigma t p.value + reflectedKernel sigma t r.value ≤
      poleDifference sigma t +
      stechkinConductorCoeff * (Real.log (max 1 |t|) - Real.log Real.pi) +
        23 / 40 - 11 * stechkinK / 30 := by
  have hv : ∀ z ∈ ({p.value, r.value} : Finset ℂ), 1 / 2 < z.re ∧ z.re < 1 := by
    intro z hz
    rcases Finset.mem_insert.mp hz with he | he
    · subst z
      exact ⟨ha.trans_lt (mem_strictZeroValues.mp p.zero_mem).2.2.1,
        (mem_strictZeroValues.mp p.zero_mem).2.2.2.1⟩
    · have he := Finset.mem_singleton.mp he
      subst z
      exact ⟨ha.trans_lt (mem_strictZeroValues.mp r.zero_mem).2.2.1,
        (mem_strictZeroValues.mp r.zero_mem).2.2.2.1⟩
  have hh := ordinary_selected_bound (1 : DirichletCharacter ℂ 1) hs hs1 t {p.value, r.value} hv
  simp only [ordinaryCost, ite_true, principalPrimeCost, Nat.primeFactors_one,
    Finset.sum_empty, add_zero] at hh
  have hm := two_slots_mass_le hs p r (hp.trans hr.symm) hne t
  rw [hp] at hm
  linarith

theorem general_zeta_pair_function {alpha y sigma : ℝ}
    (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (ha : 1 / 2 ≤ alpha)
    (p r : ZeroSlots 1 alpha y) (hp : p.character = 1) (hr : r.character = 1)
    (hne : p ≠ r) (hnc : p ≠ conjugateSlot r) :
    1 / (sigma - p.value.re) + 1 / (sigma - r.value.re) +
      (reflectedKernel sigma p.value.im r.value +
        reflectedKernel sigma p.value.im (conj r.value) +
        reflectedKernel sigma r.value.im p.value +
        reflectedKernel sigma r.value.im (conj p.value)) / 2 ≤
      1 / (sigma - 1) + stechkinConductorCoeff *
        (Real.log (max 1 |p.value.im|) + Real.log (max 1 |r.value.im|) +
          (Real.log (max 1 |p.value.im + r.value.im|) +
            Real.log (max 1 |p.value.im - r.value.im|)) / 2 - 3 * Real.log Real.pi) +
        39 / 40 - 11 * stechkinK / 10 +
        (poleDifference sigma (p.value.im + r.value.im) +
          poleDifference sigma (p.value.im - r.value.im)) / 2 := by
  have hcp : (conjugateSlot p).character = 1 := by rw [conjugateSlot_character, hp, inv_one]
  have hcr : (conjugateSlot r).character = 1 := by rw [conjugateSlot_character, hr, inv_one]
  have hnc' : r ≠ conjugateSlot p := by
    intro he
    apply hnc
    have hh := congrArg conjugateSlot he
    rw [conjugateSlot_involutive] at hh
    exact hh.symm
  have h1 := general_zeta_two_slots hs hs1 ha p r hp hr hne p.value.im
  have h2 := general_zeta_two_slots hs hs1 ha p (conjugateSlot r) hp hcr hnc p.value.im
  have h3 := general_zeta_two_slots hs hs1 ha p r hp hr hne r.value.im
  have h4 := general_zeta_two_slots hs hs1 ha r (conjugateSlot p) hr hcp hnc' r.value.im
  rw [conjugateSlot_value] at h2 h4
  have hpp := poleDifference_high_nonpos hs hs1 (general_principal_slot_height p hp).le
  have hpr := poleDifference_high_nonpos hs hs1 (general_principal_slot_height r hr).le
  have he := pair_euler_nonneg (1 : DirichletCharacter ℂ 1) 1 hs p.value.im r.value.im
  simp only [Fin.sum_univ_succ, pairCoefficients, pairCharacters, pairHeights,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, one_mul,
    mul_one, inv_one] at he
  have h0 := principal_real_strong (q := 1) hs hs1
  have hplus := principal_all_height (q := 1) hs hs1 (p.value.im + r.value.im)
  have hminus := principal_all_height (q := 1) hs hs1 (p.value.im - r.value.im)
  simp only [principalPrimeCost, Nat.primeFactors_one, Finset.sum_empty, add_zero, sub_zero] at h0 hplus hminus
  have hz := mem_strictZeroValues.mp p.zero_mem
  have hw := mem_strictZeroValues.mp r.zero_mem
  have kp := selected_pair_dominates hs ⟨hz.2.1, hz.2.2.2.1⟩
  have kr := selected_pair_dominates hs ⟨hw.2.1, hw.2.2.2.1⟩
  change _ ≤ reflectedKernel sigma p.value.im p.value at kp
  change _ ≤ reflectedKernel sigma r.value.im r.value at kr
  linarith

end LiuWang.Proof.MultiZeroRepulsion.Continuation
