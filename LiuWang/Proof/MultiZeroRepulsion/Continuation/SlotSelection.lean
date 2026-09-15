import LiuWang.Proof.MultiZeroRepulsion.Continuation.OffHeight
import LiuWang.Proof.MultiZeroRepulsion.ConjugateSlots

/-! Two distinct labelled multiplicity slots, without distinct-zero-value assumptions. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.MultiZeroRepulsion.Continuation

theorem two_slots_mass_le {q : ℕ} [NeZero q] {alpha y sigma : ℝ}
    (hs : 1 < sigma) (p r : ZeroSlots q alpha y)
    (hc : p.character = r.character) (hne : p ≠ r) (t : ℝ) :
    reflectedKernel sigma t p.value + reflectedKernel sigma t r.value ≤
      ordinaryMass p.character sigma t {p.value, r.value} := by
  have hp := mem_strictZeroValues.mp p.zero_mem
  have hr := mem_strictZeroValues.mp r.zero_mem
  have kp : 0 ≤ reflectedKernel sigma t p.value :=
    dampedZeroKernel_pair_nonneg hs t ⟨hp.2.1.le, hp.2.2.2.1.le⟩
  have kr : 0 ≤ reflectedKernel sigma t r.value :=
    dampedZeroKernel_pair_nonneg hs t ⟨hr.2.1.le, hr.2.2.2.1.le⟩
  have hir : r.index < analyticOrderNatAt p.character.LFunction r.value := by
    rw [hc]
    exact r.index_lt
  by_cases hv : p.value = r.value
  · have hidx : p.index ≠ r.index := by
      intro he
      exact hne (zeroSlots_ext hc hv he)
    have hip := p.index_lt
    rw [hv] at hip
    have hm : (2 : ℝ) ≤ analyticOrderNatAt p.character.LFunction r.value := by
      have hn : 2 ≤ analyticOrderNatAt p.character.LFunction r.value := by omega
      exact_mod_cast hn
    simp only [hv, Finset.insert_eq_of_mem (Finset.mem_singleton_self _),
      ordinaryMass, Finset.sum_singleton]
    nlinarith
  · have hmp : (1 : ℝ) ≤ analyticOrderNatAt p.character.LFunction p.value := by
      exact_mod_cast (Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) p.index_lt))
    have hmr : (1 : ℝ) ≤ analyticOrderNatAt p.character.LFunction r.value := by
      exact_mod_cast (Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) hir))
    have hnot : p.value ∉ ({r.value} : Finset ℂ) := by simpa only [Finset.mem_singleton] using hv
    unfold ordinaryMass
    rw [Finset.sum_insert hnot, Finset.sum_singleton]
    nlinarith

theorem primitive_two_slots_bound {q : ℕ} [NeZero q] {alpha y sigma : ℝ}
    (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (ha : 1 / 2 ≤ alpha)
    (p r : ZeroSlots q alpha y) (hc : p.character = r.character) (hne : p ≠ r)
    (hnp : p.character ≠ 1) (hprim : p.character.IsPrimitive) (t : ℝ) :
    dampedLogDeriv p.character sigma (stechkinSigma sigma) stechkinK t +
      reflectedKernel sigma t p.value + reflectedKernel sigma t r.value ≤
      stechkinConductorCoeff * (Real.log q + Real.log (max 1 |t|) - Real.log Real.pi) + 4 / 15 := by
  have hv : ∀ z ∈ ({p.value, r.value} : Finset ℂ), 1 / 2 < z.re := by
    intro z hz
    rcases Finset.mem_insert.mp hz with he | he
    · subst z
      exact ha.trans_lt (mem_strictZeroValues.mp p.zero_mem).2.2.1
    · have he := Finset.mem_singleton.mp he
      subst z
      exact ha.trans_lt (mem_strictZeroValues.mp r.zero_mem).2.2.1
  have hm := primitive_ordinary_mass_le hnp hprim hs t {p.value, r.value} hv
  change ordinaryMass p.character sigma t {p.value, r.value} ≤ _ at hm
  have hh := primitive_full_zero_sum_bound hnp hprim hs hs1 t
  linarith [two_slots_mass_le hs p r hc hne t]

end LiuWang.Proof.MultiZeroRepulsion.Continuation
