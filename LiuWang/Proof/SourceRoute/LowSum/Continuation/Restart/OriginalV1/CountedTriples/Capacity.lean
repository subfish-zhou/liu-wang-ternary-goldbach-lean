import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountedTriples.Transport

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.MultiZeroRepulsion LiuWang.Proof.MultiZeroRepulsion.Continuation
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountedTriples

theorem slot_fiber_capacity {d q : ℕ} [NeZero d] [NeZero q] {alpha y : ℝ}
    (chi : DirichletCharacter ℂ d) (hd : d ∣ q) (s : Finset (ZeroSlots q alpha y))
    (hl : ∀ p ∈ s, p.character = chi.changeLevel hd) (z : ℂ) :
    (s.filter (fun p => p.value = z)).card ≤ analyticOrderNatAt chi.LFunction z := by
  have hm : Set.MapsTo (fun p : ZeroSlots q alpha y => p.index)
      (s.filter (fun p => p.value = z)) (Finset.range (analyticOrderNatAt chi.LFunction z)) := by
    intro p hp
    obtain ⟨hs, hv⟩ := Finset.mem_filter.mp hp
    have hz := mem_strictZeroValues.mp p.zero_mem
    have ho := common_lift_order p.character chi (dvd_refl q) hd
      (by simpa only [DirichletCharacter.changeLevel_self] using hl p hs) hz.2.1 hz.2.2.2.1
    have hi := p.index_lt
    rw [ho, hv] at hi
    exact Finset.mem_range.mpr hi
  have hi : Set.InjOn (fun p : ZeroSlots q alpha y => p.index)
      (s.filter (fun p => p.value = z)) := by
    intro p hp r hr he
    obtain ⟨hp, hvp⟩ := Finset.mem_filter.mp hp
    obtain ⟨hr, hvr⟩ := Finset.mem_filter.mp hr
    exact zeroSlots_ext ((hl p hp).trans (hl r hr).symm) (hvp.trans hvr.symm) he
  simpa only [Finset.card_range] using Finset.card_le_card_of_injOn _ hm hi

theorem slots_mass_le {d q : ℕ} [NeZero d] [NeZero q] {alpha y sigma : ℝ}
    (chi : DirichletCharacter ℂ d) (hd : d ∣ q) (hs : 1 < sigma)
    (s : Finset (ZeroSlots q alpha y)) (hl : ∀ p ∈ s, p.character = chi.changeLevel hd) (t : ℝ) :
    (∑ p ∈ s, reflectedKernel sigma t p.value) ≤
      ordinaryMass chi sigma t (s.image ZeroSlots.value) := by
  have hf := Finset.sum_fiberwise_of_maps_to
    (show ∀ p ∈ s, p.value ∈ s.image ZeroSlots.value from fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩)
    (fun p : ZeroSlots q alpha y => reflectedKernel sigma t p.value)
  rw [← hf]
  apply Finset.sum_le_sum
  intro z hz
  have hn : 0 ≤ reflectedKernel sigma t z := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    have hh := mem_strictZeroValues.mp p.zero_mem
    exact dampedZeroKernel_pair_nonneg hs t ⟨hh.2.1.le, hh.2.2.2.1.le⟩
  have hc : ((s.filter (fun p => p.value = z)).card : ℝ) ≤ analyticOrderNatAt chi.LFunction z := by
    exact_mod_cast slot_fiber_capacity chi hd s hl z
  have he : (∑ p ∈ s.filter (fun p => p.value = z), reflectedKernel sigma t p.value) =
      (s.filter (fun p => p.value = z)).card * reflectedKernel sigma t z := by
    calc
      _ = ∑ _p ∈ s.filter (fun p => p.value = z), reflectedKernel sigma t z := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [(Finset.mem_filter.mp hp).2]
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  rw [he]
  exact mul_le_mul_of_nonneg_right hc hn

theorem slots_primitive_mass {d q : ℕ} [NeZero d] [NeZero q] {alpha y sigma : ℝ}
    (chi : DirichletCharacter ℂ d) (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    (hd : d ∣ q) (hs : 1 < sigma) (s : Finset (ZeroSlots q alpha y))
    (hl : ∀ p ∈ s, p.character = chi.changeLevel hd)
    (hr : ∀ p ∈ s, 1 / 2 < p.value.re) (t : ℝ) :
    (∑ p ∈ s, reflectedKernel sigma t p.value) ≤ primitiveZeroSum chi sigma t := by
  apply (slots_mass_le chi hd hs s hl t).trans
  apply primitive_ordinary_mass_le hc hp hs
  intro z hz
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
  exact hr p hp

theorem slots_principal_mass {q : ℕ} [NeZero q] {alpha y sigma : ℝ}
    (hs : 1 < sigma) (s : Finset (ZeroSlots q alpha y))
    (hl : ∀ p ∈ s, p.character = 1) (hr : ∀ p ∈ s, 1 / 2 < p.value.re) (t : ℝ) :
    (∑ p ∈ s, reflectedKernel sigma t p.value) ≤ zetaZeroSum sigma t := by
  apply (slots_mass_le (1 : DirichletCharacter ℂ q) (dvd_refl q) hs s
    (by simpa only [map_one] using hl) t).trans
  apply principal_ordinary_mass_le q hs
  intro z hz
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
  exact ⟨hr p hp, (mem_strictZeroValues.mp p.zero_mem).2.2.2.1⟩

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountedTriples
