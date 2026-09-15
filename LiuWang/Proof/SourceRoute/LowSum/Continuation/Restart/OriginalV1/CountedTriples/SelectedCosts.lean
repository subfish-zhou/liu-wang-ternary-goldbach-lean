import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountedTriples.Capacity

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.MultiZeroRepulsion LiuWang.Proof.MultiZeroRepulsion.Continuation
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.SinglePrincipal
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.NonprincipalProducts

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountedTriples

theorem principal_slot_RS {q : ℕ} [NeZero q] {alpha y : ℝ}
    (p : ZeroSlots q alpha y) (hp : p.character = 1) (hr : 1 / 2 < p.value.re)
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2) : 1894438 ≤ |p.value.im| := by
  have hz := mem_strictZeroValues.mp p.zero_mem
  have hzero : riemannZeta p.value = 0 :=
    (PrincipalPsi.principal_zero_iff_zeta_zero hz.2.1
      (by intro he; simp [he] at hz)).mp (hp ▸ hz.1)
  by_contra hn
  have hh := hRS p.value hzero hz.2.1 hz.2.2.2.1 (lt_of_not_ge hn)
  linarith

theorem primitive_selected_cost {d q : ℕ} [NeZero d] [NeZero q] {alpha y x sigma t : ℝ}
    (chi : DirichletCharacter ℂ d) (hp : chi.IsPrimitive)
    (hd : d ∣ q) (hq : (q : ℝ) ≤ x) (hs : 1 < sigma) (hs1 : sigma ≤ 1.02)
    (ht : |t| ≤ x / q) (hmain : chi = 1 → 1 ≤ |t|)
    (s : Finset (ZeroSlots q alpha y)) (hl : ∀ p ∈ s, p.character = chi.changeLevel hd)
    (hr : ∀ p ∈ s, 1 / 2 < p.value.re)
    (hgammaHigh : ∀ v : ℝ, 1 ≤ |v| → gammaHalfDifference sigma v <
      stechkinConductorCoeff * Real.log |v| + 0.3316) :
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK t +
      (∑ p ∈ s, reflectedKernel sigma t p.value) ≤ nonprincipalCost x := by
  have hlx := mul_le_mul_of_nonneg_left (lwd_height_log hd hq ht) conductorCoeff_bounds.1
  by_cases hc : chi = 1
  · have hd1 := primitive_principal_level chi hp hc
    subst d
    have hm := slots_principal_mass hs s (by simpa only [hc, map_one] using hl) hr t
    have hz := zeta_full_zero_sum_identity hs t
    have hpo := poleDifference_high_nonpos hs (by linarith : sigma ≤ 23 / 20) (hmain hc)
    have hg := hgammaHigh t (hmain hc)
    rw [shiftedGamma_eq] at hz
    rw [hc, principal_damped_eq]
    simp only [Nat.cast_one, Real.log_one, zero_add, max_eq_right (hmain hc)] at hlx
    unfold nonprincipalCost
    linarith
  · have hm := slots_primitive_mass chi hc hp hd hs s hl hr t
    have hb := primitive_full_zero_sum_bound hc hp hs (by linarith : sigma ≤ 23 / 20) t
    unfold nonprincipalCost
    nlinarith only [hm, hb, hlx]

theorem ordinary_selected_cost {d q : ℕ} [NeZero d] [NeZero q] {alpha y x sigma t : ℝ}
    (chi : DirichletCharacter ℂ d) (hd : d ∣ q) (hq : (q : ℝ) ≤ x)
    (hs : 1 < sigma) (hs1 : sigma ≤ 1.02) (ht : |t| ≤ x / q)
    (hmain : chi = 1 → 1 ≤ |t|)
    (s : Finset (ZeroSlots q alpha y)) (hl : ∀ p ∈ s, p.character = chi.changeLevel hd)
    (hr : ∀ p ∈ s, 1 / 2 < p.value.re)
    (hgammaHigh : ∀ v : ℝ, 1 ≤ |v| → gammaHalfDifference sigma v <
      stechkinConductorCoeff * Real.log |v| + 0.3316) :
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK t +
      (∑ p ∈ s, reflectedKernel sigma t p.value) ≤ nonprincipalCost x + 0.4977 := by
  have hlx := mul_le_mul_of_nonneg_left (lwd_height_log hd hq ht) conductorCoeff_bounds.1
  by_cases hc : chi = 1
  · have hm := slots_principal_mass hs s (by simpa only [hc, map_one] using hl) hr t
    have hz := zeta_full_zero_sum_identity hs t
    have hpo := poleDifference_high_nonpos hs (by linarith : sigma ≤ 23 / 20) (hmain hc)
    have hg := hgammaHigh t (hmain hc)
    have he := principal_damped_euler_bound (q := d) hs t
    change _ ≤ zetaDamped sigma t + principalPrimeCost d sigma at he
    have hcost := lwd_2_3 d hs
    rw [shiftedGamma_eq] at hz
    rw [hc]
    rw [max_eq_right (hmain hc)] at hlx
    unfold nonprincipalCost
    nlinarith only [hm, hz, hpo, hg, he, hcost, hlx]
  · have hm := slots_mass_le chi hd hs s hl t
    have hb := nonprincipal_ordinary_selected_bound chi hc hs (by linarith : sigma ≤ 23 / 20)
      t (s.image ZeroSlots.value) (by
        intro z hz
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
        exact hr p hp)
    have he := lwd_2_9 chi hs
    unfold nonprincipalCost ordinaryMass at *
    nlinarith only [hm, hb, he, hlx]

theorem primitive_slot_debits {d q : ℕ} [NeZero d] [NeZero q] {alpha y x sigma : ℝ}
    (chi : DirichletCharacter ℂ d) (hp : chi.IsPrimitive) (hd : d ∣ q)
    (hq : (q : ℝ) ≤ x) (hs : 1 < sigma) (hs1 : sigma ≤ 1.02)
    (p r u : ZeroSlots q alpha y) (hl : p.character = chi.changeLevel hd)
    (hrp : 1 / 2 < p.value.re) (hrr : 1 / 2 < r.value.re) (hru : 1 / 2 < u.value.re)
    (ht : |p.value.im| ≤ x / q) (hmain : chi = 1 → 1 ≤ |p.value.im|)
    (hpr : p ≠ conjugateSlot r) (hpu : p ≠ conjugateSlot u) (hru' : r ≠ u)
    (hgr : 1 - r.value.re ≤ sigma - 1) (hgu : 1 - u.value.re ≤ sigma - 1)
    (P Q : Prop) [Decidable P] [Decidable Q]
    (hPr : P → r.character⁻¹ = p.character) (hQu : Q → u.character⁻¹ = p.character)
    (hgammaHigh : ∀ v : ℝ, 1 ≤ |v| → gammaHalfDifference sigma v <
      stechkinConductorCoeff * Real.log |v| + 0.3316) :
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK p.value.im ≤
      nonprincipalCost x - 1 / (sigma - p.value.re) -
        (if P then poleDebit sigma r.value.re (p.value.im + r.value.im) else 0) -
        (if Q then poleDebit sigma u.value.re (p.value.im + u.value.im) else 0) := by
  let w : Finset (ZeroSlots q alpha y) :=
    (if P then {conjugateSlot r} else ∅) ∪ (if Q then {conjugateSlot u} else ∅)
  have hmem (z : ZeroSlots q alpha y) :
      z ∈ w ↔ (P ∧ z = conjugateSlot r) ∨ (Q ∧ z = conjugateSlot u) := by
    by_cases hP : P <;> by_cases hQ : Q <;> simp [w, hP, hQ]
  have hn : p ∉ w := by
    rw [hmem]
    exact fun h => h.elim (fun h => hpr h.2) (fun h => hpu h.2)
  have hwlabel : ∀ z ∈ w, z.character = chi.changeLevel hd := by
    intro z hz
    rcases (hmem z).mp hz with ⟨hP, rfl⟩ | ⟨hQ, rfl⟩
    · exact (hPr hP).trans hl
    · exact (hQu hQ).trans hl
  have hwre : ∀ z ∈ w, 1 / 2 < z.value.re := by
    intro z hz
    rcases (hmem z).mp hz with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact hrr
    · exact hru
  have hwgap : ∀ z ∈ w, 1 - z.value.re ≤ sigma - 1 := by
    intro z hz
    rcases (hmem z).mp hz with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact hgr
    · exact hgu
  have hb := primitive_selected_cost chi hp hd hq hs hs1 ht hmain (insert p w)
    (by simpa only [Finset.mem_insert, forall_eq_or_imp] using And.intro hl hwlabel)
    (by simpa only [Finset.mem_insert, forall_eq_or_imp] using And.intro hrp hwre) hgammaHigh
  rw [Finset.sum_insert hn] at hb
  have h0 := selected_pair_dominates hs
    ⟨(mem_strictZeroValues.mp p.zero_mem).2.1, (mem_strictZeroValues.mp p.zero_mem).2.2.2.1⟩
  change _ ≤ reflectedKernel sigma p.value.im p.value at h0
  have h1 := Finset.sum_le_sum (s := w) (fun z hz =>
    poleDebit_le_reflected hs hs1 (hwre z hz)
      (mem_strictZeroValues.mp z.zero_mem).2.2.2.1 (hwgap z hz) p.value.im)
  have hne : conjugateSlot r ≠ conjugateSlot u :=
    fun h => hru' (conjugateSlot_involutive.injective h)
  have hh : dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK p.value.im ≤
      nonprincipalCost x - 1 / (sigma - p.value.re) -
        ∑ z ∈ w, poleDebit sigma z.value.re (p.value.im - z.value.im) := by linarith
  by_cases hP : P <;> by_cases hQ : Q <;>
    simpa [w, hP, hQ, Finset.sum_pair hne, sub_add_eq_sub_sub,
      conjugateSlot_value] using hh

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountedTriples
