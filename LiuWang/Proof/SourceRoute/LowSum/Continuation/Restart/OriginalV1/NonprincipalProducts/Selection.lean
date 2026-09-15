import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.NonprincipalProducts.Kernels

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.MultiZeroRepulsion LiuWang.Proof.MultiZeroRepulsion.Continuation
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.SinglePrincipal

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.NonprincipalProducts

theorem primitive_sum_debits {d q : ℕ} [NeZero d] [NeZero q]
    (chi : DirichletCharacter ℂ d) (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    {x sigma : ℝ} (hdq : d ∣ q) (hq : (q : ℝ) ≤ x)
    (hs : 1 < sigma) (hs1 : sigma ≤ 1.02)
    {rho : ℂ} (hr : 1 / 2 < rho.re ∧ rho.re < 1) (hz : chi.LFunction rho = 0)
    (hy : |rho.im| ≤ x / q) (w : Finset ℂ) (hn : rho ∉ w)
    (hwr : ∀ z ∈ w, 1 / 2 < z.re ∧ z.re < 1)
    (hwz : ∀ z ∈ w, chi.LFunction z = 0)
    (hwg : ∀ z ∈ w, 1 - z.re ≤ sigma - 1) :
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK rho.im ≤
      nonprincipalCost x - 1 / (sigma - rho.re) -
        ∑ z ∈ w, poleDebit sigma z.re (rho.im - z.im) := by
  have hm := primitive_selected_reflections chi hc hp hs rho.im (insert rho w)
    (by simpa only [Finset.mem_insert, forall_eq_or_imp] using And.intro hr hwr)
    (by simpa only [Finset.mem_insert, forall_eq_or_imp] using And.intro hz hwz)
  rw [Finset.sum_insert hn] at hm
  have h0 := selected_pair_dominates hs ⟨by linarith [hr.1], hr.2⟩
  change _ ≤ reflectedKernel sigma rho.im rho at h0
  have h1 := Finset.sum_le_sum (s := w) (fun z h =>
    poleDebit_le_reflected hs hs1 (hwr z h).1 (hwr z h).2 (hwg z h) rho.im)
  have hb := primitive_full_zero_sum_bound hc hp hs (by linarith : sigma ≤ 23 / 20) rho.im
  have hl := mul_le_mul_of_nonneg_left (lwd_height_log hdq hq hy) conductorCoeff_bounds.1
  unfold nonprincipalCost
  nlinarith only [hm, h0, h1, hb, hl]

theorem primitive_two_debits {d q : ℕ} [NeZero d] [NeZero q]
    (chi : DirichletCharacter ℂ d) (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    {x sigma : ℝ} (hdq : d ∣ q) (hq : (q : ℝ) ≤ x)
    (hs : 1 < sigma) (hs1 : sigma ≤ 1.02)
    {rho tau upsilon : ℂ}
    (hr : 1 / 2 < rho.re ∧ rho.re < 1) (ht : 1 / 2 < tau.re ∧ tau.re < 1)
    (hu : 1 / 2 < upsilon.re ∧ upsilon.re < 1)
    (hz : chi.LFunction rho = 0) (hy : |rho.im| ≤ x / q)
    (hrt : rho ≠ conj tau) (hru : rho ≠ conj upsilon) (htu : tau ≠ upsilon)
    (hgt : 1 - tau.re ≤ sigma - 1) (hgu : 1 - upsilon.re ≤ sigma - 1)
    (P Q : Prop) [Decidable P] [Decidable Q]
    (hzt : P → chi.LFunction (conj tau) = 0)
    (hzu : Q → chi.LFunction (conj upsilon) = 0) :
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK rho.im ≤
      nonprincipalCost x - 1 / (sigma - rho.re) -
        (if P then poleDebit sigma tau.re (rho.im + tau.im) else 0) -
        (if Q then poleDebit sigma upsilon.re (rho.im + upsilon.im) else 0) := by
  let w : Finset ℂ := (if P then {conj tau} else ∅) ∪ (if Q then {conj upsilon} else ∅)
  have hmem (z : ℂ) : z ∈ w ↔ (P ∧ z = conj tau) ∨ (Q ∧ z = conj upsilon) := by
    by_cases hP : P <;> by_cases hQ : Q <;> simp [w, hP, hQ]
  have hm := primitive_sum_debits chi hc hp hdq hq hs hs1 hr hz hy w
    (by simpa only [hmem] using (show ¬ ((P ∧ rho = conj tau) ∨ (Q ∧ rho = conj upsilon))
      from fun h => h.elim (fun h => hrt h.2) (fun h => hru h.2)))
    (by intro z h; rcases (hmem z).mp h with h | h <;> rcases h with ⟨_, rfl⟩
        · simpa only [conj_re] using ht
        · simpa only [conj_re] using hu)
    (by intro z h; rcases (hmem z).mp h with h | h
        · rw [h.2]; exact hzt h.1
        · rw [h.2]; exact hzu h.1)
    (by intro z h; rcases (hmem z).mp h with h | h <;> rcases h with ⟨_, rfl⟩
        · simpa only [conj_re] using hgt
        · simpa only [conj_re] using hgu)
  have hne : conj tau ≠ conj upsilon := fun h => htu (by simpa using congrArg conj h)
  by_cases hP : P <;> by_cases hQ : Q <;>
    simpa [w, hP, hQ, Finset.sum_pair hne, sub_add_eq_sub_sub] using hm

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.NonprincipalProducts
