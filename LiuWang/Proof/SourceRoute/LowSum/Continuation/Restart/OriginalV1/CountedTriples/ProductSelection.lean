import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountedTriples.Data

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

theorem principal_pair_slot_labels {d e q : ℕ} [NeZero q] {alpha y : ℝ}
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    (hd : d ∣ q) (he : e ∣ q) (p r : ZeroSlots q alpha y)
    (hp : p.character = chi.changeLevel hd) (hr : r.character = psi.changeLevel he)
    (hm : lwdProduct chi psi = 1) :
    r.character⁻¹ = p.character ∧ p.character⁻¹ = r.character := by
  have hh : p.character * r.character = 1 := by
    rw [hp, hr]
    exact (product_principal_iff chi psi hd he).mp hm
  exact ⟨inv_eq_of_mul_eq_one_left hh, inv_eq_of_mul_eq_one_right hh⟩

theorem principal_triple_slot_label {d e f q : ℕ} [NeZero q] {alpha y : ℝ}
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    (eta : DirichletCharacter ℂ f) (hd : d ∣ q) (he : e ∣ q) (hf : f ∣ q)
    (u : ZeroSlots q alpha y) (hu : u.character = eta.changeLevel hf)
    (hm : lwdProduct (lwdProduct chi psi) eta = 1) :
    (conjugateSlot u).character = (lwdProduct chi psi).changeLevel (Nat.lcm_dvd hd he) := by
  rw [conjugateSlot_character, hu, product_changeLevel chi psi hd he]
  exact inv_eq_of_mul_eq_one_left ((triple_principal_iff chi psi eta hd he hf).mp hm)

theorem pair_with_triple_debit {d e f q : ℕ} [NeZero d] [NeZero e] [NeZero f] [NeZero q]
    {x alpha sigma : ℝ}
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e) (eta : DirichletCharacter ℂ f)
    (hd : d ∣ q) (he : e ∣ q) (hf : f ∣ q) (hq : (q : ℝ) ≤ x)
    (p r u : ZeroSlots q alpha (x / q))
    (hu : u.character = eta.changeLevel hf) (hru : 1 / 2 < u.value.re)
    (hs : 1 < sigma) (hs1 : sigma ≤ 1.02)
    (hgp : 1 - p.value.re ≤ sigma - 1) (hgr : 1 - r.value.re ≤ sigma - 1)
    (hgu : 1 - u.value.re ≤ sigma - 1)
    (hm : lwdProduct (lwdProduct chi psi) eta = 1)
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2)
    (hgammaHigh : ∀ v : ℝ, 1 ≤ |v| → gammaHalfDifference sigma v <
      stechkinConductorCoeff * Real.log |v| + 0.3316)
    (hgammaLow : ∀ v : ℝ, |v| < 1 → gammaHalfDifference sigma v < 0.0615) :
    dampedLogDeriv (lwdProduct chi psi) sigma (stechkinSigma sigma) stechkinK
      (p.value.im + r.value.im) -
      (if lwdProduct chi psi = 1 then poleDebit sigma p.value.re (p.value.im + r.value.im) else 0) -
      (if lwdProduct chi psi = 1 then poleDebit sigma r.value.re (p.value.im + r.value.im) else 0) +
      poleDebit sigma u.value.re (p.value.im + r.value.im + u.value.im) ≤
        nonprincipalCost (2 * x) + 0.4977 := by
  have hp := mem_strictZeroValues.mp p.zero_mem
  have hr := mem_strictZeroValues.mp r.zero_mem
  have hu' := mem_strictZeroValues.mp u.zero_mem
  have hx : 0 < x := (show (0 : ℝ) < q by exact_mod_cast NeZero.pos q).trans_le hq
  by_cases ht : |p.value.im + r.value.im + u.value.im| < 1
  · have hhigh : lwdProduct chi psi = 1 → 1 ≤ |p.value.im + r.value.im| := by
      intro hpair
      have hzlabel := principal_triple_slot_label chi psi eta hd he hf u hu hm
      have hul : u.character = 1 := by
        simpa only [hpair, map_one, conjugateSlot_character, inv_eq_one] using hzlabel
      have hh := principal_slot_RS u hul hru hRS
      have heq : u.value.im = (p.value.im + r.value.im + u.value.im) - (p.value.im + r.value.im) := by ring
      have hab := abs_add_le (p.value.im + r.value.im + u.value.im) (-(p.value.im + r.value.im))
      rw [← sub_eq_add_neg, abs_neg, ← heq] at hab
      linarith
    have hheight : |p.value.im + r.value.im| ≤ (2 * x) / q := by
      rw [mul_div_assoc]
      linarith [abs_add_le p.value.im r.value.im, hp.2.2.2.2, hr.2.2.2.2]
    have hc := ordinary_selected_cost (lwdProduct chi psi) (Nat.lcm_dvd hd he)
      (by linarith : (q : ℝ) ≤ 2 * x) hs hs1 hheight hhigh {conjugateSlot u}
      (by
        intro z hz
        rw [Finset.mem_singleton] at hz
        subst z
        exact principal_triple_slot_label chi psi eta hd he hf u hu hm)
      (by simpa only [Finset.mem_singleton, forall_eq, conjugateSlot_value, conj_re] using hru) hgammaHigh
    rw [Finset.sum_singleton, conjugateSlot_value] at hc
    have hkernel := poleDebit_le_reflected hs hs1
      (show 1 / 2 < (conj u.value).re from hru)
      (show (conj u.value).re < 1 from hu'.2.2.2.1)
      (show 1 - (conj u.value).re ≤ sigma - 1 from hgu) (p.value.im + r.value.im)
    simp only [conj_re, conj_im, sub_neg_eq_add] at hkernel
    by_cases hpair : lwdProduct chi psi = 1
    · have hn := not_lt_of_ge (hhigh hpair)
      simp only [hpair, if_true, poleDebit, if_neg hn, sub_zero]
      rw [hpair] at hc
      simp only [poleDebit, if_pos ht] at hkernel
      simp only [if_pos ht]
      linarith
    · simp only [if_neg hpair, sub_zero]
      linarith
  · have hb := pair_cost chi psi hd he hq hs hs1 hp.2.2.2.2 hr.2.2.2.2
      hp.2.2.2.1 hr.2.2.2.1 hgp hgr hgammaHigh hgammaLow
    have hn : 0 ≤ (if lwdProduct chi psi = 1 then (0.0602 : ℝ) else 0) := by
      split_ifs <;> norm_num
    simp only [poleDebit, if_neg ht, add_zero]
    unfold poleDebit at hb
    linarith

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountedTriples
