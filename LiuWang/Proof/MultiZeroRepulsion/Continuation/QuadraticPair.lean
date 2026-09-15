import LiuWang.Proof.MultiZeroRepulsion.Continuation.NonquadraticCount

/-! Both principal-product poles for a quadratic character, with conjugate slots retained. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.MultiZeroRepulsion.Continuation

theorem quadratic_label_function {q : ℕ} [NeZero q] {alpha y sigma : ℝ}
    (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (ha : 1 / 2 ≤ alpha)
    (p r : ZeroSlots q alpha y) (hc : p.character = r.character) (hne : p ≠ r)
    (hnc : p ≠ conjugateSlot r) (hnp : p.character ≠ 1) (hprim : p.character.IsPrimitive)
    (hsq : p.character ^ 2 = 1) :
    1 / (sigma - p.value.re) + 1 / (sigma - r.value.re) +
      (reflectedKernel sigma p.value.im r.value +
        reflectedKernel sigma p.value.im (conj r.value) +
        reflectedKernel sigma r.value.im p.value +
        reflectedKernel sigma r.value.im (conj p.value)) / 2 ≤
      1 / (sigma - 1) + stechkinConductorCoeff *
        (2 * Real.log q + Real.log (max 1 |p.value.im|) + Real.log (max 1 |r.value.im|) +
          (Real.log (max 1 |p.value.im + r.value.im|) +
            Real.log (max 1 |p.value.im - r.value.im|)) / 2 - 3 * Real.log Real.pi) +
        43 / 120 - 11 * stechkinK / 30 +
        (poleDifference sigma (p.value.im + r.value.im) +
          poleDifference sigma (p.value.im - r.value.im)) / 2 := by
  have hprod : p.character * p.character = 1 := by simpa only [pow_two] using hsq
  have hinv : p.character⁻¹ = p.character := ((mul_eq_one_iff_eq_inv).mp hprod).symm
  have hcr : p.character = (conjugateSlot r).character := by
    rw [conjugateSlot_character, ← hc, hinv]
  have hcp : r.character = (conjugateSlot p).character := by
    rw [conjugateSlot_character, hinv, hc]
  have hnc' : r ≠ conjugateSlot p := by
    intro he
    apply hnc
    have hh := congrArg conjugateSlot he
    rw [conjugateSlot_involutive] at hh
    exact hh.symm
  have hp := primitive_two_slots_bound hs hs1 ha p r hc hne hnp hprim p.value.im
  have hp' := primitive_two_slots_bound hs hs1 ha p (conjugateSlot r) hcr hnc hnp hprim p.value.im
  have hr := primitive_two_slots_bound hs hs1 ha p r hc hne hnp hprim r.value.im
  have hr' := primitive_two_slots_bound hs hs1 ha r (conjugateSlot p) hcp hnc'
    (hc ▸ hnp) (hc ▸ hprim) r.value.im
  rw [conjugateSlot_value] at hp' hr'
  rw [← hc] at hr'
  have hpos := pair_euler_nonneg p.character p.character hs p.value.im r.value.im
  simp only [Fin.sum_univ_succ, pairCoefficients, pairCharacters, pairHeights,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, one_mul,
    mul_inv_cancel, hprod] at hpos
  have h0 := principal_real_strong (q := q) hs hs1
  have hplus := principal_all_height (q := q) hs hs1 (p.value.im + r.value.im)
  have hminus := principal_all_height (q := q) hs hs1 (p.value.im - r.value.im)
  have hz := mem_strictZeroValues.mp p.zero_mem
  have hw := mem_strictZeroValues.mp r.zero_mem
  have kp := selected_pair_dominates hs ⟨hz.2.1, hz.2.2.2.1⟩
  have kr := selected_pair_dominates hs ⟨hw.2.1, hw.2.2.2.1⟩
  change _ ≤ reflectedKernel sigma p.value.im p.value at kp
  change _ ≤ reflectedKernel sigma r.value.im r.value at kr
  linarith

theorem quadratic_label_global {q : ℕ} [NeZero q] {x alpha sigma : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (ha : 1 / 2 ≤ alpha)
    (p r : ZeroSlots q alpha (x / q)) (hc : p.character = r.character) (hne : p ≠ r)
    (hnc : p ≠ conjugateSlot r) (hnp : p.character ≠ 1)
    (hprim : p.character.IsPrimitive) (hsq : p.character ^ 2 = 1)
    (hgp : 1 - p.value.re ≤ sigma - 1) (hgr : 1 - r.value.re ≤ sigma - 1) :
    1 / (sigma - p.value.re) + 1 / (sigma - r.value.re) ≤
      1 / (sigma - 1) + 3 * stechkinConductorCoeff * Real.log x := by
  have hh := quadratic_label_function hs hs1 ha p r hc hne hnc hnp hprim hsq
  have hp := mem_strictZeroValues.mp p.zero_mem
  have hr := mem_strictZeroValues.mp r.zero_mem
  have hlp := conductor_height_log_max_le hq hp.2.2.2.2
  have hlr := conductor_height_log_max_le hq hr.2.2.2.2
  have hls := paired_height_logs hq hp.2.2.2.2 hr.2.2.2.2
  have hq0 := Real.log_natCast_nonneg q
  have hpi := LiuWang.Proof.ChebyshevBound.HighHeight.log_pi_ge_one
  have htwo := Real.log_two_lt_d9
  have hk0 := stechkinK_mem.1
  have hk : 11 / 40 ≤ stechkinConductorCoeff := by
    dsimp [stechkinConductorCoeff]
    linarith [stechkinK_le]
  by_cases hhigh : 1 ≤ |p.value.im + r.value.im| ∧ 1 ≤ |p.value.im - r.value.im|
  · have hplus := poleDifference_high_nonpos hs hs1 hhigh.1
    have hminus := poleDifference_high_nonpos hs hs1 hhigh.2
    have kp : 0 ≤ reflectedKernel sigma p.value.im r.value :=
      dampedZeroKernel_pair_nonneg hs _ ⟨hr.2.1.le, hr.2.2.2.1.le⟩
    have kp' : 0 ≤ reflectedKernel sigma p.value.im (conj r.value) :=
      dampedZeroKernel_pair_nonneg hs _ ⟨hr.2.1.le, hr.2.2.2.1.le⟩
    have kr : 0 ≤ reflectedKernel sigma r.value.im p.value :=
      dampedZeroKernel_pair_nonneg hs _ ⟨hp.2.1.le, hp.2.2.2.1.le⟩
    have kr' : 0 ≤ reflectedKernel sigma r.value.im (conj p.value) :=
      dampedZeroKernel_pair_nonneg hs _ ⟨hp.2.1.le, hp.2.2.2.1.le⟩
    have hlogs : 2 * Real.log q + Real.log (max 1 |p.value.im|) +
        Real.log (max 1 |r.value.im|) +
        (Real.log (max 1 |p.value.im + r.value.im|) +
          Real.log (max 1 |p.value.im - r.value.im|)) / 2 - 3 * Real.log Real.pi ≤
        3 * Real.log x + Real.log 2 - 3 * Real.log Real.pi := by linarith [hls.1, hls.2]
    have hmult := mul_le_mul_of_nonneg_left hlogs conductorCoeff_bounds.1
    have hconst : stechkinConductorCoeff * (Real.log 2 - 3 * Real.log Real.pi) +
        43 / 120 - 11 * stechkinK / 30 ≤ 0 := by nlinarith only [hk, hk0, hpi, htwo]
    nlinarith only [hh, hmult, hconst, hplus, hminus, kp, kp', kr, kr']
  · have hsmall : Real.log (max 1 |p.value.im + r.value.im|) +
        Real.log (max 1 |p.value.im - r.value.im|) ≤ Real.log x + Real.log 2 - Real.log q := by
      by_cases ht : 1 ≤ |p.value.im + r.value.im|
      · have hd : |p.value.im - r.value.im| ≤ 1 := by
          by_contra he
          exact hhigh ⟨ht, (lt_of_not_ge he).le⟩
        rw [max_eq_left hd, Real.log_one, add_zero]
        linarith [hls.1]
      · rw [max_eq_left (lt_of_not_ge ht).le, Real.log_one, zero_add]
        linarith [hls.2]
    have kp := reflectedKernel_half_pole hs ⟨hr.2.1, hr.2.2.2.1⟩ hgr p.value.im
    have kr := reflectedKernel_half_pole hs ⟨hp.2.1, hp.2.2.2.1⟩ hgp r.value.im
    have kp' := reflectedKernel_half_pole (rho := conj r.value) hs ⟨hr.2.1, hr.2.2.2.1⟩ hgr p.value.im
    have kr' := reflectedKernel_half_pole (rho := conj p.value) hs ⟨hp.2.1, hp.2.2.2.1⟩ hgp r.value.im
    simp only [conj_im, sub_neg_eq_add] at kp' kr'
    rw [add_comm r.value.im p.value.im] at kr'
    have he : realKernel (sigma - 1) (r.value.im - p.value.im) =
        realKernel (sigma - 1) (p.value.im - r.value.im) := by
      dsimp [realKernel]
      rw [show (r.value.im - p.value.im) ^ 2 = (p.value.im - r.value.im) ^ 2 by ring]
    rw [he] at kr
    have hplus := poleDifference_le_realKernel hs (p.value.im + r.value.im)
    have hminus := poleDifference_le_realKernel hs (p.value.im - r.value.im)
    have hinv : 1 / sigma ≤ 1 := (div_le_one (by linarith)).mpr hs.le
    have hlogs : 2 * Real.log q + Real.log (max 1 |p.value.im|) +
        Real.log (max 1 |r.value.im|) +
        (Real.log (max 1 |p.value.im + r.value.im|) +
          Real.log (max 1 |p.value.im - r.value.im|)) / 2 - 3 * Real.log Real.pi ≤
        (5 / 2) * Real.log x + Real.log 2 / 2 - 3 * Real.log Real.pi := by linarith
    have hmult := mul_le_mul_of_nonneg_left hlogs conductorCoeff_bounds.1
    have hL := source_log_twenty_two hx
    have hconst : stechkinConductorCoeff *
        (Real.log 2 / 2 - 3 * Real.log Real.pi - Real.log x / 2) +
        43 / 120 - 11 * stechkinK / 30 + 2 ≤ 0 := by nlinarith only [hk, hk0, hpi, htwo, hL]
    nlinarith only [hh, hmult, hconst, hplus, hminus, hinv, kp, kp', kr, kr']

end LiuWang.Proof.MultiZeroRepulsion.Continuation
