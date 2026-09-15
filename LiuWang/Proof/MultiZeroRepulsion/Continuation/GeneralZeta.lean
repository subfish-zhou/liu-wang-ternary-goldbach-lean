import LiuWang.Proof.MultiZeroRepulsion.Continuation.GeneralPrincipal

/-! Payment of both zeta product poles using actual reflected multiplicity kernels. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.MultiZeroRepulsion.Continuation

theorem general_zeta_mother {x alpha sigma : ℝ} (hx : 8000000000 ≤ x)
    (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (ha : 1 / 2 ≤ alpha)
    (p r : ZeroSlots 1 alpha (x / 1)) (hp : p.character = 1) (hr : r.character = 1)
    (hne : p ≠ r) (hnc : p ≠ conjugateSlot r)
    (hgp : 1 - p.value.re ≤ sigma - 1) (hgr : 1 - r.value.re ≤ sigma - 1) :
    1 / (sigma - p.value.re) + 1 / (sigma - r.value.re) ≤
      1 / (sigma - 1) + 3 * stechkinConductorCoeff * Real.log x := by
  have hh := general_zeta_pair_function hs hs1 ha p r hp hr hne hnc
  have hz := mem_strictZeroValues.mp p.zero_mem
  have hw := mem_strictZeroValues.mp r.zero_mem
  have hq : ((1 : ℕ) : ℝ) ≤ x := by norm_num; linarith
  have htp : |p.value.im| ≤ x / (1 : ℕ) := by simpa using hz.2.2.2.2
  have htr : |r.value.im| ≤ x / (1 : ℕ) := by simpa using hw.2.2.2.2
  have hlp := conductor_height_log_max_le (q := 1) hq htp
  have hlr := conductor_height_log_max_le (q := 1) hq htr
  have hls := paired_height_logs (q := 1) hq htp htr
  simp only [Nat.cast_one, Real.log_one, zero_add] at hlp hlr hls
  have hpi := LiuWang.Proof.ChebyshevBound.HighHeight.log_pi_ge_one
  have htwo := Real.log_two_lt_d9
  have hk0 := stechkinK_ge
  have hk : 11 / 40 ≤ stechkinConductorCoeff := by
    unfold stechkinConductorCoeff
    linarith [stechkinK_le]
  by_cases hhigh : 1 ≤ |p.value.im + r.value.im| ∧ 1 ≤ |p.value.im - r.value.im|
  · have hplus := poleDifference_high_nonpos hs hs1 hhigh.1
    have hminus := poleDifference_high_nonpos hs hs1 hhigh.2
    have kp : 0 ≤ reflectedKernel sigma p.value.im r.value :=
      dampedZeroKernel_pair_nonneg hs _ ⟨hw.2.1.le, hw.2.2.2.1.le⟩
    have kp' : 0 ≤ reflectedKernel sigma p.value.im (conj r.value) :=
      dampedZeroKernel_pair_nonneg hs _ ⟨hw.2.1.le, hw.2.2.2.1.le⟩
    have kr : 0 ≤ reflectedKernel sigma r.value.im p.value :=
      dampedZeroKernel_pair_nonneg hs _ ⟨hz.2.1.le, hz.2.2.2.1.le⟩
    have kr' : 0 ≤ reflectedKernel sigma r.value.im (conj p.value) :=
      dampedZeroKernel_pair_nonneg hs _ ⟨hz.2.1.le, hz.2.2.2.1.le⟩
    have hlogs : Real.log (max 1 |p.value.im|) + Real.log (max 1 |r.value.im|) +
        (Real.log (max 1 |p.value.im + r.value.im|) +
          Real.log (max 1 |p.value.im - r.value.im|)) / 2 - 3 * Real.log Real.pi ≤
        3 * Real.log x + Real.log 2 - 3 * Real.log Real.pi := by linarith [hls.1, hls.2]
    have hmult := mul_le_mul_of_nonneg_left hlogs conductorCoeff_bounds.1
    have hconst : stechkinConductorCoeff * (Real.log 2 - 3 * Real.log Real.pi) +
        39 / 40 - 11 * stechkinK / 10 ≤ 0 := by nlinarith only [hk, hk0, hpi, htwo]
    nlinarith only [hh, hmult, hconst, hplus, hminus, kp, kp', kr, kr']
  · have hsmall : Real.log (max 1 |p.value.im + r.value.im|) +
        Real.log (max 1 |p.value.im - r.value.im|) ≤ Real.log x + Real.log 2 := by
      by_cases ht : 1 ≤ |p.value.im + r.value.im|
      · have hd : |p.value.im - r.value.im| ≤ 1 := by
          by_contra he
          exact hhigh ⟨ht, (lt_of_not_ge he).le⟩
        rw [max_eq_left hd, Real.log_one, add_zero]
        exact hls.1
      · rw [max_eq_left (lt_of_not_ge ht).le, Real.log_one, zero_add]
        exact hls.2
    have kp := reflectedKernel_half_pole hs ⟨hw.2.1, hw.2.2.2.1⟩ hgr p.value.im
    have kr := reflectedKernel_half_pole hs ⟨hz.2.1, hz.2.2.2.1⟩ hgp r.value.im
    have kp' := reflectedKernel_half_pole (rho := conj r.value) hs ⟨hw.2.1, hw.2.2.2.1⟩ hgr p.value.im
    have kr' := reflectedKernel_half_pole (rho := conj p.value) hs ⟨hz.2.1, hz.2.2.2.1⟩ hgp r.value.im
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
    have hlogs : Real.log (max 1 |p.value.im|) + Real.log (max 1 |r.value.im|) +
        (Real.log (max 1 |p.value.im + r.value.im|) +
          Real.log (max 1 |p.value.im - r.value.im|)) / 2 - 3 * Real.log Real.pi ≤
        (5 / 2) * Real.log x + Real.log 2 / 2 - 3 * Real.log Real.pi := by linarith
    have hmult := mul_le_mul_of_nonneg_left hlogs conductorCoeff_bounds.1
    have hL := source_log_twenty_two hx
    have hconst : stechkinConductorCoeff *
        (Real.log 2 / 2 - 3 * Real.log Real.pi - Real.log x / 2) +
        39 / 40 - 11 * stechkinK / 10 + 2 ≤ 0 := by nlinarith only [hk, hk0, hpi, htwo, hL]
    nlinarith only [hh, hmult, hconst, hplus, hminus, hinv, kp, kp', kr, kr']

theorem general_principal_mother {q : ℕ} [NeZero q] {x alpha sigma : ℝ}
    (hx : 8000000000 ≤ x) (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (ha : 1 / 2 ≤ alpha)
    (p r : ZeroSlots q alpha (x / q)) (hp : p.character = 1) (hr : r.character = 1)
    (hne : p ≠ r) (hnc : p ≠ conjugateSlot r)
    (hgp : 1 - p.value.re ≤ sigma - 1) (hgr : 1 - r.value.re ≤ sigma - 1) :
    1 / (sigma - p.value.re) + 1 / (sigma - r.value.re) ≤
      1 / (sigma - 1) + 3 * stechkinConductorCoeff * Real.log x := by
  have hx0 : 0 ≤ x := by linarith
  let a := general_principal_slot hx0 p hp
  let b := general_principal_slot hx0 r hr
  have hab : a ≠ b := by
    intro he
    have hv := congrArg ZeroSlots.value he
    have hi := congrArg ZeroSlots.index he
    exact hne (zeroSlots_ext (hp.trans hr.symm) hv hi)
  have hac : a ≠ conjugateSlot b := by
    intro he
    have hv := congrArg ZeroSlots.value he
    have hi := congrArg ZeroSlots.index he
    rw [conjugateSlot_value] at hv
    rw [conjugateSlot_index] at hi
    apply hnc
    apply zeroSlots_ext
    · rw [conjugateSlot_character, hp, hr, inv_one]
    · rw [conjugateSlot_value]
      exact hv
    · rw [conjugateSlot_index]
      exact hi
  exact general_zeta_mother hx hs hs1 ha a b rfl rfl hab hac hgp hgr

end LiuWang.Proof.MultiZeroRepulsion.Continuation
