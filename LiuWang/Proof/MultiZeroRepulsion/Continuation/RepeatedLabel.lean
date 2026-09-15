import LiuWang.Proof.MultiZeroRepulsion.Continuation.SlotSelection
import LiuWang.Proof.MultiZeroRepulsion.Continuation.PrimitiveExclusion

/-! A repeated primitive nonquadratic label, retaining the principal difference-height pole. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.MultiZeroRepulsion.Continuation

theorem repeated_label_function {q : ℕ} [NeZero q] {alpha y sigma : ℝ}
    (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (ha : 1 / 2 ≤ alpha)
    (p r : ZeroSlots q alpha y) (hc : p.character = r.character) (hne : p ≠ r)
    (hnp : p.character ≠ 1) (hprim : p.character.IsPrimitive) (hsq : p.character ^ 2 ≠ 1) :
    1 / (sigma - p.value.re) + 1 / (sigma - r.value.re) +
      reflectedKernel sigma p.value.im r.value + reflectedKernel sigma r.value.im p.value ≤
      1 / (sigma - 1) + stechkinConductorCoeff *
        ((5 / 2) * Real.log q + Real.log (max 1 |p.value.im|) +
          Real.log (max 1 |r.value.im|) +
          (Real.log (max 1 |p.value.im + r.value.im|) +
            Real.log (max 1 |p.value.im - r.value.im|)) / 2 - 3 * Real.log Real.pi) +
        49 / 240 - 11 * stechkinK / 60 + poleDifference sigma (p.value.im - r.value.im) / 2 := by
  have hpos := pair_euler_nonneg p.character p.character hs p.value.im r.value.im
  simp only [Fin.sum_univ_succ, pairCoefficients, pairCharacters, pairHeights,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, one_mul,
    mul_inv_cancel] at hpos
  have hp := primitive_two_slots_bound hs hs1 ha p r hc hne hnp hprim p.value.im
  have hr := primitive_two_slots_bound hs hs1 ha p r hc hne hnp hprim r.value.im
  have h0 := principal_real_strong (q := q) hs hs1
  have hmul := imprimitive_level_bound (p.character * p.character)
    (by simpa only [pow_two] using hsq) hs hs1 (p.value.im + r.value.im)
  have hprincipal := principal_all_height (q := q) hs hs1 (p.value.im - r.value.im)
  have hz := mem_strictZeroValues.mp p.zero_mem
  have hw := mem_strictZeroValues.mp r.zero_mem
  have kp := selected_pair_dominates hs ⟨hz.2.1, hz.2.2.2.1⟩
  have kr := selected_pair_dominates hs ⟨hw.2.1, hw.2.2.2.1⟩
  change _ ≤ reflectedKernel sigma p.value.im p.value at kp
  change _ ≤ reflectedKernel sigma r.value.im r.value at kr
  linarith

theorem source_log_twenty_two {x : ℝ} (hx : 8000000000 ≤ x) : 22 ≤ Real.log x := by
  have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2 ^ 32)
    (show (2 : ℝ) ^ 32 ≤ x by norm_num; linarith)
  rw [Real.log_pow] at hh
  norm_num at hh
  linarith [Real.log_two_gt_d9]

theorem repeated_label_global {q : ℕ} [NeZero q] {x alpha sigma : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (ha : 1 / 2 ≤ alpha)
    (p r : ZeroSlots q alpha (x / q)) (hc : p.character = r.character) (hne : p ≠ r)
    (hnp : p.character ≠ 1) (hprim : p.character.IsPrimitive) (hsq : p.character ^ 2 ≠ 1)
    (hgp : 1 - p.value.re ≤ sigma - 1) (hgr : 1 - r.value.re ≤ sigma - 1) :
    1 / (sigma - p.value.re) + 1 / (sigma - r.value.re) ≤
      1 / (sigma - 1) + 3 * stechkinConductorCoeff * Real.log x := by
  have hh := repeated_label_function hs hs1 ha p r hc hne hnp hprim hsq
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
  by_cases hd : 1 ≤ |p.value.im - r.value.im|
  · have hpole := poleDifference_high_nonpos hs hs1 hd
    have kp : 0 ≤ reflectedKernel sigma p.value.im r.value :=
      dampedZeroKernel_pair_nonneg hs _ ⟨hr.2.1.le, hr.2.2.2.1.le⟩
    have kr : 0 ≤ reflectedKernel sigma r.value.im p.value :=
      dampedZeroKernel_pair_nonneg hs _ ⟨hp.2.1.le, hp.2.2.2.1.le⟩
    have hlogs : (5 / 2) * Real.log q + Real.log (max 1 |p.value.im|) +
        Real.log (max 1 |r.value.im|) +
        (Real.log (max 1 |p.value.im + r.value.im|) +
          Real.log (max 1 |p.value.im - r.value.im|)) / 2 - 3 * Real.log Real.pi ≤
        3 * Real.log x + Real.log 2 - 3 * Real.log Real.pi := by linarith [hls.1, hls.2]
    have hmult := mul_le_mul_of_nonneg_left hlogs conductorCoeff_bounds.1
    have hconst : stechkinConductorCoeff * (Real.log 2 - 3 * Real.log Real.pi) +
        49 / 240 - 11 * stechkinK / 60 ≤ 0 := by nlinarith
    nlinarith
  · have hd1 : |p.value.im - r.value.im| ≤ 1 := (lt_of_not_ge hd).le
    rw [max_eq_left hd1, Real.log_one] at hh
    have kp := reflectedKernel_half_pole hs ⟨hr.2.1, hr.2.2.2.1⟩ hgr p.value.im
    have kr := reflectedKernel_half_pole hs ⟨hp.2.1, hp.2.2.2.1⟩ hgp r.value.im
    have he : realKernel (sigma - 1) (r.value.im - p.value.im) =
        realKernel (sigma - 1) (p.value.im - r.value.im) := by
      dsimp [realKernel]
      rw [show (r.value.im - p.value.im) ^ 2 = (p.value.im - r.value.im) ^ 2 by ring]
    rw [he] at kr
    have hpol := poleDifference_le_realKernel hs (p.value.im - r.value.im)
    have hkn := realKernel_nonneg (show 0 ≤ sigma - 1 by linarith)
      (p.value.im - r.value.im)
    have hinv : 1 / sigma ≤ 1 := (div_le_one (by linarith)).mpr hs.le
    have hlogs : (5 / 2) * Real.log q + Real.log (max 1 |p.value.im|) +
        Real.log (max 1 |r.value.im|) +
        (Real.log (max 1 |p.value.im + r.value.im|) + 0) / 2 - 3 * Real.log Real.pi ≤
        (5 / 2) * Real.log x + Real.log 2 / 2 - 3 * Real.log Real.pi := by linarith [hls.1]
    have hmult := mul_le_mul_of_nonneg_left hlogs conductorCoeff_bounds.1
    have hL := source_log_twenty_two hx
    have hconst : stechkinConductorCoeff *
        (Real.log 2 / 2 - 3 * Real.log Real.pi - Real.log x / 2) +
        49 / 240 - 11 * stechkinK / 60 + 2 ≤ 0 := by nlinarith
    nlinarith

end LiuWang.Proof.MultiZeroRepulsion.Continuation
