import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Kernel

/-! # All-real-L reduction, with a certified full tail and unchanged core integrand -/

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment

def lowerHeight (L : ℝ) : ℝ := Real.log (3.36 * L ^ (3 : ℕ))

def upperHeight (L : ℝ) : ℝ := Real.log (L ^ (18 : ℕ))

theorem lowerHeight_eq {L : ℝ} (hL : 0 < L) :
    lowerHeight L = Real.log 3.36 + 3 * Real.log L := by
  rw [lowerHeight, Real.log_mul (by norm_num) (pow_pos hL _).ne', Real.log_pow]
  norm_num

theorem original_height_bounds {L : ℝ} (hL : 3100 ≤ L) :
    0 < lowerHeight 3100 ∧ lowerHeight 3100 ≤ 100 ∧
      lowerHeight 3100 ≤ lowerHeight L ∧
      lowerHeight L ≤ upperHeight L ∧ 100 ≤ upperHeight L := by
  have h0 : 0 < L := by linarith
  have hlo := (original_log_linear hL).1
  have hc0 : 0 ≤ Real.log (3.36 : ℝ) := Real.log_nonneg (by norm_num)
  have hc := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3.36)
  have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 3100) hL
  rw [lowerHeight_eq (by norm_num), lowerHeight_eq h0, upperHeight, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  exact ⟨by linarith [log_3100_bounds.1], by linarith [log_3100_bounds.2],
    by linarith, by linarith, by linarith⟩

theorem sourceIntegrand_nonneg {L s : ℝ} (hL : 0 < L) (hs : 0 < s) :
    0 ≤ sourceIntegrand L s :=
  mul_nonneg (by positivity : 0 ≤ L ^ (4 : ℕ) * Real.exp (-s))
    (source31Profile_nonneg hL hs)

theorem sourceIntegrand_integrable (L : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (sourceIntegrand L) volume a b := by
  unfold sourceIntegrand
  simpa only [mul_assoc] using
    (source31_log_integrand_integrable L ha hab).const_mul (L ^ (4 : ℕ))

def tailPrimitive (s : ℝ) : ℝ :=
  -(s ^ (4 : ℕ) + 4 * s ^ (3 : ℕ) + 12 * s ^ (2 : ℕ) + 24 * s + 24) *
    Real.exp (-s)

theorem tailPrimitive_hasDerivAt (s : ℝ) :
    HasDerivAt tailPrimitive (s ^ (4 : ℕ) * Real.exp (-s)) s := by
  have hp : HasDerivAt
      (fun x : ℝ => -(x ^ (4 : ℕ) + 4 * x ^ (3 : ℕ) + 12 * x ^ (2 : ℕ) + 24 * x + 24))
      (-(4 * s ^ (3 : ℕ) + 12 * s ^ (2 : ℕ) + 24 * s + 24)) s := by
    convert! (((((hasDerivAt_id s).pow 4).add
      (((hasDerivAt_id s).pow 3).const_mul 4)).add
      (((hasDerivAt_id s).pow 2).const_mul 12)).add
      ((hasDerivAt_id s).const_mul 24)).add_const 24 |>.neg using 1
    simp only [id_eq]
    ring
  have he := ((hasDerivAt_id s).neg.exp)
  convert! hp.mul he using 1
  simp only [Pi.neg_apply, id_eq]
  ring

theorem polynomial_tail_bound {b : ℝ} (hb : 100 ≤ b) :
    (∫ s in (100 : ℝ)..b, 1400000 * s ^ (4 : ℕ) * Real.exp (-s)) ≤
      1 / 1000000000000000000000000000 := by
  have hi : IntervalIntegrable (fun s : ℝ => s ^ (4 : ℕ) * Real.exp (-s))
      volume 100 b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => tailPrimitive_hasDerivAt s) hi
  have hb0 : 0 ≤ b := by linarith
  have ht : tailPrimitive b ≤ 0 := by
    unfold tailPrimitive
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (Real.exp_pos _).le
  have hex : (27 / 10 : ℝ) ^ (100 : ℕ) ≤ Real.exp 100 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 27 / 10)
      ((by norm_num : (27 / 10 : ℝ) ≤ 2.7182818283).trans Real.exp_one_gt_d9.le) 100
    simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, mul_one] using h
  have hnum : (1400000 : ℝ) * (100 ^ (4 : ℕ) + 4 * 100 ^ (3 : ℕ) +
      12 * 100 ^ (2 : ℕ) + 24 * 100 + 24) ≤
      (1 / 1000000000000000000000000000 : ℝ) * (27 / 10) ^ (100 : ℕ) := by norm_num
  simp_rw [mul_assoc, intervalIntegral.integral_const_mul]
  rw [he]
  have hc : -(1400000 : ℝ) * tailPrimitive 100 ≤
      1 / 1000000000000000000000000000 := by
    unfold tailPrimitive
    rw [Real.exp_neg]
    have hh := (div_le_iff₀ (Real.exp_pos 100)).mpr
      (hnum.trans (mul_le_mul_of_nonneg_left hex (by norm_num)))
    simpa only [div_eq_mul_inv, mul_assoc, mul_neg, neg_mul, neg_neg] using hh
  linarith

theorem source_tail_bound {L b : ℝ} (hL : 0 < L) (hb : 100 ≤ b) :
    (∫ s in (100 : ℝ)..b, sourceIntegrand L s) ≤
      1 / 1000000000000000000000000000 := by
  have hi : IntervalIntegrable
      (fun s : ℝ => 1400000 * s ^ (4 : ℕ) * Real.exp (-s)) volume 100 b := by
    apply Continuous.intervalIntegrable
    fun_prop
  exact (intervalIntegral.integral_mono_on hb
    (sourceIntegrand_integrable L (by norm_num) hb) hi (fun s hs =>
      sourceIntegrand_le_polynomial hL (by linarith [hs.1]))).trans (polynomial_tail_bound hb)

theorem base_core_nonneg :
    0 ≤ ∫ s in lowerHeight 3100..(100 : ℝ), sourceIntegrand 3100 s := by
  have hb := original_height_bounds (L := 3100) le_rfl
  exact intervalIntegral.integral_nonneg hb.2.1 (fun s hs =>
    sourceIntegrand_nonneg (by norm_num) (hb.1.trans_le hs.1))

theorem uniform_source31_reduction {L : ℝ} (hL : 3100 ≤ L) :
    (∫ s in lowerHeight L..upperHeight L, sourceIntegrand L s) ≤
      (∫ s in lowerHeight 3100..(100 : ℝ), sourceIntegrand 3100 s) +
        1 / 1000000000000000000000000000 := by
  have hb := original_height_bounds hL
  have h0 : 0 < L := by linarith
  have ha0 := hb.1.trans_le hb.2.2.1
  by_cases ha : lowerHeight L ≤ 100
  · rw [← intervalIntegral.integral_add_adjacent_intervals
      (sourceIntegrand_integrable L ha0 ha)
      (sourceIntegrand_integrable L (by norm_num) hb.2.2.2.2)]
    have hcore := intervalIntegral.integral_mono_on ha
      (sourceIntegrand_integrable L ha0 ha)
      (sourceIntegrand_integrable 3100 ha0 ha)
      (fun s hs => sourceIntegrand_le_base hL (ha0.trans_le hs.1) hs.2)
    have hext := intervalIntegral.integral_mono_interval hb.2.2.1 ha le_rfl
      (ae_restrict_of_forall_mem measurableSet_Ioc (fun s hs =>
        sourceIntegrand_nonneg (by norm_num) (hb.1.trans hs.1)))
      (sourceIntegrand_integrable 3100 hb.1 hb.2.1)
    exact add_le_add (hcore.trans hext) (source_tail_bound h0 hb.2.2.2.2)
  · have ha' : 100 ≤ lowerHeight L := le_of_not_ge ha
    have hext := intervalIntegral.integral_mono_interval ha' hb.2.2.2.1 le_rfl
      (ae_restrict_of_forall_mem measurableSet_Ioc (fun s hs =>
        sourceIntegrand_nonneg h0 (by linarith [hs.1])))
      (sourceIntegrand_integrable L (by norm_num) hb.2.2.2.2)
    exact (hext.trans (source_tail_bound h0 hb.2.2.2.2)).trans
      (le_add_of_nonneg_left base_core_nonneg)

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment
