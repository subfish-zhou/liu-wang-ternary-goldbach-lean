import LiuWang.Proof.Campaign20260915.ThirdBudgets.MiddleDensityScalar

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1
open LiuWang.Proof.SourceRoute.SecondArc.Continuation
  (scaling scaling_bounds original_upper_le_scaling fixed_exponential_certificate
    exponential_absorbs_scaling)

namespace LiuWang.Proof.Campaign20260915.ThirdBudgets

def middleNearKernel (L t : ℝ) : ℝ :=
  14000 * Real.exp (-t / 2 - 0.2067 * (L - 7) / t) +
    2 * Real.exp (-t / 2 - 0.10367089 * (L - 7) / t)

theorem middle_strip_phase {L t : ℝ} (hL : 3100 ≤ L)
    (ht : 0 < t) (htu : t ≤ 60 * scaling L) :
    35.75 * scaling L + (t - 35.75 * scaling L) ^ 2 / (120 * scaling L) ≤
      t / 2 + 0.2067 * (L - 7) / t := by
  have hr := scaling_bounds hL
  have hr0 : 0 < scaling L := by linarith
  have hA : (35.75 * scaling L) ^ 2 / 2 ≤ 0.2067 * (L - 7) := by
    nlinarith [sq_nonneg (scaling L - 1)]
  have hd := div_le_div_of_nonneg_left (sq_nonneg (t - 35.75 * scaling L))
    (by positivity : 0 < 2 * t) (by linarith : 2 * t ≤ 120 * scaling L)
  calc
    _ ≤ 35.75 * scaling L + (t - 35.75 * scaling L) ^ 2 / (2 * t) :=
      add_le_add le_rfl hd
    _ = t / 2 + ((35.75 * scaling L) ^ 2 / 2) / t := by field_simp; ring
    _ ≤ _ := add_le_add le_rfl (div_le_div_of_nonneg_right hA ht.le)

theorem middle_exp_integrable {L a b d : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => Real.exp (-t / 2 - d * (L - 7) / t)) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  intro t ht
  have ht0 : t ≠ 0 := (ha.trans_le ht.1).ne'
  fun_prop

theorem middle_first_strip_integral {L a b : ℝ} (hL : 3100 ≤ L)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ Real.log (10 * Real.pi * L ^ 7)) :
    (∫ t in a..b, Real.exp (-t / 2 - 0.2067 * (L - 7) / t)) ≤
      20 * scaling L * Real.exp (-35.75 * scaling L) := by
  let B := 1 / (120 * scaling L)
  have hr := scaling_bounds hL
  have hr0 : 0 < scaling L := by linarith
  have hB : 0 < B := by dsimp only [B]; positivity
  have hg : Continuous (fun t : ℝ => Real.exp (-B * (t - 35.75 * scaling L) ^ 2)) := by fun_prop
  have h := intervalIntegral.integral_mono_on hab (middle_exp_integrable (L := L) (d := 0.2067) ha hab)
    ((hg.const_mul (Real.exp (-35.75 * scaling L))).intervalIntegrable _ _) (fun t ht => by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hp := middle_strip_phase hL (ha.trans_le ht.1)
        ((ht.2.trans hb).trans (original_upper_le_scaling hL))
      dsimp only [B]
      simp only [div_eq_mul_inv] at hp ⊢
      nlinarith only [hp])
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_right (f := fun t => Real.exp (-B * t ^ 2))] at h
  have hfull : (∫ t in (a - 35.75 * scaling L)..(b - 35.75 * scaling L),
      Real.exp (-B * t ^ 2)) ≤ Real.sqrt (Real.pi / B) := by
    rw [intervalIntegral.integral_of_le (sub_le_sub_right hab _), ← integral_gaussian]
    exact setIntegral_le_integral (integrable_exp_neg_mul_sq hB)
      (ae_of_all _ (fun _ => (Real.exp_pos _).le))
  have hroot : Real.sqrt (Real.pi / B) ≤ 20 * scaling L := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    dsimp only [B]
    simp only [div_eq_mul_inv, one_mul, inv_inv]
    have hp := mul_le_mul_of_nonneg_right
      (show Real.pi ≤ 10 / 3 by linarith [Real.pi_lt_d2]) hr0.le
    nlinarith [mul_nonneg (sub_nonneg.mpr hr.1) hr0.le]
  exact h.trans ((mul_le_mul_of_nonneg_left (hfull.trans hroot)
    (Real.exp_pos _).le).trans_eq (by ring))

theorem middle_first_strip_scalar {L a b : ℝ} (hL : 3100 ≤ L)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ Real.log (10 * Real.pi * L ^ 7)) :
    112000 * L * sourceNu (L ^ 6) *
      (∫ t in a..b, Real.exp (-t / 2 - 0.2067 * (L - 7) / t)) ≤ 0.000021 := by
  have hr := scaling_bounds hL
  have hr0 : 0 < scaling L := by linarith
  have hn : sourceNu (L ^ 6) ≤ 8 * scaling L ^ 2 := by
    have h := m5_nu_scaling hL
    have he : L / 3100 = scaling L ^ 2 := by linarith [hr.2]
    rw [he] at h
    nlinarith only [h, sq_nonneg (scaling L)]
  have hi := middle_first_strip_integral hL ha hab hb
  have hp := mul_le_mul
    (mul_le_mul_of_nonneg_left hn (show 0 ≤ 112000 * L by positivity)) hi
    (intervalIntegral.integral_nonneg hab (fun _ _ => (Real.exp_pos _).le))
    (by positivity : 0 ≤ 112000 * L * (8 * scaling L ^ 2))
  have he : (112000 * L * (8 * scaling L ^ 2)) *
      (20 * scaling L * Real.exp (-35.75 * scaling L)) =
      (112000 * 3100 * 8 * 20) * (scaling L ^ 5 * Real.exp (-35.75 * scaling L)) := by
    nth_rw 1 [hr.2]
    ring
  rw [he] at hp
  have ht := mul_le_mul_of_nonneg_left (exponential_absorbs_scaling hr.1)
    (by norm_num : (0 : ℝ) ≤ 112000 * 3100 * 8 * 20)
  have hf := mul_le_mul_of_nonneg_left fixed_exponential_certificate
    (by norm_num : (0 : ℝ) ≤ 112000 * 3100 * 8 * 20)
  norm_num at hf
  linarith only [hp, ht, hf]

theorem middle_sparse_phase {L t : ℝ} (hL : 3100 ≤ L) (ht : 0 < t) :
    17.9 * scaling L ≤ t / 4 + 0.10367089 * (L - 7) / t := by
  have hr := scaling_bounds hL
  have hsq := sq_nonneg (t / 4 - (17.9 / 2) * scaling L)
  rw [show t / 4 + 0.10367089 * (L - 7) / t =
    (t ^ 2 / 4 + 0.10367089 * (L - 7)) / t by field_simp]
  apply (le_div_iff₀ ht).mpr
  nlinarith [sq_nonneg (scaling L - 1)]

theorem middle_sparse_affine_integral {C a b : ℝ} (ha : 34 ≤ a) :
    (∫ t in a..b, Real.exp (-t / 4 - C)) ≤ 4 * Real.exp (-8.5 - C) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := a) (b := b) (f := fun t => -4 * Real.exp (-t / 4 - C))
    (f' := fun t => Real.exp (-t / 4 - C))
    (fun t _ => by
      have hd := (((((hasDerivAt_id t).neg).div_const 4).sub_const C).exp.const_mul (-4))
      dsimp only [Pi.neg_apply, id_eq] at hd
      convert! hd using 1
      ring)
    ((by fun_prop : Continuous (fun t : ℝ => Real.exp (-t / 4 - C))).intervalIntegrable _ _)
  rw [h]
  have he := Real.exp_le_exp.mpr (show -a / 4 - C ≤ -8.5 - C by linarith)
  linarith [Real.exp_pos (-b / 4 - C)]

theorem middle_sparse_integral {L a b : ℝ} (hL : 3100 ≤ L)
    (ha : 34 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, Real.exp (-t / 2 - 0.10367089 * (L - 7) / t)) ≤
      4 * Real.exp (-8.5 - 17.9 * scaling L) := by
  have h := intervalIntegral.integral_mono_on hab
    (middle_exp_integrable (L := L) (d := 0.10367089) (show 0 < a by linarith) hab)
    ((by fun_prop : Continuous (fun t : ℝ => Real.exp (-t / 4 - 17.9 * scaling L))).intervalIntegrable _ _)
    (fun t ht => Real.exp_le_exp.mpr (by
      linarith [middle_sparse_phase hL (show 0 < t by linarith [ht.1])]))
  exact h.trans (middle_sparse_affine_integral ha)

theorem middle_sparse_fixed_certificate :
    (64 * 7.56 * 3100 : ℝ) * Real.exp (-26.4) ≤ 0.000006 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
    Real.exp_one_gt_d9.le 26
  rw [← Real.exp_nat_mul] at hp
  norm_num only [Nat.cast_ofNat, mul_one] at hp
  have hs := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.4)
  have h := mul_le_mul hp hs (by norm_num) (Real.exp_pos _).le
  rw [← Real.exp_add] at h
  norm_num only [show (26 : ℝ) + 0.4 = 26.4 by norm_num] at h
  rw [Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  norm_num at h ⊢
  linarith only [h]

theorem middle_sparse_scalar {L a b : ℝ} (hL : 3100 ≤ L)
    (ha : 34 ≤ a) (hab : a ≤ b) :
    16 * L * sourceNu (L ^ 6) *
      (∫ t in a..b, Real.exp (-t / 2 - 0.10367089 * (L - 7) / t)) ≤ 0.000006 := by
  have hr := scaling_bounds hL
  have hr0 : 0 < scaling L := by linarith
  have hn : sourceNu (L ^ 6) ≤ 7.56 * scaling L ^ 2 := by
    have h := m5_nu_scaling hL
    have he : L / 3100 = scaling L ^ 2 := by linarith [hr.2]
    rwa [he] at h
  have hp := mul_le_mul
    (mul_le_mul_of_nonneg_left hn (show 0 ≤ 16 * L by positivity))
    (middle_sparse_integral hL ha hab)
    (intervalIntegral.integral_nonneg hab (fun _ _ => (Real.exp_pos _).le))
    (by positivity : 0 ≤ 16 * L * (7.56 * scaling L ^ 2))
  have htail : scaling L ^ 4 * Real.exp (-17.9 * scaling L) ≤ Real.exp (-17.9) := by
    have h := pow_le_pow_left₀ hr0.le
      (show scaling L ≤ Real.exp (scaling L - 1) by
        linarith [Real.add_one_le_exp (scaling L - 1)]) 4
    rw [← Real.exp_nat_mul] at h
    have h := mul_le_mul_of_nonneg_right h (Real.exp_pos (-17.9 * scaling L)).le
    rw [← Real.exp_add] at h
    exact h.trans (Real.exp_le_exp.mpr (by norm_num; linarith))
  have he : 16 * L * (7.56 * scaling L ^ 2) * (4 * Real.exp (-8.5 - 17.9 * scaling L)) =
      (64 * 7.56 * 3100) * Real.exp (-8.5) * (scaling L ^ 4 * Real.exp (-17.9 * scaling L)) := by
    nth_rw 1 [hr.2]
    rw [show -8.5 - 17.9 * scaling L = -8.5 + (-17.9 * scaling L) by ring, Real.exp_add]
    ring
  rw [he] at hp
  have ht := mul_le_mul_of_nonneg_left htail
    (show 0 ≤ (64 * 7.56 * 3100 : ℝ) * Real.exp (-8.5) by positivity)
  have hid : Real.exp (-8.5 : ℝ) * Real.exp (-17.9) = Real.exp (-26.4) := by
    rw [← Real.exp_add]
    norm_num
  calc
    _ ≤ (64 * 7.56 * 3100 : ℝ) * Real.exp (-8.5) * Real.exp (-17.9) := hp.trans ht
    _ = (64 * 7.56 * 3100 : ℝ) * Real.exp (-26.4) := by rw [mul_assoc, hid]
    _ ≤ _ := middle_sparse_fixed_certificate

theorem middle_near_scalar_paid {L a b : ℝ} (hL : 3100 ≤ L)
    (ha : 34 ≤ a) (hab : a ≤ b) (hb : b ≤ Real.log (10 * Real.pi * L ^ 7)) :
    8 * L * sourceNu (L ^ 6) * (∫ t in a..b, middleNearKernel L t) ≤ 0.00006 := by
  have ha0 : 0 < a := by linarith
  have h1 := middle_first_strip_scalar hL ha0 hab hb
  have h2 := middle_sparse_scalar hL ha hab
  unfold middleNearKernel
  rw [intervalIntegral.integral_add
    ((middle_exp_integrable ha0 hab).const_mul 14000)
    ((middle_exp_integrable ha0 hab).const_mul 2)]
  simp only [intervalIntegral.integral_const_mul]
  nlinarith only [h1, h2]

#print axioms middle_near_scalar_paid

end LiuWang.Proof.Campaign20260915.ThirdBudgets
