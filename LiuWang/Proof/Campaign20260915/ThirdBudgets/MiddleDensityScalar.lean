import LiuWang.Proof.Campaign20260915.ThirdBudgets.M5Scalar
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.GaussianPayment

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1
open LiuWang.Proof.SourceRoute.SecondArc.Continuation
  (scaling scaling_bounds original_upper_le_scaling)

namespace LiuWang.Proof.Campaign20260915.ThirdBudgets

def middleDensityKernel (L t : ℝ) : ℝ :=
  t ^ 6 * Real.exp (-t / 2 - 0.478 * (L - 7) / t)

theorem middle_density_phase {L t : ℝ} (hL : 3100 ≤ L)
    (ht : 0 < t) (htu : t ≤ 60 * scaling L) :
    48.64 * scaling L + (t - 60 * scaling L) ^ 2 / (150 * scaling L) ≤
      (2 / 5 : ℝ) * t + 0.478 * (L - 7) / t := by
  have hr := scaling_bounds hL
  have hr0 : 0 < scaling L := by linarith
  have hA : 1478.454 * scaling L ^ 2 ≤ 0.478 * (L - 7) := by
    nlinarith [sq_nonneg (scaling L - 1)]
  have hd := div_le_div_of_nonneg_left (sq_nonneg (t - 60 * scaling L))
    (by positivity : (0 : ℝ) < (5 / 2) * t)
    (by linarith : (5 / 2 : ℝ) * t ≤ 150 * scaling L)
  have hspare : 0.64 * scaling L ≤ (0.478 * (L - 7) - 1440 * scaling L ^ 2) / t := by
    apply (le_div_iff₀ ht).mpr
    have hm := mul_le_mul_of_nonneg_left htu hr0.le
    nlinarith [sq_nonneg (scaling L)]
  calc
    _ ≤ 48.64 * scaling L + (t - 60 * scaling L) ^ 2 / ((5 / 2) * t) :=
      add_le_add le_rfl hd
    _ = (2 / 5 : ℝ) * t + 1440 * scaling L ^ 2 / t + 0.64 * scaling L := by
      field_simp
      ring
    _ ≤ _ := by
      rw [sub_div] at hspare
      linarith only [hspare]

theorem middle_density_kernel_gaussian {L t : ℝ} (hL : 3100 ≤ L)
    (ht : 0 < t) (htu : t ≤ 60 * scaling L) :
    middleDensityKernel L t ≤
      60 ^ 6 * Real.exp (-6 - 48.64 * scaling L) *
        Real.exp (-(1 / (150 * scaling L)) * (t - 60 * scaling L) ^ 2) := by
  have hpow := sixth_power_tangent ht.le
  have hp := middle_density_phase hL ht htu
  unfold middleDensityKernel
  calc
    _ ≤ (60 ^ 6 * Real.exp (t / 10 - 6)) *
        Real.exp (-t / 2 - 0.478 * (L - 7) / t) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = 60 ^ 6 * Real.exp (t / 10 - 6 + (-t / 2 - 0.478 * (L - 7) / t)) := by
      rw [Real.exp_add]
      ring
    _ ≤ _ := by
      rw [mul_assoc, ← Real.exp_add]
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
      simp only [div_eq_mul_inv] at hp ⊢
      nlinarith only [hp]

theorem middle_half_gaussian {r a b : ℝ} (hr : 1 ≤ r)
    (hab : a ≤ b) (hb : b ≤ 60 * r) :
    (∫ t in a..b, Real.exp (-(1 / (150 * r)) * (t - 60 * r) ^ 2)) ≤
      (25 / 2 : ℝ) * r := by
  let B := 1 / (150 * r)
  have hr0 : 0 < r := by linarith
  have hB : 0 < B := by dsimp only [B]; positivity
  have he (t : ℝ) : Real.exp (-B * (t - 60 * r) ^ 2) =
      Real.exp (-B * (60 * r - t) ^ 2) := by congr 1; ring
  change (∫ t in a..b, Real.exp (-B * (t - 60 * r) ^ 2)) ≤ _
  simp_rw [he]
  rw [intervalIntegral.integral_comp_sub_left (f := fun t => Real.exp (-B * t ^ 2))]
  have hhalf : (∫ t in (60 * r - b)..(60 * r - a), Real.exp (-B * t ^ 2)) ≤
      Real.sqrt (Real.pi / B) / 2 := by
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_gaussian_Ioi]
    apply setIntegral_mono_set (integrable_exp_neg_mul_sq hB).integrableOn
      (ae_of_all _ (fun t => (Real.exp_pos _).le))
    exact Filter.Eventually.of_forall (fun t ht => by
      change 0 < t
      linarith [ht.1])
  have hroot : Real.sqrt (Real.pi / B) ≤ 25 * r := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    dsimp only [B]
    simp only [div_eq_mul_inv, one_mul, inv_inv]
    have hp := mul_le_mul_of_nonneg_right Real.pi_lt_four.le hr0.le
    nlinarith [mul_nonneg hr0.le (show 0 ≤ r - 1 by linarith)]
  linarith only [hhalf, hroot]

theorem middle_density_integral_gaussian {L a b : ℝ} (hL : 3100 ≤ L)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ Real.log (10 * Real.pi * L ^ 7)) :
    (∫ t in a..b, middleDensityKernel L t) ≤
      60 ^ 6 * Real.exp (-6 - 48.64 * scaling L) * ((25 / 2 : ℝ) * scaling L) := by
  have hi : IntervalIntegrable (middleDensityKernel L) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro t ht
    have ht0 : t ≠ 0 := (ha.trans_le ht.1).ne'
    unfold middleDensityKernel
    fun_prop
  have hg : Continuous (fun t : ℝ =>
      Real.exp (-(1 / (150 * scaling L)) * (t - 60 * scaling L) ^ 2)) := by fun_prop
  have h := intervalIntegral.integral_mono_on hab hi
    ((hg.const_mul (60 ^ 6 * Real.exp (-6 - 48.64 * scaling L))).intervalIntegrable _ _)
    (fun t ht => middle_density_kernel_gaussian hL (ha.trans_le ht.1)
      ((ht.2.trans hb).trans (original_upper_le_scaling hL)))
  rw [intervalIntegral.integral_const_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (middle_half_gaussian (scaling_bounds hL).1 hab (hb.trans (original_upper_le_scaling hL)))
    (by positivity))

theorem middle_density_fixed_certificate :
    (8 * 7.56 * 3100 * 500000 * 60 ^ 6 * (25 / 2) : ℝ) *
        Real.exp (-54.64) ≤ 0.11002 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
    Real.exp_one_gt_d9.le 54
  rw [← Real.exp_nat_mul] at hp
  norm_num only [Nat.cast_ofNat, mul_one] at hp
  have hs := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.64)
  have h := mul_le_mul hp hs (by norm_num) (Real.exp_pos _).le
  rw [← Real.exp_add] at h
  norm_num only [show (54 : ℝ) + 0.64 = 54.64 by norm_num] at h
  rw [Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  norm_num at h ⊢
  linarith only [h]

theorem middle_density_scalar_paid {L a b : ℝ} (hL : 3100 ≤ L)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ Real.log (10 * Real.pi * L ^ 7)) :
    8 * L * sourceNu (L ^ 6) * 500000 *
        (∫ t in a..b, t ^ 6 * Real.exp (-t / 2 - 0.478 * (L - 7) / t)) ≤
      0.11002 := by
  have hr := scaling_bounds hL
  have hr0 : 0 < scaling L := by linarith
  have hnu0 := (M6Certificate.sourceNu_sixth_bounds hL).1
  have hi := middle_density_integral_gaussian hL ha hab hb
  have hn : sourceNu (L ^ 6) ≤ 7.56 * scaling L ^ 2 := by
    calc
      _ ≤ 7.56 * (L / 3100) := m5_nu_scaling hL
      _ = _ := by nth_rw 1 [hr.2]; ring
  have htail : scaling L ^ 5 * Real.exp (-48.64 * scaling L) ≤ Real.exp (-48.64) := by
    have hp := pow_le_pow_left₀ hr0.le
      (show scaling L ≤ Real.exp (scaling L - 1) by
        linarith [Real.add_one_le_exp (scaling L - 1)]) 5
    rw [← Real.exp_nat_mul] at hp
    have hm := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-48.64 * scaling L)).le
    rw [← Real.exp_add] at hm
    exact hm.trans (Real.exp_le_exp.mpr (by norm_num; linarith))
  have hnon : 0 ≤ ∫ t in a..b, middleDensityKernel L t :=
    intervalIntegral.integral_nonneg hab (fun t _ => by unfold middleDensityKernel; positivity)
  have h := mul_le_mul
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ 8 * L))
      (by norm_num : (0 : ℝ) ≤ 500000)) hi hnon (by positivity)
  have hp := mul_le_mul_of_nonneg_left htail
    (show 0 ≤ (8 * 7.56 * 3100 * 500000 * 60 ^ 6 * (25 / 2) : ℝ) * Real.exp (-6) by positivity)
  change 8 * L * sourceNu (L ^ 6) * 500000 * (∫ t in a..b, middleDensityKernel L t) ≤ _
  calc
    _ ≤ (8 * 7.56 * 3100 * 500000 * 60 ^ 6 * (25 / 2) : ℝ) *
        Real.exp (-54.64) := by
      rw [show -6 - 48.64 * scaling L = -6 + (-48.64 * scaling L) by ring,
        Real.exp_add] at h
      have hid : Real.exp (-54.64 : ℝ) = Real.exp (-6) * Real.exp (-48.64) := by
        rw [← Real.exp_add]
        norm_num
      rw [hid]
      have hscale : 8 * L * (7.56 * scaling L ^ 2) * 500000 =
          (8 * 3100 * 7.56 * 500000) * scaling L ^ 4 := by nth_rw 1 [hr.2]; ring
      rw [hscale] at h
      nlinarith only [h, hp]
    _ ≤ _ := middle_density_fixed_certificate

#print axioms middle_density_scalar_paid

end LiuWang.Proof.Campaign20260915.ThirdBudgets
