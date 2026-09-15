import LiuWang.Proof.Campaign20260915.ThirdBudgets.M5ActualCount

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount hiding heightKernel
open LiuWang.Proof.SourceRoute.ThirdArc
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.ThirdBudgets

def m5LogKernel (L t : ℝ) : ℝ :=
  (33643 + 254231 / t) * t ^ 6 *
    Real.exp (-(14 / 15 : ℝ) * t - 0.478 * L / t)

def m5CountEnvelope (L q y : ℝ) : ℝ :=
  (33643 + 254231 / Real.log (q * y)) * Real.log (q * y) ^ 6 *
    Real.exp ((4 * Real.log (q * y) - Real.log q) / 60 -
      0.478 * L / Real.log (q * y))

theorem m5LogKernel_nonneg {L t : ℝ} (ht : 0 ≤ t) :
    0 ≤ m5LogKernel L t := by unfold m5LogKernel; positivity

theorem m5LogKernel_integrable {L a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (m5LogKernel L) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  intro t ht
  have ht0 : t ≠ 0 := (ha.trans_le ht.1).ne'
  unfold m5LogKernel
  fun_prop

theorem m5_envelope_log_substitution {q u v : ℝ}
    (hq : 0 < q) (hu : 0 < u) (hv : 0 < v) (L : ℝ) :
    (∫ y in u..v, heightKernel 1 y * m5CountEnvelope L q y) =
      q * Real.exp (-Real.log q / 60) *
        ∫ t in Real.log (q * u)..Real.log (q * v), m5LogKernel L t := by
  rw [height_log_substitution hq hu hv]
  simp only [Real.rpow_one, one_mul]
  rw [mul_assoc]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  have he : q * (Real.exp t / q) = Real.exp t := by field_simp
  unfold m5CountEnvelope m5LogKernel
  dsimp only
  rw [he, Real.log_exp]
  have hid : -(1 : ℝ) * t + ((4 * t - Real.log q) / 60 - 0.478 * L / t) =
      -Real.log q / 60 + (-(14 / 15 : ℝ) * t - 0.478 * L / t) := by ring
  calc
    _ = (33643 + 254231 / t) * t ^ 6 *
        (Real.exp (-(1 : ℝ) * t) *
          Real.exp ((4 * t - Real.log q) / 60 - 0.478 * L / t)) := by ring
    _ = _ := by rw [← Real.exp_add, hid, Real.exp_add]; ring

theorem m5_actual_height_integral {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (hdensity : ∀ r ∈ Set.Icc (max (100000 / (q : ℝ)) (10000 * Real.log q)) (sourceT N),
      ∀ alpha ∈ Set.Icc (59 / 60 : ℝ) (sourceCutoff q 0.478 r),
        (familyCount q alpha r : ℝ) ≤ sourceDensity q r alpha) :
    (∫ y in middleHeight N q..sourceT N, heightKernel 1 y *
        countIntegral q N y (59 / 60) (sourceCutoff q 0.478 y)) ≤
      ∫ y in middleHeight N q..sourceT N,
        heightKernel 1 y * m5CountEnvelope (sourceL N) q y := by
  have hh := original_height_order (exp_2000_le_of_exp_3100_le hN) hq1
  have hX : (1 : ℝ) ≤ N := by exact_mod_cast nat_pos_of_exp_le hN
  have hi := heightKernel_mul_integrable (lowHeight_pos.trans_le hh.1) hh.2 1
    (moving_countIntegral_monotone hN hq hX hh.1 hh.2
      (d := 0.478) (by norm_num) le_rfl).intervalIntegrable
  have hc : ContinuousOn (m5CountEnvelope (sourceL N) q)
      (Set.uIcc (middleHeight N q) (sourceT N)) := by
    rw [Set.uIcc_of_le hh.2]
    intro y hy
    have hd := m5_log_domain hN hq1 hy
    have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
    have hy0 : y ≠ 0 := by linarith [hd.1]
    have hprod : (q : ℝ) * y ≠ 0 := mul_ne_zero hq0.ne' hy0
    have hs : Real.log ((q : ℝ) * y) ≠ 0 := by linarith [hd.2.1]
    unfold m5CountEnvelope
    fun_prop
  apply intervalIntegral.integral_mono_on hh.2 hi
    (heightKernel_mul_integrable (lowHeight_pos.trans_le hh.1) hh.2 1 hc.intervalIntegrable)
  intro y hy
  have hd := m5_legal_height_domain hN hq hq1 hy
  have hy0 : 0 ≤ y := (lowHeight_pos.trans_le (hh.1.trans hy.1)).le
  exact mul_le_mul_of_nonneg_left
    (m5_count_bound_all_heights hN hq hq1 hy
      (hdensity (legalHeight q y) ⟨hd.2.1, hd.2.2.1⟩))
    (by unfold heightKernel; positivity)

theorem sourceM5_same_modulus_legal {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (hdensity : ∀ r ∈ Set.Icc (max (100000 / (q : ℝ)) (10000 * Real.log q)) (sourceT N),
      ∀ alpha ∈ Set.Icc (59 / 60 : ℝ) (sourceCutoff q 0.478 r),
        (familyCount q alpha r : ℝ) ≤ sourceDensity q r alpha) :
    sourceM5 N q ≤
      (5 * N * ((q : ℝ) / q.totient) * Real.exp ((29 / 60 : ℝ) * Real.log q)) *
        ∫ t in Real.log (10 * Real.pi * sourceL N ^ 7)..
          Real.log ((q : ℝ) * sourceT N), m5LogKernel (sourceL N) t := by
  have hh := original_height_order (exp_2000_le_of_exp_3100_le hN) hq1
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have h := m5_actual_height_integral hN hq hq1 hdensity
  rw [m5_envelope_log_substitution hq0 (lowHeight_pos.trans_le hh.1)
    (lowHeight_pos.trans_le (hh.1.trans hh.2))] at h
  have he : (q : ℝ) * middleHeight N q = 10 * Real.pi * sourceL N ^ 7 := by
    unfold middleHeight
    field_simp
  simp only [heightKernel, one_mul, show -(1 : ℝ) - 1 = -2 by norm_num, he] at h
  have hs := mul_le_mul_of_nonneg_left h
    (show 0 ≤ 5 * N * Real.sqrt q / q.totient by positivity)
  change sourceM5 N q ≤ _ at hs
  have hid : Real.sqrt q * Real.exp (-Real.log q / 60) =
      Real.exp ((29 / 60 : ℝ) * Real.log q) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hq0, ← Real.exp_add]
    congr 1
    ring
  convert hs using 1
  rw [← hid]
  ring

theorem sourceM5_original_scalar_transfer {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (hdensity : ∀ r ∈ Set.Icc (max (100000 / (q : ℝ)) (10000 * Real.log q)) (sourceT N),
      ∀ alpha ∈ Set.Icc (59 / 60 : ℝ) (sourceCutoff q 0.478 r),
        (familyCount q alpha r : ℝ) ≤ sourceDensity q r alpha)
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q)
    (hnu : sourceNu q ≤ sourceNu (sourceL N ^ 6)) :
    sourceM5 N q ≤ (N : ℝ) / sourceL N *
      (5 * sourceL N ^ (39 / 10 : ℝ) * sourceNu (sourceL N ^ 6) *
        ∫ t in Real.log (10 * Real.pi * sourceL N ^ 7)..Real.log (sourceL N ^ 21),
          (33643 + 254231 / t) * t ^ 6 *
            Real.exp (-(14 / 15 : ℝ) * t - 0.478 * sourceL N / t)) := by
  have hL0 := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  have hh := original_height_order (exp_2000_le_of_exp_3100_le hN) hq1
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hT0 : 0 < sourceT N := pow_pos hL0 15
  have he : (q : ℝ) * middleHeight N q = 10 * Real.pi * sourceL N ^ 7 := by
    unfold middleHeight
    field_simp
  have hab : Real.log (10 * Real.pi * sourceL N ^ 7) ≤
      Real.log ((q : ℝ) * sourceT N) := m5_product_lower hN hh.2
  have hbd : Real.log ((q : ℝ) * sourceT N) ≤ Real.log (sourceL N ^ 21) := by
    apply Real.log_le_log (mul_pos hq0 hT0)
    calc
      _ ≤ sourceL N ^ 6 * sourceL N ^ 15 :=
        mul_le_mul_of_nonneg_right hq1 hT0.le
      _ = _ := by ring
  have ha : 0 < Real.log (10 * Real.pi * sourceL N ^ 7) := by
    rw [← he]
    linarith [(m5_log_domain hN hq1 ⟨le_rfl, hh.2⟩).2.1]
  have hi := intervalIntegral.integral_mono_interval le_rfl hab hbd
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht =>
      m5LogKernel_nonneg (L := sourceL N) (ha.le.trans ht.1.le)))
    (m5LogKernel_integrable ha (hab.trans hbd))
  have hnu0 : 0 ≤ sourceNu (sourceL N ^ 6) :=
    (div_nonneg hq0.le (Nat.cast_nonneg _)).trans (htotient.trans hnu)
  have hqlog := Real.log_le_log hq0 hq1
  rw [sourceP1, Real.log_pow] at hqlog
  simp only [Nat.cast_ofNat] at hqlog
  have hpow : Real.exp ((29 / 60 : ℝ) * Real.log q) ≤
      sourceL N ^ (29 / 10 : ℝ) := by
    rw [Real.rpow_def_of_pos hL0]
    apply Real.exp_le_exp.mpr
    linarith
  have hc : 5 * N * ((q : ℝ) / q.totient) * Real.exp ((29 / 60 : ℝ) * Real.log q) ≤
      5 * N * sourceNu (sourceL N ^ 6) * sourceL N ^ (29 / 10 : ℝ) := by
    have h := mul_le_mul (htotient.trans hnu) hpow (Real.exp_pos _).le hnu0
    nlinarith only [mul_le_mul_of_nonneg_left h (show 0 ≤ 5 * (N : ℝ) by positivity)]
  have hi0 : 0 ≤ ∫ t in Real.log (10 * Real.pi * sourceL N ^ 7)..
      Real.log ((q : ℝ) * sourceT N), m5LogKernel (sourceL N) t :=
    intervalIntegral.integral_nonneg hab (fun t ht => m5LogKernel_nonneg (ha.le.trans ht.1))
  have hid : sourceL N ^ (39 / 10 : ℝ) = sourceL N ^ (29 / 10 : ℝ) * sourceL N := by
    rw [show (39 / 10 : ℝ) = 29 / 10 + 1 by norm_num, Real.rpow_add_one hL0.ne']
  calc
    _ ≤ _ := sourceM5_same_modulus_legal hN hq hq1 hdensity
    _ ≤ (5 * N * sourceNu (sourceL N ^ 6) * sourceL N ^ (29 / 10 : ℝ)) *
        ∫ t in Real.log (10 * Real.pi * sourceL N ^ 7)..
          Real.log (sourceL N ^ 21), m5LogKernel (sourceL N) t :=
      mul_le_mul hc hi hi0 (by positivity)
    _ = _ := by
      change _ = (N : ℝ) / sourceL N *
        (5 * sourceL N ^ (39 / 10 : ℝ) * sourceNu (sourceL N ^ 6) *
          ∫ t in Real.log (10 * Real.pi * sourceL N ^ 7)..Real.log (sourceL N ^ 21),
            m5LogKernel (sourceL N) t)
      rw [hid]
      field_simp

theorem sourceM5_original_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (hdensity : ∀ r ∈ Set.Icc (max (100000 / (q : ℝ)) (10000 * Real.log q)) (sourceT N),
      ∀ alpha ∈ Set.Icc (59 / 60 : ℝ) (sourceCutoff q 0.478 r),
        (familyCount q alpha r : ℝ) ≤ sourceDensity q r alpha)
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q)
    (hnu : sourceNu q ≤ sourceNu (sourceL N ^ 6)) :
    sourceM5 N q ≤ 0.00007 * (N : ℝ) / sourceL N := by
  have h := sourceM5_original_scalar_transfer hN hq hq1 hdensity htotient hnu
  have hp := mul_le_mul_of_nonneg_left
    (original_m5_scalar_paid (sourceL_ge_3100 hN))
    (div_nonneg (Nat.cast_nonneg N) (sourceL_pos (exp_2000_le_of_exp_3100_le hN)).le)
  exact h.trans (by simpa only [div_mul_eq_mul_div, mul_comm (N : ℝ)] using hp)

#print sourceM5_original_paid
#print axioms sourceM5_original_scalar_transfer
#print axioms sourceM5_original_paid

end LiuWang.Proof.Campaign20260915.ThirdBudgets
