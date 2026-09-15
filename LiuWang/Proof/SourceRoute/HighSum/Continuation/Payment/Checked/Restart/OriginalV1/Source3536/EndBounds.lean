import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536.LocalPayment

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536

def expKernel (A s : ℝ) : ℝ := (3100 : ℝ) ^ 4 * Real.exp (phase A s)

theorem expKernel_integrable (A : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (expKernel A) volume a b :=
  (exp_phase_integrable A ha hab).const_mul (3100 ^ 4)

theorem exponential_tail {A u v : ℝ} (hA : 0 ≤ A) (hu : 0 < u) (huv : u ≤ v)
    (hslope : A / u ^ 2 ≤ 1 / 4) :
    (∫ s in u..v, expKernel A s) ≤ (3100 : ℝ) ^ 4 * (4 / 3) * Real.exp (phase A u) := by
  have hpoint (s : ℝ) (hs : s ∈ Set.Icc u v) :
      phase A s ≤ phase A u - (3 / 4) * (s - u) := by
    have hh := phase_le_tangent hA hu (hu.trans_le hs.1)
    have hm := mul_le_mul_of_nonneg_right hslope (sub_nonneg.mpr hs.1)
    unfold tangent at hh
    linarith
  have hi : IntervalIntegrable (fun s => Real.exp (phase A u - (3 / 4) * (s - u)))
      volume u v := by apply Continuous.intervalIntegrable; fun_prop
  have hd (s : ℝ) : HasDerivAt
      (fun s => -(4 / 3) * Real.exp (phase A u - (3 / 4) * (s - u)))
      (Real.exp (phase A u - (3 / 4) * (s - u))) s := by
    convert! (((((hasDerivAt_id s).sub_const u).const_mul (3 / 4)).const_sub
      (phase A u)).exp.const_mul (-(4 / 3))) using 1
    simp only [id_eq]
    ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) hi
  have hb : (∫ s in u..v, Real.exp (phase A s)) ≤ (4 / 3) * Real.exp (phase A u) := by
    have hh := intervalIntegral.integral_mono_on huv (exp_phase_integrable A hu huv)
      hi (fun s hs => Real.exp_le_exp.mpr (hpoint s hs))
    rw [he, sub_self, mul_zero, sub_zero] at hh
    linarith [Real.exp_pos (phase A u - (3 / 4) * (v - u))]
  unfold expKernel
  rw [intervalIntegral.integral_const_mul]
  exact (mul_le_mul_of_nonneg_left hb (by norm_num)).trans_eq (by ring)

theorem first_tail :
    (∫ s in ((start : ℝ) + 16)..(60 : ℝ), expKernel firstA s) ≤ 1 / 10000000 := by
  have hh := exponential_tail (A := (firstA : ℝ)) (u := (start : ℝ) + 16) (v := 60)
    (by norm_num [firstA]) (by norm_num [start]) (by norm_num [start])
    (by norm_num [firstA, start])
  have he := exp_upper (x := (start + 16) + firstA / (start + 16)) (by norm_num [start, firstA])
  have hp : phase (firstA : ℝ) ((start : ℝ) + 16) =
      -(((start + 16) + firstA / (start + 16) : ℚ) : ℝ) := by
    unfold phase
    push_cast
    ring
  rw [hp] at hh
  apply (hh.trans (mul_le_mul_of_nonneg_left he (by norm_num))).trans
  norm_num [expUpper, taylor12, start, firstA, Finset.sum_range_succ]

theorem second_tail :
    (∫ s in ((start : ℝ) + 16)..(60 : ℝ), expKernel secondA s) ≤ 1 / 10000000 := by
  have hh := exponential_tail (A := (secondA : ℝ)) (u := (start : ℝ) + 16) (v := 60)
    (by norm_num [secondA]) (by norm_num [start]) (by norm_num [start])
    (by norm_num [secondA, start])
  have he := exp_upper (x := (start + 16) + secondA / (start + 16)) (by norm_num [start, secondA])
  have hp : phase (secondA : ℝ) ((start : ℝ) + 16) =
      -(((start + 16) + secondA / (start + 16) : ℚ) : ℝ) := by
    unfold phase
    push_cast
    ring
  rw [hp] at hh
  apply (hh.trans (mul_le_mul_of_nonneg_left he (by norm_num))).trans
  norm_num [expUpper, taylor12, start, secondA, Finset.sum_range_succ]

theorem remaining_phase {lam s : ℝ} (hlam : 0.2743 ≤ lam) (hs : 0 < s) :
    phase (lam * 3100) s ≤ -58 := by
  have hA : 841 ≤ lam * 3100 := by linarith
  unfold phase
  have hsq := sq_nonneg (s - 29)
  have h : 58 - s ≤ lam * 3100 / s := by
    apply (le_div_iff₀ hs).mpr
    nlinarith
  linarith

theorem remaining_kernel {lam s : ℝ} (hlam : 0.2743 ≤ lam) (hs : 0 < s) :
    expKernel (lam * 3100) s ≤ (3100 : ℝ) ^ 4 * Real.exp (-58) :=
  mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (remaining_phase hlam hs)) (by norm_num)

theorem remaining_fee :
    (∫ _s in (start : ℝ)..(60 : ℝ), (18 : ℝ) * (3100 ^ 4 * Real.exp (-58))) ≤
      1 / 100000000 := by
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  have hh := exp_upper (x := 58) (by norm_num)
  norm_num only [Rat.cast_ofNat] at hh
  have hp := mul_le_mul_of_nonneg_left hh
    (show 0 ≤ (60 - (start : ℝ)) * (18 * 3100 ^ 4) by norm_num [start])
  apply (show (60 - (start : ℝ)) * (18 * (3100 ^ 4 * Real.exp (-58))) ≤
    (60 - (start : ℝ)) * (18 * 3100 ^ 4) * (expUpper 58 : ℝ) by nlinarith only [hp]).trans
  norm_num [expUpper, taylor12, start, Finset.sum_range_succ]

theorem signed_negative_tail :
    (3100 : ℝ) ^ 4 / 3 ^ 69 ≤
      ∫ s in (start : ℝ)..(60 : ℝ), expKernel 1116 s := by
  have hphase (s : ℝ) (hs : s ∈ Set.Icc (30 : ℝ) 31) : -69 ≤ phase 1116 s := by
    have hdiv : (1116 : ℝ) / s ≤ 1116 / 30 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs.1
    unfold phase
    linarith [hs.2]
  have hex : (1 / 3 ^ 69 : ℝ) ≤ Real.exp (-69) := by
    have hp := pow_le_pow_left₀ (Real.exp_pos 1).le
      (Real.exp_one_lt_d9.le.trans (by norm_num : (2.7182818286 : ℝ) ≤ 3)) 69
    rw [← Real.exp_nat_mul] at hp
    norm_num only [Nat.cast_ofNat, mul_one] at hp
    rw [Real.exp_neg, ← one_div]
    apply one_div_le_one_div_of_le (Real.exp_pos 69)
    norm_num at hp ⊢
    exact hp
  have hc : (3100 : ℝ) ^ 4 / 3 ^ 69 ≤
      ∫ s in (30 : ℝ)..31, expKernel 1116 s := by
    have hh := intervalIntegral.integral_mono_on (by norm_num : (30 : ℝ) ≤ 31)
      (f := fun _ => (3100 : ℝ) ^ 4 / 3 ^ 69) intervalIntegrable_const
      (expKernel_integrable 1116 (by norm_num) (by norm_num)) (fun s hs => by
        simpa only [expKernel, mul_one_div] using
          mul_le_mul_of_nonneg_left (hex.trans (Real.exp_le_exp.mpr (hphase s hs)))
            (by norm_num : (0 : ℝ) ≤ 3100 ^ 4))
    simpa only [intervalIntegral.integral_const, smul_eq_mul, show (31 - 30 : ℝ) = 1 by norm_num,
      one_mul] using hh
  apply hc.trans
  apply intervalIntegral.integral_mono_interval (by norm_num [start] : (start : ℝ) ≤ 30)
    (by norm_num : (30 : ℝ) ≤ 31) (by norm_num : (31 : ℝ) ≤ 60)
  · exact ae_restrict_of_forall_mem measurableSet_Ioc (fun _ _ => by unfold expKernel; positivity)
  · exact expKernel_integrable _ (by norm_num [start]) (by norm_num [start])

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536
