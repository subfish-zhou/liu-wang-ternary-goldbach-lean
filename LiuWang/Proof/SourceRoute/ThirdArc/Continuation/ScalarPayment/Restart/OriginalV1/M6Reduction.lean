import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.MovingDomains

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1

def sourceNu (x : ℝ) : ℝ :=
  Real.exp Real.eulerMascheroniConstant * Real.log (Real.log x) +
    2.50637 / Real.log (Real.log x)

def sourceM6 (N q : ℕ) [NeZero q] : ℝ :=
  (5 * N * Real.sqrt q / q.totient) *
    ∫ y in middleHeight N q..sourceT N, y ^ (-2 : ℝ) *
      countIntegral q N y (sourceCutoff q 0.478 y) (sourceCutoff q 0.10367089 y)

def m6LogKernel (L t : ℝ) : ℝ := Real.exp (-t - 0.10367089 * L / t)

def m6OriginalScalar (L : ℝ) : ℝ :=
  70000 * L ^ 4 * sourceNu (L ^ 6) *
    ∫ t in Real.log (10 * Real.pi * L ^ 7)..Real.log (L ^ 21), m6LogKernel L t

theorem moving_14000_strip_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    {X y d : ℝ} (hX : 1 ≤ X) (hy : lowHeight ≤ y)
    (hd : 0 ≤ d) (hd1 : d ≤ 0.478) :
    countIntegral q X y (sourceCutoff q 0.478 y) (sourceCutoff q d y) ≤
      14000 * Real.exp (-d * Real.log X / Real.log ((q : ℝ) * y)) := by
  have h := M3_near_one_integral_paid .r0478 hN hq hX hy hd hd1
  change countIntegral q X y (sourceCutoff q 0.478 y) (sourceCutoff q d y) ≤
    14000 * (Real.exp (-d * Real.log X / Real.log ((q : ℝ) * y)) -
      Real.exp (-0.478 * Real.log X / Real.log ((q : ℝ) * y))) at h
  linarith [Real.exp_pos (-0.478 * Real.log X / Real.log ((q : ℝ) * y))]

theorem moving_cutoff_exp_continuous {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (X d : ℝ) {u v : ℝ} (hu : lowHeight ≤ u) (huv : u ≤ v) :
    ContinuousOn (fun y => Real.exp (-d * Real.log X / Real.log ((q : ℝ) * y)))
      (Set.uIcc u v) := by
  rw [Set.uIcc_of_le huv]
  intro y hy
  have hlow := hu.trans hy.1
  have hz : 0 < (q : ℝ) * y := by linarith [(M3_table_domain hN hq hlow).1]
  have hl : Real.log ((q : ℝ) * y) ≠ 0 := by
    linarith [M3_log_product_ge_thirty hN hq hlow]
  exact (Real.continuous_exp.continuousAt.comp
    (continuousAt_const.div ((continuousAt_const.mul continuousAt_id).log hz.ne') hl)
      ).continuousWithinAt

theorem moving_14000_height_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    {X u v d p : ℝ} (hX : 1 ≤ X) (hu : lowHeight ≤ u) (huv : u ≤ v)
    (hd : 0 ≤ d) (hd1 : d ≤ 0.478) (hp : 0 ≤ p) :
    (∫ y in u..v, heightKernel p y *
      countIntegral q X y (sourceCutoff q 0.478 y) (sourceCutoff q d y)) ≤
      14000 * ∫ y in u..v, heightKernel p y *
        Real.exp (-d * Real.log X / Real.log ((q : ℝ) * y)) := by
  have hi := heightKernel_mul_integrable (lowHeight_pos.trans_le hu) huv p
    (moving_cutoff_exp_continuous hN hq X d hu huv).intervalIntegrable
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on huv
    (moving_strip_integrable hN hq hX hu huv hd hd1 le_rfl) (hi.const_mul _)
  intro y hy
  have hk : 0 ≤ heightKernel p y :=
    mul_nonneg hp (Real.rpow_nonneg (lowHeight_pos.trans_le (hu.trans hy.1)).le _)
  have h := mul_le_mul_of_nonneg_left
    (moving_14000_strip_bound hN hq hX (hu.trans hy.1) hd hd1) hk
  nlinarith only [h]

theorem cutoff_exp_log_substitution (q : ℕ) [NeZero q]
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (X d p : ℝ) :
    (∫ y in u..v, heightKernel p y *
      Real.exp (-d * Real.log X / Real.log ((q : ℝ) * y))) =
      p * (q : ℝ) ^ p *
        ∫ t in Real.log ((q : ℝ) * u)..Real.log ((q : ℝ) * v),
          Real.exp (-p * t - d * Real.log X / t) := by
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  rw [height_log_substitution hq hu hv]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  have he : (q : ℝ) * (Real.exp t / q) = Real.exp t := by field_simp
  dsimp only
  rw [he, Real.log_exp, ← Real.exp_add]
  congr 1
  ring

theorem sourceM6_same_modulus {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N) :
    sourceM6 N q ≤
      (70000 * N * Real.sqrt q * ((q : ℝ) / q.totient)) *
        ∫ t in Real.log (10 * Real.pi * sourceL N ^ 7)..
          Real.log ((q : ℝ) * sourceT N), m6LogKernel (sourceL N) t := by
  have hh := original_height_order (exp_2000_le_of_exp_3100_le hN) hq1
  have hX : (1 : ℝ) ≤ N := by exact_mod_cast nat_pos_of_exp_le hN
  have h := moving_14000_height_bound hN hq hX hh.1 hh.2
    (d := 0.10367089) (p := 1) (by norm_num) (by norm_num) (by norm_num)
  rw [cutoff_exp_log_substitution q (lowHeight_pos.trans_le hh.1)
    (lowHeight_pos.trans_le (hh.1.trans hh.2))] at h
  have he : (q : ℝ) * middleHeight N q = 10 * Real.pi * sourceL N ^ 7 := by
    unfold middleHeight
    have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
    field_simp
  simp only [heightKernel, one_mul, Real.rpow_one,
    show -(1 : ℝ) - 1 = -2 by norm_num, he, neg_mul, one_mul] at h
  have hs := mul_le_mul_of_nonneg_left h
    (show 0 ≤ 5 * N * Real.sqrt q / q.totient by positivity)
  change sourceM6 N q ≤ _ at hs
  unfold m6LogKernel
  change sourceM6 N q ≤ _ at hs
  convert hs using 1
  unfold sourceL
  ring

theorem m6LogKernel_integrable {L a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (m6LogKernel L) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  intro t ht
  have ht0 : t ≠ 0 := (ha.trans_le ht.1).ne'
  exact (Real.continuous_exp.continuousAt.comp
    (continuousAt_id.neg.sub (continuousAt_const.div continuousAt_id ht0))).continuousWithinAt

theorem equation_5_44_original_integral {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q)
    (hnu : sourceNu q ≤ sourceNu (sourceL N ^ 6)) :
    sourceM6 N q ≤ (N : ℝ) / sourceL N * m6OriginalScalar (sourceL N) := by
  have hL0 := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  have hh := original_height_order (exp_2000_le_of_exp_3100_le hN) hq1
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hT0 : 0 < sourceT N := pow_pos hL0 15
  have he : (q : ℝ) * middleHeight N q = 10 * Real.pi * sourceL N ^ 7 := by
    unfold middleHeight
    field_simp
  have hab : Real.log (10 * Real.pi * sourceL N ^ 7) ≤
      Real.log ((q : ℝ) * sourceT N) := by
    rw [← he]
    exact Real.log_le_log (mul_pos hq0 (lowHeight_pos.trans_le hh.1))
      (mul_le_mul_of_nonneg_left hh.2 hq0.le)
  have hbd : Real.log ((q : ℝ) * sourceT N) ≤ Real.log (sourceL N ^ 21) := by
    apply Real.log_le_log (mul_pos hq0 hT0)
    calc
      _ ≤ sourceL N ^ 6 * sourceL N ^ 15 :=
        mul_le_mul_of_nonneg_right hq1 hT0.le
      _ = _ := by ring
  have ha : 0 < Real.log (10 * Real.pi * sourceL N ^ 7) := by
    rw [← he]
    linarith [M3_log_product_ge_thirty hN hq hh.1]
  have hi := intervalIntegral.integral_mono_interval le_rfl hab hbd
    (ae_of_all _ (fun t => (Real.exp_pos (-t - 0.10367089 * sourceL N / t)).le))
    (m6LogKernel_integrable ha (hab.trans hbd))
  have hnu0 : 0 ≤ sourceNu (sourceL N ^ 6) :=
    (div_nonneg hq0.le (Nat.cast_nonneg _)).trans (htotient.trans hnu)
  have hsqrt : Real.sqrt q ≤ sourceL N ^ 3 := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨(pow_pos hL0 3).le, ?_⟩
    calc
      (q : ℝ) ≤ sourceL N ^ 6 := hq1
      _ = (sourceL N ^ 3) ^ 2 := by ring
  have hc : 70000 * N * Real.sqrt q * ((q : ℝ) / q.totient) ≤
      70000 * N * sourceL N ^ 3 * sourceNu (sourceL N ^ 6) := by
    have h := mul_le_mul hsqrt (htotient.trans hnu)
      (div_nonneg hq0.le (Nat.cast_nonneg _)) (pow_nonneg hL0.le 3)
    nlinarith only [mul_le_mul_of_nonneg_left h (show 0 ≤ 70000 * (N : ℝ) by positivity)]
  have hi0 : 0 ≤ ∫ t in Real.log (10 * Real.pi * sourceL N ^ 7)..
      Real.log ((q : ℝ) * sourceT N), m6LogKernel (sourceL N) t :=
    intervalIntegral.integral_nonneg hab (fun _ _ => (Real.exp_pos _).le)
  calc
    _ ≤ _ := sourceM6_same_modulus hN hq hq1
    _ ≤ (70000 * N * sourceL N ^ 3 * sourceNu (sourceL N ^ 6)) *
        ∫ t in Real.log (10 * Real.pi * sourceL N ^ 7)..
          Real.log (sourceL N ^ 21), m6LogKernel (sourceL N) t :=
      mul_le_mul hc hi hi0 (by positivity)
    _ = _ := by
      unfold m6OriginalScalar
      field_simp

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1
