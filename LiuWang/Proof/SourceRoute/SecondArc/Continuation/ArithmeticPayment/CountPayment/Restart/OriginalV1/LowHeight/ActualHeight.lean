import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight.ActualCount

set_option autoImplicit false
noncomputable section
open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight

theorem low_integrand_continuous {L : ℝ} (hL : 3100 ≤ L) :
    ContinuousOn (fun s : ℝ => lowWeight (L ^ (3 : ℕ)) s *
      Real.exp (-0.478 * (L + Real.log 0.001) / Real.log s))
        (Set.Icc (3.36 * L ^ (3 : ℕ)) (scaledGate L)) := by
  apply continuousOn_of_forall_continuousAt
  intro s hs
  have hd := (low_scalar_domain hL).2.2 s hs
  have hs0 : 0 < s := by linarith [hd.1]
  have hL0 : 0 < L := by linarith
  have hlog : Real.log s ≠ 0 := (Real.log_pos hd.1).ne'
  have hp1 : ContinuousAt (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) s :=
    continuousAt_id.rpow_const (Or.inl hs0.ne')
  have hp3 : ContinuousAt (fun t : ℝ => t ^ (-(3 / 2 : ℝ))) s :=
    continuousAt_id.rpow_const (Or.inl hs0.ne')
  have hl : ContinuousAt (fun t : ℝ => Real.log (L ^ (3 : ℕ) * t)) s :=
    ((continuousAt_const (y := L ^ (3 : ℕ))).mul continuousAt_id).log
      (mul_ne_zero (pow_ne_zero _ hL0.ne') hs0.ne')
  have hw : ContinuousAt (lowWeight (L ^ (3 : ℕ))) s :=
    (((hp1.mul hl).div_const Real.pi).sub (hp1.const_mul 0.874) |>.add
      ((hp3.const_mul (6.8423 * L ^ (3 : ℕ))).mul hl)).add
        (hp3.const_mul (15 * L ^ (3 : ℕ)))
  exact hw.mul (Real.continuous_exp.continuousAt.comp
    ((continuousAt_const (y := -0.478 * (L + Real.log 0.001))).div
      (continuousAt_id.log hs0.ne') hlog))

theorem low_integrand_nonneg {L s : ℝ} (hL : 3100 ≤ L)
    (hs : s ∈ Set.Icc (3.36 * L ^ (3 : ℕ)) (scaledGate L)) :
    0 ≤ lowWeight (L ^ (3 : ℕ)) s * Real.exp (-0.478 * (L + Real.log 0.001) / Real.log s) := by
  have hd := (low_scalar_domain hL).2.2 s hs
  exact mul_nonneg (lowWeight_nonneg (by positivity) (by linarith [hd.1]) hd.2)
    (Real.exp_pos _).le

theorem originalLowScalar_nonneg {L : ℝ} (hL : 3100 ≤ L) : 0 ≤ originalLowScalar L := by
  unfold originalLowScalar
  apply intervalIntegral.integral_nonneg (low_scalar_domain hL).2.1
  intro s hs
  simpa only [mul_assoc] using mul_nonneg (by linarith : 0 ≤ L) (low_integrand_nonneg hL hs)

theorem actual_low_height_le_original {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hgate : omegaCutoff N q ≤ densityGate q) :
    lowHeightIntegral N q ≤
      (q.totient / Real.sqrt q) * (originalLowScalar (sourceL N) / sourceL N) := by
  have hL := sourceL_ge_3100 hN
  have hL0 : 0 < sourceL N := by linarith
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hd := low_gate_coupled_domain hN hq hgate
  have hfull := (middle_height_domain hN hq).2.1
  have hi : IntervalIntegrable (fun y : ℝ => heightKernel y *
      ∫ alpha in (59 / 60 : ℝ)..stripLower q y,
        alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ))
        volume (omegaCutoff N q) (densityGate q) := by
    apply (actual_high_alpha_height_integrable hN hq).mono_set
    rw [Set.uIcc_of_le hgate, Set.uIcc_of_le hfull]
    exact Set.Icc_subset_Icc le_rfl hd.2.1
  have hc : ContinuousOn (fun y : ℝ => heightKernel y * (q.totient * source24Envelope q y) *
      Real.exp (-0.478 * (sourceL N + Real.log 0.001) / Real.log ((q : ℝ) * y)))
        (Set.Icc (omegaCutoff N q) (densityGate q)) := by
    apply continuousOn_of_forall_continuousAt
    intro y hy
    have hy0 := hd.1.trans_le hy.1
    have hz := (middle_log_domain hN hq (low_scaled_interval hN hq hgate hy).2).2.1
    have hlog : Real.log ((q : ℝ) * y) ≠ 0 := by linarith
    have hk : ContinuousAt heightKernel y :=
      continuousAt_id.rpow_const (Or.inl hy0.ne')
    have hl : ContinuousAt (fun t : ℝ => Real.log ((q : ℝ) * t)) y :=
      ((continuousAt_const (y := (q : ℝ))).mul continuousAt_id).log (mul_ne_zero hq0.ne' hy0.ne')
    have hw : ContinuousAt (source24Envelope q) y :=
      ((((continuousAt_id.div_const Real.pi).mul hl).sub (continuousAt_id.const_mul 0.874)).add
        (hl.const_mul 6.8423)).add continuousAt_const
    exact (hk.mul (hw.const_mul (q.totient : ℝ))).mul (Real.continuous_exp.continuousAt.comp
      ((continuousAt_const (y := -0.478 * (sourceL N + Real.log 0.001))).div hl hlog))
  have hbound := intervalIntegral.integral_mono_on hgate hi
    (hc.intervalIntegrable_of_Icc hgate) (fun y hy => by
      have hh := mul_le_mul_of_nonneg_left (actual_low_inner_source24 hN hq hgate hy)
        (heightKernel_nonneg (hd.1.trans_le hy.1).le)
      simpa only [mul_assoc] using hh)
  rw [source24_height_change hq0 hd.1 hgate] at hbound
  have hstart : (q : ℝ) * omegaCutoff N q = 3.36 * sourceP N := by
    unfold omegaCutoff
    field_simp
  rw [hstart] at hbound
  have hab : 3.36 * sourceP N ≤ (q : ℝ) * densityGate q := by
    rw [← hstart]
    exact mul_le_mul_of_nonneg_left hgate hq0.le
  have hdom := low_scalar_domain hL
  have hsub : Set.Icc (3.36 * sourceP N) ((q : ℝ) * densityGate q) ⊆
      Set.Icc (3.36 * sourceL N ^ (3 : ℕ)) (scaledGate (sourceL N)) :=
    Set.Icc_subset_Icc le_rfl hd.2.2
  have hscont : ContinuousOn (fun s : ℝ => scaledSource24Weight q s *
      Real.exp (-0.478 * (sourceL N + Real.log 0.001) / Real.log s))
        (Set.Icc (3.36 * sourceP N) ((q : ℝ) * densityGate q)) := by
    apply continuousOn_of_forall_continuousAt
    intro s hs
    have hs1 := (hdom.2.2 s (hsub hs)).1
    have hs0 : 0 < s := by linarith
    have hl : Real.log s ≠ 0 := (Real.log_pos hs1).ne'
    have hp3 : ContinuousAt (fun t : ℝ => t ^ (-(3 / 2 : ℝ))) s :=
      continuousAt_id.rpow_const (Or.inl hs0.ne')
    have hlc : ContinuousAt Real.log s := continuousAt_id.log hs0.ne'
    have hw : ContinuousAt (scaledSource24Weight q) s :=
      hp3.mul (((continuousAt_id.mul hlc).div_const Real.pi |>.sub
        (continuousAt_id.const_mul 0.874)).add (hlc.const_mul (6.8423 * q)) |>.add continuousAt_const)
    exact hw.mul (Real.continuous_exp.continuousAt.comp
      ((continuousAt_const (y := -0.478 * (sourceL N + Real.log 0.001))).div hlc hl))
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hab
    (hscont.intervalIntegrable_of_Icc hab)
    (((low_integrand_continuous hL).mono hsub).intervalIntegrable_of_Icc hab)
    (fun s hs => mul_le_mul_of_nonneg_right
      (scaledSource24Weight_le hq1 hq ((hdom.2.2 s (hsub hs)).1.le))
        (Real.exp_pos _).le)
  have hext := intervalIntegral.integral_mono_interval (μ := volume) (le_refl (3.36 * sourceP N))
    hab hd.2.2 (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
      (fun s hs => low_integrand_nonneg hL ⟨hs.1.le, hs.2⟩))
    ((low_integrand_continuous hL).intervalIntegrable_of_Icc hdom.2.1)
  have hscalar : originalLowScalar (sourceL N) / sourceL N =
      ∫ s in (3.36 * sourceP N)..scaledGate (sourceL N),
        lowWeight (sourceP N) s * Real.exp (-0.478 * (sourceL N + Real.log 0.001) / Real.log s) := by
    unfold originalLowScalar
    simp_rw [mul_assoc]
    rw [intervalIntegral.integral_const_mul]
    rw [mul_div_cancel_left₀ _ hL0.ne']
    simp only [sourceP, scaledGate, mul_assoc]
  rw [hscalar]
  exact hbound.trans (mul_le_mul_of_nonneg_left (hmono.trans hext) (by positivity))

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight
