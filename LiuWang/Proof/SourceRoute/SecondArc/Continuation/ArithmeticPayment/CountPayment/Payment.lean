import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.ActualHeight
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.ScalarPayment

set_option autoImplicit false
noncomputable section
open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment

theorem actual_low_height_integral_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hgate : omegaCutoff N q ≤ densityGate q) :
    (Real.sqrt q / q.totient) * lowHeightIntegral N q ≤
      ∫ z in (3.36 * sourceL N ^ (3 : ℕ))..scaledGate (sourceL N),
        coupledKernel (sourceL N ^ (3 : ℕ)) (sourceL N + Real.log 0.001) z := by
  have hd := low_gate_coupled_domain hN hq hgate
  have hL := sourceL_ge_3100 hN
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hA : 1 < 3.36 * sourceL N ^ (3 : ℕ) := by
    have hp : 1 ≤ sourceL N ^ (3 : ℕ) := one_le_pow₀ (by linarith : 1 ≤ sourceL N)
    linarith
  have hstart : (q : ℝ) * omegaCutoff N q = 3.36 * sourceL N ^ (3 : ℕ) := by
    unfold omegaCutoff sourceP
    field_simp
  have hAB : 3.36 * sourceL N ^ (3 : ℕ) ≤ (q : ℝ) * densityGate q := by
    rw [← hstart]
    exact mul_le_mul_of_nonneg_left hgate hq0.le
  have hfull := hAB.trans hd.2.2
  have hi := (coupledKernel_continuous (P := sourceL N ^ (3 : ℕ))
    (H := sourceL N + Real.log 0.001) hA).intervalIntegrable_of_Icc (μ := volume) hfull
  apply (actual_low_height_coupled_bound hN hq hgate).trans
  calc
    _ ≤ ∫ z in (3.36 * sourceL N ^ (3 : ℕ))..((q : ℝ) * densityGate q),
        coupledKernel (sourceL N ^ (3 : ℕ)) (sourceL N + Real.log 0.001) z := by
      apply intervalIntegral.integral_mono_on hAB
        ((coupledKernel_continuous (P := (q : ℝ))
          (H := sourceL N + Real.log 0.001) hA).intervalIntegrable_of_Icc hAB)
        ((coupledKernel_continuous (P := sourceL N ^ (3 : ℕ))
          (H := sourceL N + Real.log 0.001) hA).intervalIntegrable_of_Icc hAB)
      intro z hz
      have hz0 : 0 < z := by linarith [hz.1]
      have hl0 := Real.log_nonneg (le_of_lt (hA.trans_le hz.1))
      unfold coupledKernel heightKernel
      gcongr
      exact hq
    _ ≤ _ := intervalIntegral.integral_mono_interval le_rfl hAB hd.2.2
      (by
        apply ae_restrict_of_forall_mem measurableSet_Ioc
        intro z hz
        have hz0 : 0 < z := by linarith [hz.1]
        have hl0 := Real.log_nonneg (le_of_lt (hA.trans hz.1))
        unfold coupledKernel heightKernel
        positivity) hi

theorem actual_513_normalized_sharp {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hgate : omegaCutoff N q ≤ densityGate q) :
    (Real.sqrt q / q.totient) * lowHeightIntegral N q ≤
      0.000006510372 / sourceL N := by
  have hL := sourceL_ge_3100 hN
  have hLp : 0 < sourceL N := by linarith
  have h := actual_low_height_integral_bound hN hq hgate
  have hc := coupled_scalar_payment hL
  apply h.trans
  apply (le_div_iff₀ hLp).mpr
  linarith only [hc]

theorem actual_513_payment {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hgate : omegaCutoff N q ≤ densityGate q) :
    lowHeightIntegral N q ≤
      0.0000076 * (q.totient : ℝ) / (Real.sqrt q * sourceL N) := by
  have h := actual_513_normalized_sharp hN hq hgate
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hs : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hq0
  have hphi : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  have hLp : 0 < sourceL N := by linarith [sourceL_ge_3100 hN]
  apply (le_div_iff₀ (mul_pos hs hLp)).mpr
  have hh := (le_div_iff₀ hLp).mp h
  have hm := mul_le_mul_of_nonneg_right hh hphi.le
  field_simp at hm
  nlinarith only [hm, hphi]

theorem low_height_strong_payment {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hgate : omegaCutoff N q ≤ densityGate q) :
    (5 * (N : ℝ) * Real.sqrt q / q.totient) * lowHeightIntegral N q ≤
      0.00003255186 * (N : ℝ) / sourceL N := by
  have hh := mul_le_mul_of_nonneg_left (actual_513_normalized_sharp hN hq hgate)
    (by positivity : 0 ≤ 5 * (N : ℝ))
  simp only [div_eq_mul_inv] at hh ⊢
  nlinarith only [hh]

theorem low_height_original_eight_payment {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hgate : omegaCutoff N q ≤ densityGate q) :
    (8 * (N : ℝ) * Real.sqrt q / q.totient) * lowHeightIntegral N q ≤
      0.000052082976 * (N : ℝ) / sourceL N := by
  have hh := mul_le_mul_of_nonneg_left (actual_513_normalized_sharp hN hq hgate)
    (by positivity : 0 ≤ 8 * (N : ℝ))
  simp only [div_eq_mul_inv] at hh ⊢
  nlinarith only [hh]

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment
