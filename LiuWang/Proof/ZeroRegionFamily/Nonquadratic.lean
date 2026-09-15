import LiuWang.Proof.ZeroRegionFamily.ComplexKernel
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.PrincipalHighStripLogDerivativeBound

/-! # 非二次字符的实际全高度零点间距 -/

set_option autoImplicit false
noncomputable section

open Complex
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ChebyshevBound.HighHeight

namespace LiuWang.Proof.ZeroRegionFamily

theorem principal_real_le_pole {q : ℕ} [NeZero q] {sigma : ℝ}
    (hs : 1 < sigma) (hs2 : sigma ≤ 2) :
    -(logDeriv (1 : DirichletCharacter ℂ q).LFunction (sigma : ℂ)).re ≤ 1/(sigma-1) := by
  have hn := norm_neg_logDeriv_LFunction_le_zeta (1 : DirichletCharacter ℂ q) hs
  have hz := norm_zeta_real_le_pole hs hs2
  have hr := (neg_le_abs (logDeriv (1 : DirichletCharacter ℂ q).LFunction (sigma : ℂ)).re).trans
    (Complex.abs_re_le_norm _)
  have hn' : ‖logDeriv (1 : DirichletCharacter ℂ q).LFunction (sigma : ℂ)‖ ≤ 1/(sigma-1) := by
    apply le_trans _ hz
    simpa [logDeriv_apply, norm_div, norm_neg] using hn
  exact hr.trans hn'

theorem principal_complex_le_pole {q : ℕ} [NeZero q] {s : ℂ}
    (hs : 1 < s.re) (hs2 : s.re ≤ 2) :
    -(logDeriv (1 : DirichletCharacter ℂ q).LFunction s).re ≤
      (1/(s-1)).re + Real.log q + Real.log (|s.im|+2)/2 + 1/3 := by
  have hz := zeta_without_zeros_le hs
  have ha := archimedean_re_le hs.le hs2
  have hc := norm_logDeriv_principalLevelCorrection_le_log (N := q) hs.le
  have hr := (neg_le_abs (logDeriv (principalLevelCorrection q) s).re).trans
    (Complex.abs_re_le_norm _)
  rw [logDeriv_principal_eq_levelCorrection_add_riemannZeta hs, Complex.add_re]
  simp only [neg_div, Complex.neg_re, ← logDeriv_apply] at hz
  linarith

theorem doubled_log_le (t : ℝ) :
    Real.log (|2*t|+2) ≤ Real.log (|t|+2)+1 := by
  have hh := Real.log_le_log (by positivity : 0 < |2*t|+2)
    (show |2*t|+2 ≤ 2*(|t|+2) by rw [abs_mul]; norm_num; linarith [abs_nonneg t])
  rw [Real.log_mul (by norm_num) (by positivity)] at hh
  linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]

theorem primitive_nonquadratic_gap {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hchi : chi ≠ 1) (hprim : chi.IsPrimitive)
    (hsq : chi^2 ≠ 1) {rho : ℂ} (hrho : 0 < rho.re) (hz : chi.LFunction rho = 0) :
    1/(140*(Real.log q+Real.log (|rho.im|+2))) ≤ 1-rho.re := by
  obtain ⟨p, hp⟩ := exists_completedZeroIndex_of_LFunction_eq_zero hchi hprim hrho hz
  have hstrip := symmetricCompletedLFunction_divisorZeroIndex₀_re_mem_Ioo hchi hprim p
  rw [hp] at hstrip
  have hlog := log_level_gt_one
    (BombieriVinogradov.DirichletCharacter.three_le_level_of_ne_one chi hchi)
  have hht : 0 ≤ Real.log (|rho.im|+2) := Real.log_nonneg (by linarith [abs_nonneg rho.im])
  have hcore : (14*10*(Real.log q+Real.log (|rho.im|+2)))⁻¹ ≤ 1-rho.re := by
    apply core_inequality_implies_gap (K := 10) hstrip.2 (by norm_num)
      (by linarith) (by linarith)
    intro sigma hs hs2
    have hpos := logDerivative_combination_nonneg chi hs rho.im
    have hmain := primitive_selected_kernel_le hchi hprim p
      (s := (sigma : ℂ)+I*(rho.im : ℂ)) (by simpa using hs) (by simpa using hs2)
    have hthird := nonprincipal_without_zeros_le hsq
      (s := (sigma : ℂ)+2*I*(rho.im : ℂ)) (by simpa using hs) (by simpa using hs2)
    have hprincipal := principal_real_le_pole (q := q) hs hs2
    have hk := zeroKernel_re_of_same_im (s := (sigma : ℂ)+I*(rho.im : ℂ)) (rho := rho)
      (by simpa using ne_of_gt (hstrip.2.trans hs)) (by simp)
    rw [hp, one_div, hk] at hmain
    simp only [neg_div, Complex.neg_re, ← logDeriv_apply] at hpos
    have hdouble := doubled_log_le rho.im
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hdouble
    norm_num [Complex.add_im, Complex.mul_im, Complex.add_re, Complex.mul_re] at hmain hthird
    have hcoeff : 7/2*Real.log q + 5/2*Real.log (|rho.im|+2)+11/2 ≤
        10*(Real.log q+Real.log (|rho.im|+2)) := by linarith
    simp only [one_div] at hprincipal hmain ⊢
    linarith
  simpa only [show (14:ℝ)*10=140 by norm_num, one_div] using hcore

theorem nonquadratic_gap {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hsq : chi^2 ≠ 1)
    {rho : ℂ} (hrho : 0 < rho.re) (hz : chi.LFunction rho = 0) :
    1/(140*(Real.log chi.conductor+Real.log (|rho.im|+2))) ≤ 1-rho.re := by
  have hchi : chi ≠ 1 := by intro h; apply hsq; simp [h]
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hpr := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hchi
  have hsqp := BombieriVinogradov.DirichletCharacter.primitiveCharacter_pow_ne_one_of_pow_ne_one
    chi hsq
  exact primitive_nonquadratic_gap hpr chi.primitiveCharacter_isPrimitive hsqp hrho
    (primitive_LFunction_eq_zero_of_LFunction_eq_zero chi hchi hrho hz)

end LiuWang.Proof.ZeroRegionFamily
