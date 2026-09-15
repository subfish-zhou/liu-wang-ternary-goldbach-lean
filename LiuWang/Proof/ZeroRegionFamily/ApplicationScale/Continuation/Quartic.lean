import LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.EulerShare

/-! # 任意谐波的Euler费用在合成后消去，保实际正极点 -/

set_option autoImplicit false
noncomputable section

open Complex
open LiuWang.Proof.ChebyshevBound.HighHeight
open LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.ZeroRegionFamily.RealClosure
open LiuWang.Proof.ZeroRegionFamily.Uniform

namespace LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation

theorem harmonic_share {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    harmonicBound chi sigma t ≤ harmonicPole chi sigma t+
      stechkinConductorCoeff*(Real.log q+Real.log (max 1 |t|)-Real.log Real.pi)+
        21/50+(14379/22150)*principalPrimeCost q sigma := by
  unfold harmonicBound harmonicPole
  split_ifs
  · have hh := principal_euler_share q hs
    linarith [stechkinK_tight.1]
  · have hh := conductor_euler_share chi hs
    linarith

theorem primitive_quartic_no_absolute_cost {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hc : chi ≠ 1) (hp : chi.IsPrimitive) {rho : ℂ}
    (hr : 1/2 < rho.re) (hz : chi.LFunction rho=0)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) :
    24480/(sigma-rho.re) ≤ 14379/(sigma-1)+
      46630*stechkinConductorCoeff*(Real.log q+Real.log (max 1 |rho.im|))+
        14900*harmonicPole (chi^2) sigma (2*rho.im)+
          6000*harmonicPole (chi^3) sigma (3*rho.im)+
            1250*harmonicPole (chi^4) sigma (4*rho.im) := by
  have hpos := quartic_stechkin_nonneg chi hs rho.im
  have hmain := primitive_actual_selected_bound hc hp hr hz hs hs1
  have h0 := principal_real_strong (q := q) hs hs1
  have h2 := (harmonicBound_paid (chi^2) hs hs1 (2*rho.im)).trans
    (harmonic_share (chi^2) hs (2*rho.im))
  have h3 := (harmonicBound_paid (chi^3) hs hs1 (3*rho.im)).trans
    (harmonic_share (chi^3) hs (3*rho.im))
  have h4 := (harmonicBound_paid (chi^4) hs hs1 (4*rho.im)).trans
    (harmonic_share (chi^4) hs (4*rho.im))
  have hl2 := mul_le_mul_of_nonneg_left (log_max_multiple (t := rho.im) (by norm_num : 1 ≤ (2 : ℕ))) conductorCoeff_bounds.1
  have hl3 := mul_le_mul_of_nonneg_left (log_max_multiple (t := rho.im) (by norm_num : 1 ≤ (3 : ℕ))) conductorCoeff_bounds.1
  have hl4 := mul_le_mul_of_nonneg_left (log_max_multiple (t := rho.im) (by norm_num : 1 ≤ (4 : ℕ))) conductorCoeff_bounds.1
  norm_num only [Nat.cast_ofNat] at hl2 hl3 hl4
  have hlog4 : Real.log (4 : ℝ)=2*Real.log 2 := by
    rw [show (4 : ℝ)=2^2 by norm_num, Real.log_pow]; norm_num
  rw [hlog4] at hl4
  have hlpi := mul_le_mul_of_nonneg_left log_pi_ge_one conductorCoeff_bounds.1
  have hl2u := mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le conductorCoeff_bounds.1
  have hl3u := mul_le_mul_of_nonneg_left Real.log_three_lt_d9.le conductorCoeff_bounds.1
  have hk := conductorCoeff_lower
  have hk1 := conductorCoeff_le_691_2500
  simp only [div_eq_mul_inv] at *
  nlinarith

end LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation
