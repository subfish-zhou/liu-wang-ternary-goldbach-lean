import LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Frontier.Inverse

/-! # 同一个实际四次正性中保留低阶额外选中核，显式保留偏心误差 -/

set_option autoImplicit false
noncomputable section

open Complex
open LiuWang.Proof.ChebyshevBound.HighHeight
open LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.ZeroRegionFamily.RealClosure
open LiuWang.Proof.ZeroRegionFamily.Uniform

namespace LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Frontier

private theorem quartic_combine {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    {rho : ℂ} (hr : 1/2 < rho.re) (hz : chi.LFunction rho=0)
    {sigma k2 k3 k4 e2 e3 e4 : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20)
    (h2 : dampedLogDeriv (chi^2) sigma (stechkinSigma sigma) stechkinK (2*rho.im)+k2 ≤
      harmonicPole (chi^2) sigma (2*rho.im)+
        stechkinConductorCoeff*(Real.log q+Real.log (max 1 |2*rho.im|)-Real.log Real.pi)+
          21/50+(14379/22150)*principalPrimeCost q sigma+e2)
    (h3 : dampedLogDeriv (chi^3) sigma (stechkinSigma sigma) stechkinK (3*rho.im)+k3 ≤
      harmonicPole (chi^3) sigma (3*rho.im)+
        stechkinConductorCoeff*(Real.log q+Real.log (max 1 |3*rho.im|)-Real.log Real.pi)+
          21/50+(14379/22150)*principalPrimeCost q sigma+e3)
    (h4 : dampedLogDeriv (chi^4) sigma (stechkinSigma sigma) stechkinK (4*rho.im)+k4 ≤
      harmonicPole (chi^4) sigma (4*rho.im)+
        stechkinConductorCoeff*(Real.log q+Real.log (max 1 |4*rho.im|)-Real.log Real.pi)+
          21/50+(14379/22150)*principalPrimeCost q sigma+e4) :
    24480/(sigma-rho.re)+14900*k2+6000*k3+1250*k4 ≤ 14379/(sigma-1)+
      46630*stechkinConductorCoeff*(Real.log q+Real.log (max 1 |rho.im|))+
        14900*harmonicPole (chi^2) sigma (2*rho.im)+
          6000*harmonicPole (chi^3) sigma (3*rho.im)+
            1250*harmonicPole (chi^4) sigma (4*rho.im)+14900*e2+6000*e3+1250*e4 := by
  have hpos := quartic_stechkin_nonneg chi hs rho.im
  have hmain := primitive_actual_selected_bound hc hp hr hz hs hs1
  have h0 := principal_real_strong (q := q) hs hs1
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

private theorem offset_share {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) (hp : chi.IsPrimitive) {rho : ℂ} (hr : 1/2 < rho.re)
    (hz : chi.LFunction rho=0) {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) (t : ℝ) :
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK t+
      (sigma-rho.re)/((sigma-rho.re)^2+(t-rho.im)^2) ≤
        harmonicPole chi sigma t+
          stechkinConductorCoeff*(Real.log q+Real.log (max 1 |t|)-Real.log Real.pi)+
            21/50+(14379/22150)*principalPrimeCost q sigma+(t-rho.im)^2/(sigma-1+rho.re)^3 := by
  have hh := primitive_actual_offset_bound hc hp hr hz hs hs1 t
  have he := principalPrimeCost_nonneg q hs
  simp only [harmonicPole, if_neg hc, zero_add]
  linarith

theorem cubic_quartic_augmented {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hc : chi ≠ 1) (hp : chi.IsPrimitive) (h3 : chi^3=1)
    {rho : ℂ} (hr : 1/2 < rho.re) (hz : chi.LFunction rho=0) {sigma : ℝ}
    (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) :
    24480/(sigma-rho.re)+16150*((sigma-rho.re)/((sigma-rho.re)^2+9*rho.im^2)) ≤
      14379/(sigma-1)+46630*stechkinConductorCoeff*(Real.log q+Real.log (max 1 |rho.im|))+
        6000*poleDifference sigma (3*rho.im)+145350*rho.im^2/(sigma-1+rho.re)^3 := by
  have h2i := power_predecessor_eq_inverse (j := 2) h3
  have h4i : chi^4=chi := by rw [show (4 : ℕ)=3+1 by norm_num, pow_succ, h3, one_mul]
  have hci := BombieriVinogradov.DirichletCharacter.inv_ne_one_of_ne_one hc
  have hpi := BombieriVinogradov.DirichletCharacter.IsPrimitive.inv hp
  have hzi : chi⁻¹.LFunction ((starRingEnd ℂ) rho)=0 := by
    rw [BombieriVinogradov.SiegelWalfisz.DirichletCharacter.LFunction_inv_eq_conj_conj hc,
      Complex.conj_conj, hz, map_zero]
  have h2 := offset_share hci hpi (by simpa only [Complex.conj_re] using hr) hzi hs hs1 (2*rho.im)
  have h4 := offset_share hc hp hr hz hs hs1 (4*rho.im)
  have hmid := (harmonicBound_paid (chi^3) hs hs1 (3*rho.im)).trans
    (harmonic_share (chi^3) hs (3*rho.im))
  have h2' := h2
  rw [← h2i] at h2'
  simp only [Complex.conj_re, Complex.conj_im, sub_neg_eq_add] at h2'
  have h4' := h4
  rw [← h4i] at h4'
  have hh := quartic_combine hc hp hr hz (k3 := 0) (e3 := 0) hs hs1 h2' (by simpa using hmid) h4'
  rw [h2i, h3, h4i] at hh
  simp only [harmonicPole, if_neg hci, if_neg hc, ite_true] at hh
  convert hh using 1 <;> ring

theorem quartic_quartic_augmented {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hc : chi ≠ 1) (hp : chi.IsPrimitive) (h4 : chi^4=1)
    {rho : ℂ} (hr : 1/2 < rho.re) (hz : chi.LFunction rho=0) {sigma : ℝ}
    (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) :
    24480/(sigma-rho.re)+6000*((sigma-rho.re)/((sigma-rho.re)^2+16*rho.im^2)) ≤
      14379/(sigma-1)+46630*stechkinConductorCoeff*(Real.log q+Real.log (max 1 |rho.im|))+
        14900*harmonicPole (chi^2) sigma (2*rho.im)+
          1250*poleDifference sigma (4*rho.im)+96000*rho.im^2/(sigma-1+rho.re)^3 := by
  have h3i := power_predecessor_eq_inverse (j := 3) h4
  have hci := BombieriVinogradov.DirichletCharacter.inv_ne_one_of_ne_one hc
  have hpi := BombieriVinogradov.DirichletCharacter.IsPrimitive.inv hp
  have hzi : chi⁻¹.LFunction ((starRingEnd ℂ) rho)=0 := by
    rw [BombieriVinogradov.SiegelWalfisz.DirichletCharacter.LFunction_inv_eq_conj_conj hc,
      Complex.conj_conj, hz, map_zero]
  have h3 := offset_share hci hpi (by simpa only [Complex.conj_re] using hr) hzi hs hs1 (3*rho.im)
  rw [← h3i] at h3
  simp only [Complex.conj_re, Complex.conj_im, sub_neg_eq_add] at h3
  have h2 := (harmonicBound_paid (chi^2) hs hs1 (2*rho.im)).trans
    (harmonic_share (chi^2) hs (2*rho.im))
  have hl4 := (harmonicBound_paid (chi^4) hs hs1 (4*rho.im)).trans
    (harmonic_share (chi^4) hs (4*rho.im))
  have hh := quartic_combine hc hp hr hz (k2 := 0) (e2 := 0) (k4 := 0) (e4 := 0)
    hs hs1 (by simpa using h2) h3 (by simpa using hl4)
  rw [h3i, h4] at hh
  simp only [harmonicPole, if_neg hci, ite_true] at hh
  unfold harmonicPole
  convert hh using 1 <;> ring

end LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Frontier
