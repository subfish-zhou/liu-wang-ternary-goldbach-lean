import LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Frontier.Offset

/-! # 逆字符共轭零点在额外谐波中的真实选中核 -/

set_option autoImplicit false
noncomputable section

open Complex
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Frontier

theorem inverse_actual_offset_bound {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    {rho : ℂ} (hr : 1/2 < rho.re) (hz : chi.LFunction rho=0) {sigma : ℝ}
    (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) (t : ℝ) :
    dampedLogDeriv chi⁻¹ sigma (stechkinSigma sigma) stechkinK t+
      (sigma-rho.re)/((sigma-rho.re)^2+(t+rho.im)^2) ≤
        stechkinConductorCoeff*(Real.log q+Real.log (max 1 |t|)-Real.log Real.pi)+
          4/15+(t+rho.im)^2/(sigma-1+rho.re)^3 := by
  have hinv := BombieriVinogradov.DirichletCharacter.inv_ne_one_of_ne_one hc
  have hp' := BombieriVinogradov.DirichletCharacter.IsPrimitive.inv hp
  have hz' : chi⁻¹.LFunction ((starRingEnd ℂ) rho)=0 := by
    rw [DirichletCharacter.LFunction_inv_eq_conj_conj hc, Complex.conj_conj, hz, map_zero]
  have hh := primitive_actual_offset_bound hinv hp' (by simpa only [Complex.conj_re] using hr)
    hz' hs hs1 t
  simpa only [Complex.conj_re, Complex.conj_im, sub_neg_eq_add] using hh

theorem power_predecessor_eq_inverse {q j : ℕ} {chi : DirichletCharacter ℂ q}
    (hj : chi^(j+1)=1) : chi^j=chi⁻¹ := by
  apply mul_right_cancel (b := chi)
  rw [inv_mul_cancel, ← pow_succ, hj]

theorem cubic_second_selected {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    (h3 : chi^3=1) {rho : ℂ} (hr : 1/2 < rho.re) (hz : chi.LFunction rho=0)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) :
    dampedLogDeriv (chi^2) sigma (stechkinSigma sigma) stechkinK (2*rho.im)+
      (sigma-rho.re)/((sigma-rho.re)^2+9*rho.im^2) ≤
        stechkinConductorCoeff*(Real.log q+Real.log (max 1 |2*rho.im|)-Real.log Real.pi)+
          4/15+9*rho.im^2/(sigma-1+rho.re)^3 := by
  have hh := inverse_actual_offset_bound hc hp hr hz hs hs1 (2*rho.im)
  rw [power_predecessor_eq_inverse (j := 2) h3]
  convert hh using 1 <;> ring

theorem quartic_third_selected {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    (h4 : chi^4=1) {rho : ℂ} (hr : 1/2 < rho.re) (hz : chi.LFunction rho=0)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) :
    dampedLogDeriv (chi^3) sigma (stechkinSigma sigma) stechkinK (3*rho.im)+
      (sigma-rho.re)/((sigma-rho.re)^2+16*rho.im^2) ≤
        stechkinConductorCoeff*(Real.log q+Real.log (max 1 |3*rho.im|)-Real.log Real.pi)+
          4/15+16*rho.im^2/(sigma-1+rho.re)^3 := by
  have hh := inverse_actual_offset_bound hc hp hr hz hs hs1 (3*rho.im)
  rw [power_predecessor_eq_inverse (j := 3) h4]
  convert hh using 1 <;> ring

end LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Frontier
