import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CaseIV

set_option autoImplicit false
noncomputable section

open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.MultiZeroRepulsion

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1

def lwdSignedCharacter {q : ℕ} (chi : DirichletCharacter ℂ q) (b : Bool) :
    DirichletCharacter ℂ q := if b then chi⁻¹ else chi

def lwdSignedZero (rho : ℂ) (b : Bool) : ℂ := if b then conj rho else rho

theorem lwd_signed_nonprincipal {q : ℕ} (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1)
    (b : Bool) : lwdSignedCharacter chi b ≠ 1 := by
  cases b <;> simpa [lwdSignedCharacter] using hc

theorem lwd_signed_primitive {q : ℕ} (chi : DirichletCharacter ℂ q) (hp : chi.IsPrimitive)
    (b : Bool) : (lwdSignedCharacter chi b).IsPrimitive := by
  cases b
  · exact hp
  · exact BombieriVinogradov.DirichletCharacter.IsPrimitive.inv hp

theorem lwd_signed_zero {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) {rho : ℂ} (hz : chi.LFunction rho = 0) (b : Bool) :
    (lwdSignedCharacter chi b).LFunction (lwdSignedZero rho b) = 0 := by
  cases b
  · exact hz
  · simp only [lwdSignedCharacter, lwdSignedZero, if_true]
    rw [BombieriVinogradov.SiegelWalfisz.DirichletCharacter.LFunction_inv_eq_conj_conj hc,
      Complex.conj_conj, hz, map_zero]

theorem lwd_signed_re (rho : ℂ) (b : Bool) : (lwdSignedZero rho b).re = rho.re := by
  cases b <;> simp [lwdSignedZero]

theorem lwd_signed_height (rho : ℂ) (b : Bool) :
    |(lwdSignedZero rho b).im| = |rho.im| := by
  cases b <;> simp [lwdSignedZero]

theorem lwd_2_28_all_nonprincipal
    {d e f q : ℕ} [NeZero d] [NeZero e] [NeZero f] [NeZero q]
    {x : ℝ} (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (hdq : d ∣ q) (heq : e ∣ q) (hfq : f ∣ q)
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    (eta : DirichletCharacter ℂ f)
    (hc : chi ≠ 1) (hp : psi ≠ 1) (he : eta ≠ 1)
    (hpc : chi.IsPrimitive) (hpp : psi.IsPrimitive) (hpe : eta.IsPrimitive)
    (hcp : ∀ b, lwdProduct chi (lwdSignedCharacter psi b) ≠ 1)
    (hce : ∀ c, lwdProduct chi (lwdSignedCharacter eta c) ≠ 1)
    (hpe' : ∀ b c, lwdProduct (lwdSignedCharacter psi b) (lwdSignedCharacter eta c) ≠ 1)
    (hcpe : ∀ b c, lwdProduct (lwdProduct chi (lwdSignedCharacter psi b))
      (lwdSignedCharacter eta c) ≠ 1)
    {rho tau upsilon : ℂ}
    (hr : 1 / 2 < rho.re) (hr1 : rho.re < 1) (hzr : chi.LFunction rho = 0)
    (ht : 1 / 2 < tau.re) (ht1 : tau.re < 1) (hzt : psi.LFunction tau = 0)
    (hu : 1 / 2 < upsilon.re) (hu1 : upsilon.re < 1) (hzu : eta.LFunction upsilon = 0)
    (hyr : |rho.im| ≤ x / q) (hyt : |tau.im| ≤ x / q) (hyu : |upsilon.im| ≤ x / q) :
    0 ≤ 1 / (lwdSourceSigma x - 1) -
      (1 / (lwdSourceSigma x - rho.re) + 1 / (lwdSourceSigma x - tau.re) +
        1 / (lwdSourceSigma x - upsilon.re)) +
      7 * stechkinConductorCoeff * Real.log x + 2.4998 := by
  have hbound (b c : Bool) :
      lwdG chi (lwdSignedCharacter psi b) (lwdSignedCharacter eta c) (lwdSourceSigma x)
        rho.im (lwdSignedZero tau b).im (lwdSignedZero upsilon c).im ≤
        1 / (lwdSourceSigma x - 1) -
          (1 / (lwdSourceSigma x - rho.re) + 1 / (lwdSourceSigma x - tau.re) +
            1 / (lwdSourceSigma x - upsilon.re)) +
          7 * stechkinConductorCoeff * Real.log x + 2.4998 := by
    have hh := lwd_2_27_case_iv hx hq hdq heq hfq chi
      (lwdSignedCharacter psi b) (lwdSignedCharacter eta c) hc
      (lwd_signed_nonprincipal psi hp b) (lwd_signed_nonprincipal eta he c) hpc
      (lwd_signed_primitive psi hpp b) (lwd_signed_primitive eta hpe c)
      (hcp b) (hce c) (hpe' b c) (hcpe b c) hr hr1 hzr
      (show 1 / 2 < (lwdSignedZero tau b).re by rwa [lwd_signed_re])
      (show (lwdSignedZero tau b).re < 1 by rwa [lwd_signed_re])
      (lwd_signed_zero psi hp hzt b)
      (show 1 / 2 < (lwdSignedZero upsilon c).re by rwa [lwd_signed_re])
      (show (lwdSignedZero upsilon c).re < 1 by rwa [lwd_signed_re])
      (lwd_signed_zero eta he hzu c) hyr
      (show |(lwdSignedZero tau b).im| ≤ x / q by rwa [lwd_signed_height])
      (show |(lwdSignedZero upsilon c).im| ≤ x / q by rwa [lwd_signed_height])
    simpa only [lwd_signed_re] using hh
  have h0 := hbound false false
  have h1 := hbound true false
  have h2 := hbound false true
  have h3 := hbound true true
  simp only [lwdSignedCharacter, lwdSignedZero, Bool.false_eq_true, if_false, if_true, conj_im]
    at h0 h1 h2 h3
  have hpos := lwd_2_13 chi psi eta (lwd_source_parameters hx).2.2.1
    rho.im tau.im upsilon.im
  linarith only [hpos, h0, h1, h2, h3]

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1
