import LiuWang.Proof.MajorZeroMomentPayment.Continuation.Defect

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.SingularIntegral

namespace LiuWang.Proof.MajorZeroMomentPayment.Continuation

def shiftedEnvelope (v w : ℝ) (D A B C : ℂ) : ℝ :=
  ‖D + A*v + B*(v : ℂ)^2 + C*(v : ℂ)^3‖ +
    ‖A + 2*B*v + 3*C*(v : ℂ)^2‖*w +
    ‖B + 3*C*v‖*w^2 + ‖C‖*w^3

theorem shifted_polynomial_bound {v w k : ℝ} (_hw : 0 ≤ w) (hk : 0 ≤ k)
    (D A B C X Y : ℂ) (hx : ‖X‖ ≤ k) (hy : ‖Y - v*X‖ ≤ k*w) :
    ‖D*X^3 + A*X^2*Y + B*X*Y^2 + C*Y^3‖ ≤
      k^3 * shiftedEnvelope v w D A B C := by
  have he :
      D*X^3 + A*X^2*Y + B*X*Y^2 + C*Y^3 =
      (D + A*v + B*(v : ℂ)^2 + C*(v : ℂ)^3)*X^3 +
      (A + 2*B*v + 3*C*(v : ℂ)^2)*X^2*(Y-v*X) +
      (B + 3*C*v)*X*(Y-v*X)^2 + C*(Y-v*X)^3 := by ring
  rw [he]
  calc
    _ ≤ ‖(D + A*v + B*(v : ℂ)^2 + C*(v : ℂ)^3)*X^3‖ +
        ‖(A + 2*B*v + 3*C*(v : ℂ)^2)*X^2*(Y-v*X)‖ +
        ‖(B + 3*C*v)*X*(Y-v*X)^2‖ + ‖C*(Y-v*X)^3‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add ((norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ ‖D + A*v + B*(v : ℂ)^2 + C*(v : ℂ)^3‖*k^3 +
        ‖A + 2*B*v + 3*C*(v : ℂ)^2‖*k^2*(k*w) +
        ‖B + 3*C*v‖*k*(k*w)^2 + ‖C‖*(k*w)^3 := by
      simp only [norm_mul, norm_pow]
      gcongr
    _ = _ := by unfold shiftedEnvelope; ring

def jointKernel (N : ℕ) (beta : ℝ) (D A B C : ℂ) (eta : ℝ) : ℂ :=
  D*tripleKernel N 1 1 1 eta + A*tripleKernel N 1 1 beta eta +
    B*tripleKernel N 1 beta beta eta + C*tripleKernel N beta beta beta eta

theorem jointKernel_integrable {N : ℕ} (hN : 0 < N) (beta : ℝ) (D A B C : ℂ) :
    Integrable (jointKernel N beta D A B C) :=
  ((((tripleKernel_integrable hN 1 1 1).const_mul D).add
    ((tripleKernel_integrable hN 1 1 beta).const_mul A)).add
    ((tripleKernel_integrable hN 1 beta beta).const_mul B)).add
    ((tripleKernel_integrable hN beta beta beta).const_mul C)

theorem jointKernel_shift_bound {N : ℕ} (hN : 0 < N) {beta : ℝ} (hb : beta ≤ 1)
    {k : ℝ} (hk : 0 ≤ k) (D A B C : ℂ) (eta : ℝ)
    (hx : ‖J N eta‖ ≤ k) (hy : ‖realDefect N beta eta‖ ≤ k * endpointGap N beta) :
    ‖jointKernel N beta D A B C eta‖ ≤
      k^3 * shiftedEnvelope (baseWeight N beta) (endpointGap N beta) D A B C := by
  have he : jointKernel N beta D A B C eta =
      charReal (-(N : ℝ)*eta) *
        (D*(J N eta)^3 + A*(J N eta)^2*Jrho N beta eta +
          B*(J N eta)*(Jrho N beta eta)^2 + C*(Jrho N beta eta)^3) := by
    simp only [jointKernel, tripleKernel, Jrho_one_eq_J]
    ring
  rw [he, norm_mul, charReal_norm, one_mul]
  exact shifted_polynomial_bound (endpointGap_nonneg hN hb) hk D A B C
    (J N eta) (Jrho N beta eta) hx hy

theorem jointKernel_integral_norm_shift {N : ℕ} (hN : 0 < N) {beta : ℝ} (hb : beta ≤ 1)
    (D A B C : ℂ) :
    (∫ eta : ℝ, ‖jointKernel N beta D A B C eta‖) ≤
      (3 / Real.pi) * (N : ℝ)^2 *
        shiftedEnvelope (baseWeight N beta) (endpointGap N beta) D A B C := by
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have ha : 0 < 1 / (Real.pi * (N : ℝ)) := by positivity
  have hm (eta : ℝ) : ‖J N eta‖ ≤ (N : ℝ) := by
    simpa only [Complex.ofReal_one, Jrho_one_eq_J, realEndpoint, sub_self,
      Real.rpow_zero, mul_one] using Jrho_real_mass hN (beta := 1) le_rfl eta
  have hr (eta : ℝ) (he : eta ≠ 0) : ‖J N eta‖ ≤ 1 / (Real.pi * |eta|) := by
    simpa only [Complex.ofReal_one, Jrho_one_eq_J, Complex.one_re, sub_self, Real.rpow_zero]
      using OscillatoryBounds.Jrho_real_reciprocal hN (rho := 1) le_rfl (by simp) he
  have h := integral_norm_core_tail (jointKernel_integrable hN beta D A B C) ha
    (B := (N : ℝ)^3 * shiftedEnvelope (baseWeight N beta) (endpointGap N beta) D A B C)
    (C := shiftedEnvelope (baseWeight N beta) (endpointGap N beta) D A B C / Real.pi^3)
    (fun eta => jointKernel_shift_bound hN hb hn.le D A B C eta (hm eta) (realDefect_mass hN hb eta))
    (fun eta he => by
      have he' := abs_pos.mp (ha.trans he)
      have hdef : ‖realDefect N beta eta‖ ≤
          (1 / (Real.pi * |eta|)) * endpointGap N beta := by
        simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using realDefect_reciprocal hN hb he'
      apply (jointKernel_shift_bound hN hb (by positivity : 0 ≤ 1 / (Real.pi * |eta|))
        D A B C eta (hr eta he') hdef).trans_eq
      ring)
  apply h.trans_eq
  field_simp
  ring

theorem jointFinite_shift_lower {N : ℕ} (hN : 0 < N) {beta : ℝ} (hb : beta ≤ 1)
    {delta : ℝ} (hd : 0 ≤ delta) (D A B C : ℂ) :
    -(3 / Real.pi) * (N : ℝ)^2 *
      shiftedEnvelope (baseWeight N beta) (endpointGap N beta) D A B C ≤
        (jointFinite N delta beta D A B C).re := by
  have hnorm : ‖jointFinite N delta beta D A B C‖ ≤
      (3 / Real.pi) * (N : ℝ)^2 *
        shiftedEnvelope (baseWeight N beta) (endpointGap N beta) D A B C := by
    rw [jointFinite_eq_integral hN]
    exact (finite_norm_le_integral_norm (jointKernel_integrable hN beta D A B C) hd).trans
      (jointKernel_integral_norm_shift hN hb D A B C)
  have h := Complex.re_le_norm (-jointFinite N delta beta D A B C)
  rw [Complex.neg_re, norm_neg] at h
  linarith

theorem shiftedEnvelope_at_one (N : ℕ) (D A B C : ℂ) :
    shiftedEnvelope (baseWeight N 1) (endpointGap N 1) D A B C = ‖D + A + B + C‖ := by
  simp [shiftedEnvelope, baseWeight, endpointGap, realEndpoint]

theorem jointFinite_shift_lower_decimal {N : ℕ} (hN : 0 < N) {beta : ℝ} (hb : beta ≤ 1)
    {delta : ℝ} (hd : 0 ≤ delta) (D A B C : ℂ) :
    -0.955 * (N : ℝ)^2 *
      shiftedEnvelope (baseWeight N beta) (endpointGap N beta) D A B C ≤
        (jointFinite N delta beta D A B C).re := by
  have hc : (3 : ℝ) / Real.pi ≤ 0.955 := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    nlinarith [Real.pi_gt_d4]
  have henv : 0 ≤ shiftedEnvelope (baseWeight N beta) (endpointGap N beta) D A B C := by
    have hw := endpointGap_nonneg hN hb
    unfold shiftedEnvelope
    positivity
  have hh := mul_le_mul_of_nonneg_right hc (mul_nonneg (sq_nonneg (N : ℝ)) henv)
  linarith [jointFinite_shift_lower hN hb hd D A B C]

end LiuWang.Proof.MajorZeroMomentPayment.Continuation
