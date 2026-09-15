import LiuWang.Proof.SourceRoute.MajorException.RealWeight
import LiuWang.Proof.MajorZeroMomentPayment.Continuation.Uniform

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.SingularIntegral
open LiuWang.Proof.MajorZeroMomentPayment
open LiuWang.Proof.MajorZeroMomentPayment.Continuation

namespace LiuWang.Proof.SourceRoute.MajorException

theorem norm_triple_repeated (N : ℕ) (rho : ℂ) (eta : ℝ) :
    ‖tripleKernel N rho rho rho eta‖ = ‖Jrho N rho eta‖^3 := by
  simp only [tripleKernel, norm_mul, charReal_norm, one_mul]
  ring

theorem Jrho_cube_integrable {N : ℕ} (hN : 0 < N) (rho : ℂ) :
    Integrable (fun eta => ‖Jrho N rho eta‖^3) := by
  simpa only [norm_triple_repeated] using
    (tripleKernel_integrable hN rho rho rho).norm

theorem Jrho_cubic_mass_tail {N : ℕ} (hN : 0 < N) (rho : ℂ)
    {A D : ℝ} (hA : 0 < A) (hD : 0 < D)
    (hm : ∀ eta, ‖Jrho N rho eta‖ ≤ A)
    (ht : ∀ eta, eta ≠ 0 → ‖Jrho N rho eta‖ ≤ D / |eta|) :
    (∫ eta : ℝ, ‖Jrho N rho eta‖^3) ≤ 3 * A^2 * D := by
  have h := integral_norm_core_tail (tripleKernel_integrable hN rho rho rho)
    (div_pos hD hA) (B := A^3) (C := D^3)
    (fun eta => by rw [norm_triple_repeated]; gcongr; exact hm eta)
    (fun eta he => by
      rw [norm_triple_repeated, ← div_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (ht eta (abs_pos.mp ((div_pos hD hA).trans he))) 3)
  simp only [norm_triple_repeated] at h
  apply h.trans_eq
  field_simp
  ring

theorem finite_Jrho_cube_le_full {N : ℕ} (hN : 0 < N) (rho : ℂ)
    {delta : ℝ} (hd : 0 ≤ delta) :
    (∫ eta in -delta..delta, ‖Jrho N rho eta‖^3) ≤
      ∫ eta : ℝ, ‖Jrho N rho eta‖^3 := by
  rw [intervalIntegral.integral_of_le (by linarith : -delta ≤ delta)]
  exact setIntegral_le_integral (Jrho_cube_integrable hN rho)
    (Filter.Eventually.of_forall (fun eta => by positivity))

theorem J_cubic_source {N : ℕ} (hN : 0 < N) {delta : ℝ} (hd : 0 ≤ delta) :
    (∫ eta in -delta..delta, ‖J N eta‖^3) ≤
      (2.994006 / Real.pi) * (N : ℝ)^2 := by
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have h := Jrho_cubic_mass_tail hN 1
    (A := 0.999 * (N : ℝ)) (D := 1 / Real.pi) (by positivity) (by positivity)
    (fun eta => by simpa only [Jrho_one_eq_J] using OscillatoryBounds.J_length N eta)
    (fun eta he => by
      simpa only [Jrho_one_eq_J, div_div] using OscillatoryBounds.J_reciprocal N he)
  have hfinite := (finite_Jrho_cube_le_full hN 1 hd).trans h
  simp only [Jrho_one_eq_J] at hfinite
  apply hfinite.trans
  calc
    _ = 2.994003 * ((N : ℝ)^2 / Real.pi) := by ring
    _ ≤ 2.994006 * ((N : ℝ)^2 / Real.pi) :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = _ := by ring

theorem Jrho_cubic_source_full {N : ℕ} (hN : 0 < N) {beta : ℝ}
    (hb : 0.9957 ≤ beta) (hb1 : beta ≤ 1) :
    (∫ eta : ℝ, ‖Jrho N (beta : ℂ) eta‖^3) ≤
      (3 * 1.0302 * 1.0033^2 / Real.pi) * (N : ℝ)^(3 * beta - 1) := by
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have h := Jrho_cubic_mass_tail hN (beta : ℂ)
    (A := 1.0033 * (N : ℝ)^beta)
    (D := 1.0302 * (N : ℝ)^(beta - 1) / Real.pi)
    (by positivity) (by positivity) (Jrho_source_mass hN hb hb1)
    (fun eta he => by simpa only [div_div] using Jrho_source_reciprocal hN hb hb1 he)
  apply h.trans_eq
  rw [mul_pow, ← Real.rpow_mul_natCast hn.le]
  have hp : (N : ℝ)^(beta * 2) * (N : ℝ)^(beta - 1) =
      (N : ℝ)^(3 * beta - 1) := by
    rw [← Real.rpow_add hn]
    congr 1
    ring
  calc
    _ = (3 * 1.0302 * 1.0033^2 / Real.pi) *
        ((N : ℝ)^(beta * 2) * (N : ℝ)^(beta - 1)) := by ring
    _ = _ := by rw [hp]

theorem Jrho_cubic_source {N : ℕ} (hN : 0 < N) {beta delta : ℝ}
    (hb : 0.9957 ≤ beta) (hb1 : beta ≤ 1) (hd : 0 ≤ delta) :
    (∫ eta in -delta..delta, ‖Jrho N (beta : ℂ) eta‖^3) ≤
      (3 * 1.0302 * 1.0033^2 / Real.pi) * (N : ℝ)^(3 * beta - 1) :=
  (finite_Jrho_cube_le_full hN beta hd).trans (Jrho_cubic_source_full hN hb hb1)

end LiuWang.Proof.SourceRoute.MajorException
