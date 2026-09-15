import LiuWang.Proof.MajorZeroInteraction.Consumer
import LiuWang.Proof.OscillatoryBounds.Consumer

/-! Finite-radius triple moments. Both tails and all three endpoint variations
are paid before the full-axis singular-integral identity is used. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MeasureTheory Set
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.SingularIntegral LiuWang.Proof.SingularSeries

namespace LiuWang.Proof.MajorZeroMomentPayment

def tripleKernel (N : ℕ) (r s t : ℂ) (eta : ℝ) : ℂ :=
  charReal (-(N : ℝ) * eta) * Jrho N r eta * Jrho N s eta * Jrho N t eta

def finiteMoment (N : ℕ) (delta : ℝ) (r s t : ℂ) : ℂ :=
  ∫ eta in -delta..delta, tripleKernel N r s t eta

def fullMoment (N : ℕ) (r s t : ℂ) : ℂ :=
  ∫ eta : ℝ, tripleKernel N r s t eta

theorem tripleKernel_integrable {N : ℕ} (hN : 0 < N) (r s t : ℂ) :
    Integrable (tripleKernel N r s t) :=
  Jrho_triple_integrable hN r s t

theorem continuous_tripleKernel {N : ℕ} (hN : 0 < N) (r s t : ℂ) :
    Continuous (tripleKernel N r s t) :=
  (((charReal_continuous.comp (continuous_const.mul continuous_id)).mul
    (Jrho_continuous hN r)).mul (Jrho_continuous hN s)).mul (Jrho_continuous hN t)

theorem two_sided_tail {f : ℝ → ℂ} (hf : Integrable f) {delta C : ℝ}
    (hd : 0 < delta) (hb : ∀ eta, delta < |eta| → ‖f eta‖ ≤ C / |eta|^3) :
    ‖(∫ eta : ℝ, f eta) - (∫ eta in -delta..delta, f eta)‖ ≤ C / delta^2 := by
  have hr := norm_integral_Ioi_le_inv_cube hf hd (C := C) (by
    intro eta he
    simpa only [abs_of_pos (hd.trans he)] using hb eta
      (by simpa only [abs_of_pos (hd.trans he)] using he))
  have hl := norm_integral_Ioi_le_inv_cube hf.comp_neg hd (C := C) (by
    intro eta he
    simpa only [abs_neg, abs_of_pos (hd.trans he)] using hb (-eta)
      (by simpa only [abs_neg, abs_of_pos (hd.trans he)] using he))
  rw [integral_comp_neg_Ioi] at hl
  rw [integral_sub_interval_eq_tails hf hd.le]
  exact (norm_add_le _ _).trans ((add_le_add hl hr).trans_eq (by ring))

theorem norm_tripleKernel_le_variation {N : ℕ} (hN : 0 < N) (r s t : ℂ)
    {eta : ℝ} (he : eta ≠ 0) :
    ‖tripleKernel N r s t eta‖ ≤
      weightVariation N r * weightVariation N s * weightVariation N t / |eta|^3 := by
  have hb (rho : ℂ) : ‖Jrho N rho eta‖ ≤ weightVariation N rho / |eta| :=
    (le_div_iff₀ (abs_pos.mpr he)).mpr
      (by simpa only [mul_comm] using Jrho_abs_mul_norm_le_variation hN rho eta)
  have hv (rho : ℂ) : 0 ≤ weightVariation N rho / |eta| :=
    div_nonneg (weightVariation_nonneg N rho) (abs_nonneg eta)
  simp only [tripleKernel, norm_mul, charReal_norm, one_mul]
  calc
    _ ≤ (weightVariation N r / |eta|) * (weightVariation N s / |eta|) *
        (weightVariation N t / |eta|) := by
      gcongr
      · exact mul_nonneg (hv r) (hv s)
      · exact hv r
      · exact hb r
      · exact hb s
      · exact hb t
    _ = _ := by ring

theorem moment_tail_variation {N : ℕ} (hN : 0 < N) (r s t : ℂ)
    {delta : ℝ} (hd : 0 < delta) :
    ‖fullMoment N r s t - finiteMoment N delta r s t‖ ≤
      weightVariation N r * weightVariation N s * weightVariation N t / delta^2 := by
  exact two_sided_tail (tripleKernel_integrable hN r s t) hd
    (fun eta he => norm_tripleKernel_le_variation hN r s t
      (abs_pos.mp (hd.trans he)))

def realEndpoint (N : ℕ) (beta : ℝ) : ℝ :=
  (0.001 * (N : ℝ)) ^ (beta - 1)

theorem norm_real_tripleKernel {N : ℕ} (hN : 0 < N) {r s t : ℝ}
    (hr : r ≤ 1) (hs : s ≤ 1) (ht : t ≤ 1) {eta : ℝ} (he : eta ≠ 0) :
    ‖tripleKernel N r s t eta‖ ≤
      (realEndpoint N r * realEndpoint N s * realEndpoint N t / Real.pi^3) /
        |eta|^3 := by
  have hb (beta : ℝ) (hbeta : beta ≤ 1) :
      ‖Jrho N beta eta‖ ≤ realEndpoint N beta / (Real.pi * |eta|) := by
    exact OscillatoryBounds.Jrho_real_reciprocal hN
      (by simpa only [Complex.ofReal_re] using hbeta) (by simp) he
  have hv (beta : ℝ) : 0 ≤ realEndpoint N beta / (Real.pi * |eta|) := by
    unfold realEndpoint
    positivity
  simp only [tripleKernel, norm_mul, charReal_norm, one_mul]
  calc
    _ ≤ (realEndpoint N r / (Real.pi * |eta|)) *
        (realEndpoint N s / (Real.pi * |eta|)) *
        (realEndpoint N t / (Real.pi * |eta|)) := by
      gcongr
      · exact mul_nonneg (hv r) (hv s)
      · exact hv r
      · exact hb r hr
      · exact hb s hs
      · exact hb t ht
    _ = _ := by ring

theorem moment_tail_real {N : ℕ} (hN : 0 < N) {r s t : ℝ}
    (hr : r ≤ 1) (hs : s ≤ 1) (ht : t ≤ 1) {delta : ℝ} (hd : 0 < delta) :
    ‖fullMoment N r s t - finiteMoment N delta r s t‖ ≤
      realEndpoint N r * realEndpoint N s * realEndpoint N t /
        (Real.pi^3 * delta^2) := by
  have h := two_sided_tail (tripleKernel_integrable hN (r : ℂ) (s : ℂ) (t : ℂ)) hd
    (fun eta he => norm_real_tripleKernel hN hr hs ht (abs_pos.mp (hd.trans he)))
  simpa only [div_div, fullMoment, finiteMoment] using h

theorem fullMoment_eq_simplex {N : ℕ} (hN : 0 < N) (r s t : ℂ) :
    fullMoment N r s t =
      (N : ℂ)^2 * ∫ x in sourceSimplex,
        (((N : ℝ) * x.1 : ℝ) : ℂ)^(r - 1) *
        (((N : ℝ) * x.2 : ℝ) : ℂ)^(s - 1) *
        (((N : ℝ) * (1 - x.1 - x.2) : ℝ) : ℂ)^(t - 1) :=
  integral_Jrho_triple_eq_sourceSimplex hN r s t

theorem actual_radius_tail_real {N q : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    (hq : 0 < q) {r s t : ℝ} (hr : r ≤ 1) (hs : s ≤ 1) (ht : t ≤ 1) :
    ‖fullMoment N r s t - finiteMoment N (deltaRadius N q) r s t‖ ≤
      (100 / (3.36^2 * Real.pi)) * ((q : ℝ) / sourceP N)^2 * (N : ℝ)^2 *
        (realEndpoint N r * realEndpoint N s * realEndpoint N t) := by
  apply (moment_tail_real (nat_pos_of_exp_le hN) hr hs ht (deltaRadius_pos hN hq)).trans_eq
  unfold deltaRadius
  field_simp
  ring

end LiuWang.Proof.MajorZeroMomentPayment
