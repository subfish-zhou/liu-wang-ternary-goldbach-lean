import LiuWang.Proof.Campaign20260915.ZetaMordell.ClosedForm
import LiuWang.Proof.Campaign20260915.ZetaValidation.RiemannSiegelPhiBounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Filter Set
open scoped Real Topology

namespace LiuWang.Proof.Campaign20260915.ZetaMordell

open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem siegelIntegral_analytic (u : ℂ) : AnalyticAt ℂ siegelIntegral u := by
  have h : Differentiable ℂ (siegelMoment 0) := fun z => (siegelMoment_hasDerivAt 0 z).differentiableAt
  rw [siegelMoment_zero] at h
  exact h.analyticAt u

theorem correctionIntegral_analytic (z : ℂ) : AnalyticAt ℂ correctionIntegral z := by
  have hp : AnalyticAt ℂ correctionFactor z := by
    unfold correctionFactor
    apply AnalyticAt.cexp
    fun_prop
  have hs : AnalyticAt ℂ (fun w : ℂ => siegelIntegral (w + 1 / 2)) z :=
    (siegelIntegral_analytic _).comp (by fun_prop)
  exact (hp.mul hs).congr (Eventually.of_forall (fun w => (correctionIntegral_normalization w).symm))

theorem correctionIntegral_cos_identity (z : ℂ) :
    correctionIntegral z * Complex.cos (Real.pi * z) =
      Complex.cos (Real.pi * z ^ 2 / 2 + 3 * Real.pi / 8) := by
  have hd (v : ℂ) : exp (Real.pi * I * v) - exp (-Real.pi * I * v) =
      2 * I * Complex.sin (Real.pi * v) := by
    unfold Complex.sin
    rw [show -(Real.pi * v) * I = -Real.pi * I * v by ring,
      show Real.pi * v * I = Real.pi * I * v by ring]
    ring_nf
    simp only [I_sq]
    ring
  have hden : exp (Real.pi * I * (z + 1 / 2)) - exp (-Real.pi * I * (z + 1 / 2)) =
      2 * I * Complex.cos (Real.pi * z) := by
    rw [hd, show Real.pi * (z + 1 / 2) = Real.pi * z + Real.pi / 2 by ring,
      Complex.sin_add_pi_div_two]
  have hnum : correctionFactor z *
      (exp (Real.pi * I * (z + 1 / 2)) - exp (Real.pi * I * (z + 1 / 2) ^ 2)) =
      2 * I * Complex.cos (Real.pi * z ^ 2 / 2 + 3 * Real.pi / 8) := by
    unfold correctionFactor
    rw [mul_sub, ← exp_add, ← exp_add,
      show Real.pi * z ^ 2 / 2 + 3 * Real.pi / 8 =
        Real.pi / 2 - (Real.pi / 8 - Real.pi * z ^ 2 / 2) by ring,
      Complex.cos_pi_div_two_sub]
    unfold Complex.sin
    rw [show Real.pi * I * (1 / 8 - (z + 1) ^ 2 / 2) + Real.pi * I * (z + 1 / 2) =
      (Real.pi / 8 - Real.pi * z ^ 2 / 2) * I by ring,
      show Real.pi * I * (1 / 8 - (z + 1) ^ 2 / 2) + Real.pi * I * (z + 1 / 2) ^ 2 =
      -(Real.pi / 8 - Real.pi * z ^ 2 / 2) * I by ring]
    ring_nf
    simp only [I_sq]
    ring
  apply mul_left_cancel₀ (show (2 * I : ℂ) ≠ 0 by simp)
  calc
    2 * I * (correctionIntegral z * Complex.cos (Real.pi * z)) =
      correctionFactor z * (siegelIntegral (z + 1 / 2) *
        (exp (Real.pi * I * (z + 1 / 2)) - exp (-Real.pi * I * (z + 1 / 2)))) := by
          rw [correctionIntegral_normalization, hden]
          ring
    _ = _ := by rw [siegelIntegral_closed_identity, hnum]

theorem correctionIntegral_eq_rsPhi {z : ℝ} (hz : |z| < 3 / 2) :
    correctionIntegral (z : ℂ) = (rsPhi z : ℂ) := by
  let U : Set ℝ := Ioo (-3 / 2) (3 / 2)
  have hC (x : ℝ) : AnalyticAt ℝ (fun y : ℝ => correctionIntegral (y : ℂ)) x :=
    ((correctionIntegral_analytic (x : ℂ)).restrictScalars (𝕜 := ℝ)).comp
      (Complex.ofRealCLM.analyticAt x)
  have hf : AnalyticOnNhd ℝ (fun x : ℝ => correctionIntegral (x : ℂ) - (rsPhi x : ℂ)) U := by
    intro x hx
    have hx' : |x| < 3 / 2 := abs_lt.mpr (by simpa [U, neg_div] using hx)
    exact (hC x).sub ((Complex.ofRealCLM.analyticAt _).comp (rsPhi_analytic hx'))
  have hg : AnalyticOnNhd ℝ (fun x : ℝ => (Real.cos (Real.pi * x) : ℂ)) U := by
    intro x _
    apply (Complex.ofRealCLM.analyticAt _).comp
    exact Real.analyticAt_cos.comp (by fun_prop)
  have he := hf.eq_zero_or_eq_zero_of_mul_eq_zero hg (fun x hx => by
    have hc := correctionIntegral_cos_identity (x : ℂ)
    have hp := congrArg Complex.ofReal
      (rsPhi_cos_identity (z := x) (abs_lt.mpr (by simpa [U, neg_div] using hx)))
    push_cast at hp
    rw [show Real.pi * (4 * (x : ℂ) ^ 2 + 3) / 8 =
      Real.pi * (x : ℂ) ^ 2 / 2 + 3 * Real.pi / 8 by ring] at hp
    rw [Complex.ofReal_cos, Complex.ofReal_mul]
    linear_combination hc - hp) (convex_Ioo (-3 / 2 : ℝ) (3 / 2)).isPreconnected
  rcases he with he | he
  · exact sub_eq_zero.mp (he z (by simpa [U, neg_div] using abs_lt.mp hz))
  · have h0 := he 0 (by norm_num [U])
    norm_num at h0

theorem correctionIntegral_iteratedDeriv_eq_rsPhi (n : ℕ) {z : ℝ} (hz : |z| < 3 / 2) :
    iteratedDeriv n correctionIntegral (z : ℂ) = ((iteratedDeriv n rsPhi z : ℝ) : ℂ) := by
  induction n generalizing z with
  | zero => simpa using correctionIntegral_eq_rsPhi hz
  | succ n ih =>
    have he : (fun x : ℝ => iteratedDeriv n correctionIntegral (x : ℂ)) =ᶠ[𝓝 z]
        fun x : ℝ => ((iteratedDeriv n rsPhi x : ℝ) : ℂ) := by
      filter_upwards [isOpen_Ioo.mem_nhds (abs_lt.mp hz)] with x hx
      exact ih (abs_lt.mpr hx)
    have hc : HasDerivAt (fun x : ℝ => iteratedDeriv n correctionIntegral (x : ℂ))
        (iteratedDeriv (n + 1) correctionIntegral (z : ℂ)) z := by
      rw [iteratedDeriv_succ]
      have h := ((correctionIntegral_analytic (z : ℂ)).iterated_deriv n).differentiableAt.hasDerivAt.comp_ofReal
      simpa only [iteratedDeriv_eq_iterate] using h
    have hp : HasDerivAt (fun x : ℝ => ((iteratedDeriv n rsPhi x : ℝ) : ℂ))
        ((iteratedDeriv (n + 1) rsPhi z : ℝ) : ℂ) z := by
      rw [iteratedDeriv_succ]
      have h := (rsPhi_iterated_deriv_analytic hz n).differentiableAt.hasDerivAt.ofReal_comp
      simpa only [iteratedDeriv_eq_iterate] using h
    exact hc.deriv.symm.trans (he.deriv_eq.trans hp.deriv)

theorem correctionIntegral_third_deriv_phiOne {z : ℝ} (hz : |z| < 3 / 2) :
    iteratedDeriv 3 correctionIntegral (z : ℂ) / (12 * Real.pi ^ 2) = (rsPhiOne z : ℂ) := by
  rw [correctionIntegral_iteratedDeriv_eq_rsPhi 3 hz]
  simp only [rsPhiOne, ofReal_div, ofReal_mul, ofReal_ofNat, ofReal_pow]

theorem correctionIntegral_derivs_phiTwo {z : ℝ} (hz : |z| < 3 / 2) :
    iteratedDeriv 2 correctionIntegral (z : ℂ) / (16 * Real.pi ^ 2) +
      iteratedDeriv 6 correctionIntegral (z : ℂ) / (288 * Real.pi ^ 4) = (rsPhiTwo z : ℂ) := by
  rw [correctionIntegral_iteratedDeriv_eq_rsPhi 2 hz, correctionIntegral_iteratedDeriv_eq_rsPhi 6 hz]
  simp only [rsPhiTwo, ofReal_add, ofReal_div, ofReal_mul, ofReal_ofNat, ofReal_pow]

end LiuWang.Proof.Campaign20260915.ZetaMordell
