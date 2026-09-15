import LiuWang.Proof.Campaign20260915.ZetaValidation.CountingPrimitive
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaWinding

open LiuWang.Proof.Campaign20260915.ZetaValidation

def localXiPrimitive (c s : ℂ) : ℂ :=
  log (c * riemannZeta s) + log s + log (s - 1) +
    gammaLogBranch (s / 2) - s / 2 * (Real.log Real.pi : ℂ)

theorem rotated_re_pos_of_ball {w z c : ℂ} {r : ℝ}
    (he : ‖w - z‖ ≤ r) (hm : ‖c‖ * r < (c * z).re) :
    0 < (c * w).re := by
  have hn : ‖c * (w - z)‖ ≤ ‖c‖ * r := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left he (norm_nonneg c)
  have hr := neg_norm_le_re (c * (w - z))
  rw [mul_sub] at hn
  rw [mul_sub, sub_re] at hr
  linarith

theorem rotated_log_increment_integer {c u v : ℂ}
    (hc : c ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ k : ℤ, log (c * v) - log (c * u) =
      log v - log u + (k : ℂ) * (2 * Real.pi * I) := by
  apply exp_eq_exp_iff_exists_int.mp
  rw [exp_sub, exp_sub, exp_log (mul_ne_zero hc hv),
    exp_log (mul_ne_zero hc hu), exp_log hv, exp_log hu]
  exact mul_div_mul_left v u hc

theorem localXiPrimitive_increment_integer {c u v : ℂ}
    (hc : c ≠ 0) (hu : riemannZeta u ≠ 0) (hv : riemannZeta v ≠ 0) :
    ∃ k : ℤ, localXiPrimitive c v - localXiPrimitive c u =
      xiCountingPrimitive v - xiCountingPrimitive u +
        (k : ℂ) * (2 * Real.pi * I) := by
  obtain ⟨k, hk⟩ := rotated_log_increment_integer hc hu hv
  refine ⟨k, ?_⟩
  dsimp [localXiPrimitive, xiCountingPrimitive]
  linear_combination hk

theorem localXiPrimitive_hasDerivAt {c s : ℂ} (hs : 0 < s.re)
    (hslit : s - 1 ∈ slitPlane) (hz : 0 < (c * riemannZeta s).re) :
    HasDerivAt (localXiPrimitive c) (logDeriv riemannXi s) s := by
  have hcz := ne_zero_of_re_pos hz
  have hc : c ≠ 0 := left_ne_zero_of_mul hcz
  have hsz : riemannZeta s ≠ 0 := right_ne_zero_of_mul hcz
  have hs0 : s ≠ 0 := ne_zero_of_re_pos hs
  have hs1 : s ≠ 1 := by
    intro he
    simp [he] at hslit
  have hlz := ((differentiableAt_riemannZeta hs1).hasDerivAt.const_mul c).clog
    (mem_slitPlane_iff.mpr (Or.inl hz))
  have hls := hasDerivAt_log (mem_slitPlane_iff.mpr (Or.inl hs))
  have hl1 := ((hasDerivAt_id s).sub_const 1).clog hslit
  have hg : HasDerivAt (fun w : ℂ => gammaLogBranch (w / 2))
      ((1 / 2 : ℂ) * digamma (s / 2)) s := by
    have h := LiuWang.Proof.DirichletZeroCount.Remainder.logGamma_hasDerivAt
      (z := s / 2) (by simpa using half_pos hs)
    simpa only [gammaLogBranch, LiuWang.Proof.DirichletZeroCount.Remainder.logGamma,
      Function.comp_def, id_eq, mul_comm] using! h.comp s ((hasDerivAt_id s).div_const 2)
  have hd := (((hlz.add hls).add hl1).add hg).sub
    (((hasDerivAt_id s).div_const 2).mul_const (Real.log Real.pi : ℂ))
  have hx := LiuWang.Proof.PrincipalPsi.Quantitative.logDeriv_xi_eq_zeta
    (by linarith : -2 < s.re) hs1 hsz
  have hgam : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m he
    have hr := congrArg Complex.re he
    simp only [div_ofNat_re, neg_re, natCast_re] at hr
    linarith [Nat.cast_nonneg m (α := ℝ)]
  rw [digamma_apply_add_one (s / 2) hgam] at hx
  have hder : c * deriv riemannZeta s / (c * riemannZeta s) + s⁻¹ +
      1 / (s - 1) + (1 / 2 : ℂ) * digamma (s / 2) -
        (1 / 2 : ℂ) * (Real.log Real.pi : ℂ) = logDeriv riemannXi s := by
    rw [hx, logDeriv_apply]
    field_simp
    ring
  change HasDerivAt (localXiPrimitive c)
    (c * deriv riemannZeta s / (c * riemannZeta s) + s⁻¹ + 1 / (s - 1) +
      1 / 2 * digamma (s / 2) - 1 / 2 * (Real.log Real.pi : ℂ)) s at hd
  rw [hder] at hd
  exact hd

theorem xi_line_integrable {a b : ℝ} (z v : ℂ)
    (hn : ∀ t ∈ Set.uIcc a b, riemannXi (z + (t : ℂ) * v) ≠ 0) :
    IntervalIntegrable (fun t : ℝ => v * logDeriv riemannXi (z + (t : ℂ) * v))
      volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have ha := differentiable_riemannXi.analyticAt (z + (t : ℂ) * v)
  have hc := (ha.deriv.div ha (hn t ht)).continuousAt.comp
    (f := fun x : ℝ => z + (x : ℂ) * v) (by fun_prop)
  simpa only [logDeriv_apply, Function.comp_def, Pi.div_apply, Pi.mul_apply] using!
    ((continuousAt_const (y := v)).mul hc).continuousWithinAt

theorem localXiPrimitive_line_integral {a b : ℝ} {z v c : ℂ}
    (hs : ∀ t ∈ Set.uIcc a b, 0 < (z + (t : ℂ) * v).re)
    (hslit : ∀ t ∈ Set.uIcc a b, z + (t : ℂ) * v - 1 ∈ slitPlane)
    (hz : ∀ t ∈ Set.uIcc a b, 0 < (c * riemannZeta (z + (t : ℂ) * v)).re) :
    (∫ t in a..b, v * logDeriv riemannXi (z + (t : ℂ) * v)) =
      localXiPrimitive c (z + (b : ℂ) * v) -
        localXiPrimitive c (z + (a : ℂ) * v) := by
  have hn : ∀ t ∈ Set.uIcc a b, riemannXi (z + (t : ℂ) * v) ≠ 0 := by
    intro t ht hx
    have hs1 : z + (t : ℂ) * v ≠ 1 := by
      intro he
      simpa [he] using hslit t ht
    have h := (LiuWang.Proof.PrincipalPsi.Quantitative.xi_zero_iff_zeta_zero
      (by linarith [hs t ht] : -2 < (z + (t : ℂ) * v).re) hs1).mp hx
    simpa [h] using hz t ht
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (xi_line_integrable z v hn)
  intro t ht
  have hd := localXiPrimitive_hasDerivAt (hs t ht) (hslit t ht) (hz t ht)
  simpa only [LiuWang.Proof.DirichletZeroCount.Argument.linePoint,
    Function.comp_def, smul_eq_mul] using
    hd.scomp t (LiuWang.Proof.DirichletZeroCount.Argument.line_hasDerivAt z v t)

#print axioms rotated_re_pos_of_ball
#print axioms rotated_log_increment_integer
#print axioms localXiPrimitive_line_integral

end LiuWang.Proof.Campaign20260915.ZetaWinding
