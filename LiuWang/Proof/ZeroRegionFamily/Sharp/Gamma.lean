import LiuWang.Proof.ZeroRegionFamily.Sharp.DigammaShift
import LiuWang.Proof.ZeroRegionFamily.StechkinKernel

/-! # Stechkin的实际奇偶Gamma差分费用：同域强于配套Lemma2.5 -/

set_option autoImplicit false
noncomputable section

open Complex
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.ZeroRegionFamily.Sharp

def stechkinConductorCoeff : ℝ := (1-stechkinK)/2

theorem stechkinSigma_sub_le {sigma : ℝ} (hs : 1 < sigma) :
    stechkinSigma sigma-sigma ≤ 2/3 := by
  have hsq := Real.sq_sqrt (show 0 ≤ 1+4*sigma^2 by positivity)
  have hp := Real.sqrt_nonneg (1+4*sigma^2)
  dsimp [stechkinSigma]
  nlinarith

theorem stechkinK_ge : 11/25 ≤ stechkinK := by
  have hr : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  dsimp [stechkinK]
  apply (le_div_iff₀ hr).mpr
  nlinarith

theorem digamma_difference_bound {a b : ℝ} (ha : 1/2 ≤ a) (ha1 : a ≤ 43/40)
    (hab : a ≤ b) (hgap : b-a ≤ 1/3) (y : ℝ) :
    (Complex.digamma ((a : ℂ)+Complex.I*y)).re-
      stechkinK*(Complex.digamma ((b : ℂ)+Complex.I*y)).re ≤
      (1-stechkinK)*Real.log (max 1 (2*|y|))+5/8-5*stechkinK/24 := by
  have href := digamma_one_re_le_log_max y
  have hu : (Complex.digamma ((a : ℂ)+Complex.I*y)).re ≤
      Real.log (max 1 (2*|y|))+5/8 := by
    by_cases hsmall : a ≤ 1
    · have hh := digamma_shift_down_le ha hsmall y
      norm_num only [Complex.ofReal_one] at hh
      linarith
    · have hh := digamma_shift_up_le (a := 1) (b := a) le_rfl (le_of_not_ge hsmall) y
      norm_num only [Complex.ofReal_one] at hh
      linarith
  have hshift := digamma_shift_down_le ha hab y
  have hk := stechkinK_mem
  have h1 := mul_le_mul_of_nonneg_left hu (sub_nonneg.mpr hk.2)
  have h2 := mul_le_mul_of_nonneg_left hshift hk.1
  have h3 := mul_le_mul_of_nonneg_left hgap hk.1
  nlinarith

def gammaDifferenceAt {q : ℕ} (chi : DirichletCharacter ℂ q) (sigma t : ℝ) : ℝ :=
  (logDeriv chi.gammaFactor ((sigma : ℂ)+Complex.I*t)).re-
    stechkinK*(logDeriv chi.gammaFactor ((stechkinSigma sigma : ℂ)+Complex.I*t)).re

theorem gammaDifference_even {q : ℕ} {chi : DirichletCharacter ℂ q}
    (he : chi.Even) {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    gammaDifferenceAt chi sigma t =
      -stechkinConductorCoeff*Real.log Real.pi+
      ((Complex.digamma (((sigma/2 : ℝ) : ℂ)+Complex.I*(t/2 : ℝ))).re-
        stechkinK*(Complex.digamma
          (((stechkinSigma sigma/2 : ℝ) : ℂ)+Complex.I*(t/2 : ℝ))).re)/2 := by
  have hs1 := hs.trans_le (stechkinSigma_ge hs)
  unfold gammaDifferenceAt
  rw [logDeriv_gammaFactor_of_even he (by simpa [Complex.mul_re] using (show 0 < sigma by linarith)),
    logDeriv_gammaFactor_of_even he
      (by simpa [Complex.mul_re] using (show 0 < stechkinSigma sigma by linarith))]
  have hhalf (u : ℝ) : ((u : ℂ)+Complex.I*t)/2 =
      (((u/2 : ℝ) : ℂ)+Complex.I*(t/2 : ℝ)) := by push_cast; ring
  rw [hhalf, hhalf]
  simp [stechkinConductorCoeff, Complex.mul_re]
  ring

theorem gammaDifference_odd {q : ℕ} {chi : DirichletCharacter ℂ q}
    (he : chi.Odd) {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    gammaDifferenceAt chi sigma t =
      -stechkinConductorCoeff*Real.log Real.pi+
      ((Complex.digamma ((((sigma+1)/2 : ℝ) : ℂ)+Complex.I*(t/2 : ℝ))).re-
        stechkinK*(Complex.digamma
          ((((stechkinSigma sigma+1)/2 : ℝ) : ℂ)+Complex.I*(t/2 : ℝ))).re)/2 := by
  have hs1 := hs.trans_le (stechkinSigma_ge hs)
  unfold gammaDifferenceAt
  rw [logDeriv_gammaFactor_of_odd he (by simpa [Complex.mul_re] using (show 0 < sigma by linarith)),
    logDeriv_gammaFactor_of_odd he
      (by simpa [Complex.mul_re] using (show 0 < stechkinSigma sigma by linarith))]
  have hhalf (u : ℝ) : (((u : ℂ)+Complex.I*t)+1)/2 =
      ((((u+1)/2 : ℝ) : ℂ)+Complex.I*(t/2 : ℝ)) := by push_cast; ring
  rw [hhalf, hhalf]
  simp [stechkinConductorCoeff, Complex.mul_re]
  ring

theorem gammaDifference_le {q : ℕ} (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) (t : ℝ) :
    gammaDifferenceAt chi sigma t ≤
      stechkinConductorCoeff*(Real.log (max 1 |t|)-Real.log Real.pi)+
        5/16-5*stechkinK/48 := by
  have hgap := stechkinSigma_sub_le hs
  have hge := stechkinSigma_ge hs
  have hlog : 2*|t/2|=|t| := by rw [abs_div]; norm_num; ring
  rcases chi.even_or_odd with he | ho
  · rw [gammaDifference_even he hs t]
    have hh := digamma_difference_bound (a := sigma/2) (b := stechkinSigma sigma/2)
      (by linarith) (by linarith) (by linarith) (by linarith) (t/2)
    rw [hlog] at hh
    dsimp [stechkinConductorCoeff]
    nlinarith
  · rw [gammaDifference_odd ho hs t]
    have hh := digamma_difference_bound (a := (sigma+1)/2) (b := (stechkinSigma sigma+1)/2)
      (by linarith) (by linarith) (by linarith) (by linarith) (t/2)
    rw [hlog] at hh
    dsimp [stechkinConductorCoeff]
    nlinarith

theorem gammaDifference_le_four_fifteenths {q : ℕ} (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) (t : ℝ) :
    gammaDifferenceAt chi sigma t ≤
      stechkinConductorCoeff*(Real.log (max 1 |t|)-Real.log Real.pi)+4/15 := by
  linarith [gammaDifference_le chi hs hs1 t, stechkinK_ge]

theorem gammaDifference_low {q : ℕ} (chi : DirichletCharacter ℂ q)
    {sigma t : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) (ht : |t| ≤ 1) :
    gammaDifferenceAt chi sigma t ≤ -stechkinConductorCoeff*Real.log Real.pi+4/15 := by
  simpa [max_eq_left ht] using gammaDifference_le_four_fifteenths chi hs hs1 t

theorem gammaDifference_high {q : ℕ} (chi : DirichletCharacter ℂ q)
    {sigma t : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) (ht : 1 ≤ |t|) :
    gammaDifferenceAt chi sigma t ≤
      stechkinConductorCoeff*(Real.log |t|-Real.log Real.pi)+4/15 := by
  simpa [max_eq_right ht] using gammaDifference_le_four_fifteenths chi hs hs1 t

theorem primitive_damped_bound {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) (hp : chi.IsPrimitive) {sigma : ℝ}
    (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) (t : ℝ) :
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK t ≤
      stechkinConductorCoeff*(Real.log q+Real.log (max 1 |t|)-Real.log Real.pi)+4/15 := by
  have hh := stechkin_without_zeros hc hp hs t
  have hg := gammaDifference_le_four_fifteenths chi hs hs1 t
  dsimp [gammaDifferenceAt, stechkinConductorCoeff] at hg ⊢
  linarith

end LiuWang.Proof.ZeroRegionFamily.Sharp
