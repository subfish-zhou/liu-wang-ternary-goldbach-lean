import LiuWang.Proof.Campaign20260915.ZetaWinding.UncompensatedXi

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Filter

namespace LiuWang.Proof.Campaign20260915.ZetaWinding

open LiuWang.Proof.PrincipalPsi
open LiuWang.Proof.PrincipalPsi.Quantitative
open LiuWang.Proof.DirichletZeroCount.Argument

def lehmanGammaLog (T x : ℝ) : ℝ :=
  Real.log ‖Gamma (horizontalAt T x / 2 + 1) /
    Gamma (horizontalAt T (x + 1) / 2 + 1)‖

def lehmanPoleLog (T x : ℝ) : ℝ :=
  Real.log ‖horizontalAt T x / (horizontalAt T x - 1)‖

theorem xi_log_norm_zeta_factors {s : ℂ} (hs : -2 < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s ≠ 0) :
    Real.log ‖riemannXi s‖ = -s.re / 2 * Real.log Real.pi +
      Real.log ‖Gamma (s / 2 + 1)‖ + Real.log ‖s - 1‖ + Real.log ‖riemannZeta s‖ := by
  have hg : Gamma (s / 2 + 1) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hp : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (.inl (by exact_mod_cast Real.pi_ne_zero))
  rw [xi_eq_factor_regularized hs, regularizedPrincipal_eq hs1,
    DirichletCharacter.LFunction_modOne_eq, norm_mul,
    Real.log_mul (norm_ne_zero_iff.mpr (xiFactor_ne_zero hs))
      (norm_ne_zero_iff.mpr (mul_ne_zero (sub_ne_zero.mpr hs1) hz)),
    norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hs1))
      (norm_ne_zero_iff.mpr hz)]
  unfold xiFactor
  rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hp) (norm_ne_zero_iff.mpr hg),
    norm_cpow_eq_rpow_re_of_pos Real.pi_pos, Real.log_rpow Real.pi_pos]
  simp only [div_ofNat_re, neg_re]
  ring

theorem lehman_zeta_factor_ratio {T x : ℝ} (hT : T ≠ 0) (hx : 1 / 2 ≤ x)
    (hz : riemannZeta (horizontalAt T x) ≠ 0) :
    Real.log ‖riemannZeta (horizontalAt T x) /
      riemannZeta (horizontalAt T (x + 1))‖ =
      Real.log ‖riemannXi (horizontalAt T x) /
        riemannXi (horizontalAt T (x + 1))‖ -
      lehmanGammaLog T x + lehmanPoleLog T x - Real.log Real.pi / 2 := by
  let s := horizontalAt T x
  let w := horizontalAt T (x + 1)
  have hs : -2 < s.re := by simp [s, horizontalAt]; linarith
  have hw : 1 < w.re := by simp [w, horizontalAt]; linarith
  have hn (y : ℝ) : horizontalAt T y ≠ 1 := by
    intro he
    exact hT (by simpa [horizontalAt] using congrArg Complex.im he)
  have hs0 : s ≠ 0 := by intro he; have hh := congrArg Complex.re he; simp [s, horizontalAt] at hh; linarith
  have hzn : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hw
  have hxn : riemannXi s ≠ 0 := (xi_zero_iff_zeta_zero hs (hn x)).not.mpr hz
  have hwn : riemannXi w ≠ 0 :=
    (xi_zero_iff_zeta_zero (by linarith) (hn (x + 1))).not.mpr hzn
  have hg : Gamma (s / 2 + 1) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp [s, horizontalAt]; linarith)
  have hgw : Gamma (w / 2 + 1) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp [w, horizontalAt]; linarith)
  have ha := xi_log_norm_zeta_factors hs (hn x) hz
  have hb := xi_log_norm_zeta_factors (by linarith : -2 < w.re) (hn (x + 1)) hzn
  have hws : w - 1 = s := by dsimp [w, s, horizontalAt]; push_cast; ring
  change Real.log ‖riemannZeta s / riemannZeta w‖ =
    Real.log ‖riemannXi s / riemannXi w‖ -
      Real.log ‖Gamma (s / 2 + 1) / Gamma (w / 2 + 1)‖ +
        Real.log ‖s / (s - 1)‖ - Real.log Real.pi / 2
  rw [norm_div, Real.log_div (norm_ne_zero_iff.mpr hz) (norm_ne_zero_iff.mpr hzn),
    norm_div, Real.log_div (norm_ne_zero_iff.mpr hxn) (norm_ne_zero_iff.mpr hwn),
    norm_div, Real.log_div (norm_ne_zero_iff.mpr hg) (norm_ne_zero_iff.mpr hgw),
    norm_div, Real.log_div (norm_ne_zero_iff.mpr hs0)
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hn x)))]
  rw [hws] at hb
  have hsr : s.re = x := by simp [s, horizontalAt]
  have hwr : w.re = x + 1 := by simp [w, horizontalAt]
  rw [hsr] at ha
  rw [hwr] at hb
  linear_combination hb - ha

theorem lehmanGammaLog_continuousOn (T : ℝ) :
    ContinuousOn (lehmanGammaLog T) (Set.Ici (1 / 2 : ℝ)) := by
  intro x hx
  have hx' : 1 / 2 ≤ x := hx
  have hg (u : ℝ) (hu : 1 / 2 ≤ u) :
      0 < (horizontalAt T u / 2 + 1).re := by simp [horizontalAt]; linarith
  have hc (u : ℝ) (hu : 1 / 2 ≤ u) :
      ContinuousAt (fun y => Gamma (horizontalAt T y / 2 + 1)) u :=
    (differentiableAt_Gamma _ (fun n => by
      intro he
      have hh := hg u hu
      rw [he] at hh
      simp at hh
      linarith [Nat.cast_nonneg (α := ℝ) n])).continuousAt.comp
        (by unfold horizontalAt; fun_prop)
  have hd : ContinuousAt (fun y => Gamma (horizontalAt T (y + 1) / 2 + 1)) x :=
    (hc (x + 1) (by linarith)).comp (f := fun y : ℝ => y + 1) (by fun_prop)
  exact (((hc x hx').div hd (Gamma_ne_zero_of_re_pos (hg _ (by linarith)))).norm.log
    (norm_ne_zero_iff.mpr (div_ne_zero (Gamma_ne_zero_of_re_pos (hg x hx'))
      (Gamma_ne_zero_of_re_pos (hg _ (by linarith)))))).continuousWithinAt

theorem lehmanGammaLog_integrable (T : ℝ) :
    IntervalIntegrable (lehmanGammaLog T) volume (1 / 2) (3 / 2) :=
  ((lehmanGammaLog_continuousOn T).mono (by
    intro x hx
    exact (Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 3 / 2) ▸ hx).1)).intervalIntegrable

theorem lehmanPoleLog_integrable (T : ℝ) :
    IntervalIntegrable (lehmanPoleLog T) volume (1 / 2) (3 / 2) := by
  apply MeromorphicOn.intervalIntegrable_log_norm
  intro x _
  have h : AnalyticAt ℝ (horizontalAt T) x := (ofRealCLM.analyticAt x).add analyticAt_const
  exact h.meromorphicAt.div (h.sub analyticAt_const).meromorphicAt

theorem zeta_lehman_unit_shift_integral {T : ℝ} (hT : T ≠ 0) :
    (∫ x in (1 / 2 : ℝ)..(3 / 2),
      Real.log ‖riemannZeta (horizontalAt T x) /
        riemannZeta (horizontalAt T (x + 1))‖) =
      (∑' p : RiemannXiDivisorZeroIndex,
        ∫ x in (1 / 2 : ℝ)..(3 / 2),
          Real.log ‖(horizontalAt T x - riemannXiDivisorZeroValue p) /
            (horizontalAt T (x + 1) - riemannXiDivisorZeroValue p)‖) -
      (∫ x in (1 / 2 : ℝ)..(3 / 2), lehmanGammaLog T x) +
      (∫ x in (1 / 2 : ℝ)..(3 / 2), lehmanPoleLog T x) - Real.log Real.pi / 2 := by
  have hix : IntervalIntegrable
      (fun x => Real.log ‖riemannXi (horizontalAt T x) / riemannXi (horizontalAt T (x + 1))‖)
      volume (1 / 2) (3 / 2) := by
    apply MeromorphicOn.intervalIntegrable_log_norm
    intro x _
    have h : AnalyticAt ℝ (horizontalAt T) x := (ofRealCLM.analyticAt x).add analyticAt_const
    have hw : AnalyticAt ℝ (fun y => horizontalAt T (y + 1)) x := by
      simpa only [horizontalAt, ofReal_add, ofReal_one] using!
        (((ofRealCLM.analyticAt x).add (analyticAt_const (v := (1 : ℂ)))).add
          (analyticAt_const (v := (T : ℂ) * I)))
    exact (((differentiable_riemannXi.analyticAt _).restrictScalars (𝕜 := ℝ)).comp h).meromorphicAt.div
      (((differentiable_riemannXi.analyticAt _).restrictScalars (𝕜 := ℝ)).comp hw).meromorphicAt
  have hae : ∀ᵐ x : ℝ, x ∈ Set.uIoc (1 / 2 : ℝ) (3 / 2) →
      Real.log ‖riemannZeta (horizontalAt T x) / riemannZeta (horizontalAt T (x + 1))‖ =
        Real.log ‖riemannXi (horizontalAt T x) / riemannXi (horizontalAt T (x + 1))‖ -
          lehmanGammaLog T x + lehmanPoleLog T x - Real.log Real.pi / 2 := by
    filter_upwards [xi_horizontal_ne_zero_ae T] with x hx hxI
    have hx' : 1 / 2 ≤ x := (Set.uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 3 / 2) ▸ hxI).1.le
    have hs : -2 < (horizontalAt T x).re := by simp [horizontalAt]; linarith
    have hn : horizontalAt T x ≠ 1 := by
      intro he
      exact hT (by simpa [horizontalAt] using congrArg Complex.im he)
    exact lehman_zeta_factor_ratio hT hx' ((xi_zero_iff_zeta_zero hs hn).not.mp hx)
  rw [intervalIntegral.integral_congr_ae hae,
    intervalIntegral.integral_sub ((hix.sub (lehmanGammaLog_integrable T)).add
      (lehmanPoleLog_integrable T)) intervalIntegrable_const,
    intervalIntegral.integral_add (hix.sub (lehmanGammaLog_integrable T))
      (lehmanPoleLog_integrable T),
    intervalIntegral.integral_sub hix (lehmanGammaLog_integrable T),
    xi_lehman_uncompensated_series, intervalIntegral.integral_const]
  norm_num

theorem horizontalLogMass_lehman_zero_series {T : ℝ} (hT : T ≠ 0) :
    horizontalLogMass T =
      (∑' p : RiemannXiDivisorZeroIndex,
        ∫ x in (1 / 2 : ℝ)..(3 / 2),
          Real.log ‖(horizontalAt T x - riemannXiDivisorZeroValue p) /
            (horizontalAt T (x + 1) - riemannXiDivisorZeroValue p)‖) -
      (∫ x in (1 / 2 : ℝ)..(3 / 2), lehmanGammaLog T x) +
      (∫ x in (1 / 2 : ℝ)..(3 / 2), lehmanPoleLog T x) - Real.log Real.pi / 2 +
      (∫ x in Set.Ioi (3 / 2 : ℝ), Real.log ‖riemannZeta (horizontalAt T x)‖) +
      (∫ x in (3 / 2 : ℝ)..(5 / 2), Real.log ‖riemannZeta (horizontalAt T x)‖) := by
  rw [lehman_shift_one_identity hT, zeta_lehman_unit_shift_integral hT]

#print axioms xi_log_norm_zeta_factors
#print axioms lehman_zeta_factor_ratio
#print axioms zeta_lehman_unit_shift_integral
#print axioms horizontalLogMass_lehman_zero_series

end LiuWang.Proof.Campaign20260915.ZetaWinding
