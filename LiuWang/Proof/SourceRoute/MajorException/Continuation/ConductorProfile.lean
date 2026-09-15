import LiuWang.Proof.SourceRoute.MajorException.Continuation.PaidMass
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation

def decayPower : PureKind → ℝ
  | .linear => 3/2
  | .quadratic => 1
  | .cubic => 1/2

def zeroPower : PureKind → ℝ
  | .linear => 1
  | .quadratic => 2
  | .cubic => 3

def gammaFactor : ℝ := Real.exp Real.eulerMascheroniConstant
def nu (r : ℝ) : ℝ :=
  gammaFactor * Real.log (Real.log r) + 2.50637 / Real.log (Real.log r)

def paperDomain (r L : ℝ) : Prop := 987 ≤ r ∧ 3100 ≤ L ∧ r ≤ L^3

def conductorScalar (j : PureKind) (r L : ℝ) : ℝ :=
  r^(-decayPower j) * nu r^2 *
    Real.exp (-(zeroPower j*Real.pi*L)/(0.4923*Real.sqrt r*(Real.log r)^2))

def logNu (t : ℝ) : ℝ := gammaFactor * Real.log t + 2.50637 / Real.log t
def logNuD (t : ℝ) : ℝ := gammaFactor/t - 2.50637/(t*(Real.log t)^2)
def logNuDD (t : ℝ) : ℝ :=
  -gammaFactor/t^2 + 2.50637*(Real.log t+2)/(t^2*(Real.log t)^3)
def attenuation (t : ℝ) : ℝ := Real.exp (-t/2)/t^2
def attenuationSlope (t : ℝ) : ℝ := 1/2+2/t
def attenuationCurve (t : ℝ) : ℝ := 1/4+2/t+6/t^2
def zeroScale (j : PureKind) (L : ℝ) : ℝ := zeroPower j*Real.pi*L/0.4923

def conductorProfile (j : PureKind) (L t : ℝ) : ℝ :=
  Real.exp (-decayPower j*t) * logNu t^2 *
    Real.exp (-zeroScale j L*attenuation t)

def profileLogDerivative (j : PureKind) (L t : ℝ) : ℝ :=
  -decayPower j + 2*logNuD t/logNu t +
    zeroScale j L*attenuation t*attenuationSlope t

theorem gammaFactor_lower : (3/2 : ℝ) ≤ gammaFactor := by
  have h := Real.add_one_le_exp Real.eulerMascheroniConstant
  have hg := Real.one_half_lt_eulerMascheroniConstant
  dsimp [gammaFactor]
  linarith

theorem logNu_pos {t : ℝ} (ht : 1 < t) : 0 < logNu t := by
  have hl := Real.log_pos ht
  dsimp [logNu, gammaFactor]
  positivity

theorem logNu_hasDerivAt {t : ℝ} (ht : 1 < t) :
    HasDerivAt logNu (logNuD t) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl0 := (Real.log_pos ht).ne'
  apply (((Real.hasDerivAt_log ht0).const_mul gammaFactor).add
    ((hasDerivAt_const t (2.50637 : ℝ)).div (Real.hasDerivAt_log ht0) hl0)).congr_deriv
  dsimp [logNuD]
  field_simp
  ring

theorem logNuD_hasDerivAt {t : ℝ} (ht : 1 < t) :
    HasDerivAt logNuD (logNuDD t) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl0 := (Real.log_pos ht).ne'
  apply (((hasDerivAt_const t gammaFactor).div (hasDerivAt_id t) ht0).sub
    ((hasDerivAt_const t (2.50637 : ℝ)).div
      ((hasDerivAt_id t).mul ((Real.hasDerivAt_log ht0).pow 2))
      (mul_ne_zero ht0 (pow_ne_zero 2 hl0)))).congr_deriv
  dsimp [logNuDD]
  field_simp
  ring

theorem attenuation_hasDerivAt {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt attenuation (-attenuation t*attenuationSlope t) t := by
  apply (((((hasDerivAt_id t).neg.div_const 2).exp).div
    ((hasDerivAt_id t).pow 2) (pow_ne_zero 2 ht))).congr_deriv
  dsimp [attenuation, attenuationSlope]
  field_simp
  ring

theorem attenuationSlope_hasDerivAt {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt attenuationSlope (-2/t^2) t := by
  apply (((hasDerivAt_const t (2 : ℝ)).div (hasDerivAt_id t) ht).const_add (1/2)).congr_deriv
  dsimp
  ring

theorem profile_hasDerivAt (j : PureKind) (L : ℝ) {t : ℝ} (ht : 1 < t) :
    HasDerivAt (conductorProfile j L)
      (profileLogDerivative j L t * conductorProfile j L t) t := by
  have ht0 : t ≠ 0 := by linarith
  have hv := (logNu_pos ht).ne'
  apply (((((hasDerivAt_id t).const_mul (-decayPower j)).exp).mul
    ((logNu_hasDerivAt ht).pow 2)).mul
    (((attenuation_hasDerivAt ht0).const_mul (-zeroScale j L)).exp)).congr_deriv
  dsimp [profileLogDerivative, conductorProfile]
  field_simp

theorem profileLogDerivative_hasDerivAt (j : PureKind) (L : ℝ) {t : ℝ} (ht : 1 < t) :
    HasDerivAt (profileLogDerivative j L)
      (2*(logNuDD t*logNu t-logNuD t^2)/logNu t^2 -
        zeroScale j L*attenuation t*attenuationCurve t) t := by
  have ht0 : t ≠ 0 := by linarith
  have hv := (logNu_pos ht).ne'
  apply (((((logNuD_hasDerivAt ht).const_mul 2).div
    (logNu_hasDerivAt ht) hv).const_add (-decayPower j)).add
    (((attenuation_hasDerivAt ht0).const_mul (zeroScale j L)).mul
      (attenuationSlope_hasDerivAt ht0))).congr_deriv
  dsimp [attenuationSlope, attenuationCurve]
  field_simp
  ring

theorem profile_pos (j : PureKind) (L : ℝ) {t : ℝ} (ht : 1 < t) :
    0 < conductorProfile j L t := by
  dsimp [conductorProfile]
  exact mul_pos (mul_pos (Real.exp_pos _) (sq_pos_of_pos (logNu_pos ht))) (Real.exp_pos _)

theorem profile_log_hasDerivAt (j : PureKind) (L : ℝ) {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun u => Real.log (conductorProfile j L u))
      (profileLogDerivative j L t) t := by
  apply ((profile_hasDerivAt j L ht).log (profile_pos j L ht).ne').congr_deriv
  exact mul_div_cancel_right₀ _ (profile_pos j L ht).ne'

theorem scalar_eq_profile (j : PureKind) {r : ℝ} (hr : 0 < r) (L : ℝ) :
    conductorScalar j r L = conductorProfile j L (Real.log r) := by
  have hs : Real.sqrt r = Real.exp (Real.log r/2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hr]
    congr 1
    ring
  have hp : r^(-decayPower j) = Real.exp (-decayPower j*Real.log r) := by
    rw [Real.rpow_def_of_pos hr, mul_comm]
  simp only [conductorScalar, conductorProfile, nu, logNu, hp]
  congr 1
  congr 1
  rw [hs]
  dsimp [zeroScale, attenuation]
  rw [show -Real.log r/2 = -(Real.log r/2) by ring, Real.exp_neg]
  ring

theorem scalar_antitone_L (j : PureKind) {r : ℝ} (hr : 1 < r) :
    Antitone (conductorScalar j r) := by
  intro L M hLM
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hk : 0 ≤ zeroPower j := by cases j <;> norm_num [zeroPower]
  nlinarith [mul_le_mul_of_nonneg_left hLM (mul_nonneg hk Real.pi_pos.le)]

theorem paperDomain_log_iff {r L : ℝ} (hr : 0 < r) (hL : 0 < L) :
    paperDomain r L ↔ Real.log 987 ≤ Real.log r ∧
      3100 ≤ L ∧ Real.log r ≤ 3*Real.log L := by
  unfold paperDomain
  rw [← Real.log_le_log_iff (by norm_num : (0 : ℝ) < 987) hr,
    ← Real.log_le_log_iff hr (pow_pos hL 3), Real.log_pow]
  norm_num

end LiuWang.Proof.SourceRoute.MajorException.Continuation
