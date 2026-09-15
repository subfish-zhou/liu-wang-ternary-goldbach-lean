import LiuWang.Proof.Campaign20260915.ZetaValidation.AbelEvaluation
import LiuWang.Proof.Campaign20260915.ZetaValidation.CriticalLine

set_option autoImplicit false
noncomputable section

open Complex
open scoped ComplexConjugate

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def criticalGammaNorm (t : ℝ) : ℝ := ‖Gammaℝ (criticalPoint t)‖

def normalizedCriticalZeta (t : ℝ) : ℝ :=
  criticalCompletedZeta t / criticalGammaNorm t

def criticalGammaPhase (t : ℝ) : ℂ :=
  Gammaℝ (criticalPoint t) / (criticalGammaNorm t : ℂ)

theorem criticalGammaNorm_pos (t : ℝ) : 0 < criticalGammaNorm t :=
  norm_pos_iff.mpr (Gammaℝ_ne_zero_of_re_pos (by norm_num [criticalPoint]))

theorem norm_criticalGammaPhase (t : ℝ) : ‖criticalGammaPhase t‖ = 1 := by
  rw [criticalGammaPhase, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (criticalGammaNorm_pos t)]
  exact div_self (criticalGammaNorm_pos t).ne'

theorem normalizedCriticalZeta_ofReal (t : ℝ) :
    (normalizedCriticalZeta t : ℂ) =
      riemannZeta (criticalPoint t) * criticalGammaPhase t := by
  rw [normalizedCriticalZeta, ofReal_div, criticalCompletedZeta_ofReal,
    criticalGammaPhase, riemannZeta_def_of_ne_zero (criticalPoint_ne_zero t)]
  field_simp [Gammaℝ_ne_zero_of_re_pos (by norm_num [criticalPoint] :
    0 < (criticalPoint t).re)]

theorem abs_normalizedCriticalZeta (t : ℝ) :
    |normalizedCriticalZeta t| = ‖riemannZeta (criticalPoint t)‖ := by
  have h := congrArg norm (normalizedCriticalZeta_ofReal t)
  simpa only [Complex.norm_real, Real.norm_eq_abs, norm_mul,
    norm_criticalGammaPhase, mul_one] using h

theorem normalizedCriticalZeta_neg_iff (t : ℝ) :
    normalizedCriticalZeta t < 0 ↔ criticalCompletedZeta t < 0 := by
  change criticalCompletedZeta t / criticalGammaNorm t < 0 ↔ _
  rw [div_lt_iff₀ (criticalGammaNorm_pos t), zero_mul]

theorem normalized_abel_error (t : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    |normalizedCriticalZeta t - (abelApprox (criticalPoint t) N * criticalGammaPhase t).re| ≤
      ‖criticalPoint t‖ * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have he : normalizedCriticalZeta t -
      (abelApprox (criticalPoint t) N * criticalGammaPhase t).re =
      ((riemannZeta (criticalPoint t) - abelApprox (criticalPoint t) N) *
        criticalGammaPhase t).re := by
    rw [sub_mul, sub_re, ← normalizedCriticalZeta_ofReal, ofReal_re]
  rw [he]
  have h := norm_zeta_sub_abelApprox_le (s := criticalPoint t)
    (by norm_num [criticalPoint]) (criticalPoint_ne_one t) hN
  calc
    _ ≤ ‖(riemannZeta (criticalPoint t) - abelApprox (criticalPoint t) N) *
        criticalGammaPhase t‖ := abs_re_le_norm _
    _ = ‖riemannZeta (criticalPoint t) - abelApprox (criticalPoint t) N‖ := by
      rw [norm_mul, norm_criticalGammaPhase, mul_one]
    _ ≤ _ := by simpa [criticalPoint] using h

theorem criticalGammaPhase_zero : criticalGammaPhase 0 = 1 := by
  let g : ℝ := Real.pi ^ (-(1 / 4 : ℝ)) * Real.Gamma (1 / 4)
  have hg : 0 < g :=
    mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by norm_num))
  have hp : criticalPoint 0 = (1 / 2 : ℂ) := by
    apply Complex.ext <;> norm_num [criticalPoint]
  have hG : Gammaℝ (criticalPoint 0) = (g : ℂ) := by
    rw [hp, Gammaℝ_def]
    norm_num only [show -(1 / 2 : ℂ) / 2 = -(1 / 4) by norm_num,
      show (1 / 2 : ℂ) / 2 = 1 / 4 by norm_num]
    dsimp [g]
    push_cast
    rw [Complex.ofReal_cpow Real.pi_pos.le]
    rw [← Complex.Gamma_ofReal (1 / 4 : ℝ)]
    norm_num
  rw [criticalGammaPhase, criticalGammaNorm, hG,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hg]
  exact div_self (Complex.ofReal_ne_zero.mpr hg.ne')

theorem normalizedCriticalZeta_zero_eq :
    normalizedCriticalZeta 0 = (riemannZeta (criticalPoint 0)).re := by
  have h := congrArg Complex.re (normalizedCriticalZeta_ofReal 0)
  simpa only [ofReal_re, criticalGammaPhase_zero, mul_one] using h

theorem endpoint_zero_rational_enclosure :
    -(2 : ℝ) ≤ normalizedCriticalZeta 0 ∧ normalizedCriticalZeta 0 ≤ -1 := by
  have h := normalized_abel_error 0 (N := 1) (by norm_num)
  have hp : criticalPoint 0 = (1 / 2 : ℂ) := by
    apply Complex.ext <;> norm_num [criticalPoint]
  norm_num [hp, abelApprox, zetaPartialSum, criticalGammaPhase_zero] at h
  constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]

theorem endpoint_zero_strict_sign : criticalCompletedZeta 0 < 0 := by
  apply (normalizedCriticalZeta_neg_iff 0).mp
  linarith [endpoint_zero_rational_enclosure.2]

#print axioms normalized_abel_error
#print axioms endpoint_zero_rational_enclosure
#print axioms endpoint_zero_strict_sign

end LiuWang.Proof.Campaign20260915.ZetaValidation
