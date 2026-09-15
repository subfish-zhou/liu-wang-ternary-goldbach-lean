import LiuWang.Proof.Campaign20260915.ZetaValidation.HankelExpandedSource
import LiuWang.Proof.Campaign20260915.ZetaValidation.GammaStirlingPhase

set_option autoImplicit false
noncomputable section
open Complex
open scoped ComplexConjugate

namespace LiuWang.Proof.Campaign20260915.ZetaRealNormalization
open LiuWang.Proof.Campaign20260915.ZetaValidation

def sourceChi (s : ℂ) : ℂ :=
  (2 * Real.pi : ℂ) ^ s / (2 * Gamma s * cos (Real.pi * s / 2))

def sourceRealMainSum (t : ℝ) (m : ℕ) : ℝ :=
  2 * ∑ n ∈ Finset.range m,
    ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
      Real.cos (criticalGammaArgument t - t * Real.log (n + 1))

theorem criticalPoint_conj (t : ℝ) : conj (criticalPoint t) = 1 - criticalPoint t := by
  apply Complex.ext <;> norm_num [criticalPoint]

theorem sourceChi_critical (t : ℝ) :
    sourceChi (criticalPoint t) =
      conj (Gammaℝ (criticalPoint t)) / Gammaℝ (criticalPoint t) := by
  have h := Gammaℝ_div_Gammaℝ_one_sub (s := criticalPoint t) (by
    intro n hn
    have hr := congrArg Complex.re hn
    norm_num [criticalPoint] at hr
    linarith [Nat.cast_nonneg (α := ℝ) n])
  have hi := congrArg (fun z : ℂ => z⁻¹) h
  rw [inv_div, Gammaℂ_def, cpow_neg] at hi
  rw [← criticalPoint_conj,
    BombieriVinogradov.SiegelWalfisz.Complex.Gammaℝ_conj] at hi
  rw [sourceChi, hi]
  simp only [mul_inv_rev, inv_inv, div_eq_mul_inv]
  ring

theorem sourceChi_mul_phase (t : ℝ) :
    sourceChi (criticalPoint t) * criticalGammaPhase t = conj (criticalGammaPhase t) := by
  rw [sourceChi_critical, criticalGammaPhase, map_div₀, conj_ofReal]
  field_simp [Gammaℝ_ne_zero_of_re_pos (by norm_num [criticalPoint] :
    0 < (criticalPoint t).re)]

theorem critical_inverse_power_conj {x : ℝ} (hx : 0 < x) (t : ℝ) :
    (x : ℂ) ^ (criticalPoint t - 1) =
      conj (1 / (x : ℂ) ^ criticalPoint t) := by
  have he : criticalPoint t - 1 = -(conj (criticalPoint t)) := by
    rw [criticalPoint_conj]
    ring
  rw [he, cpow_neg, cpow_conj _ _ (by
    rw [arg_ofReal_of_nonneg hx.le]
    exact Real.pi_ne_zero.symm)]
  simp

theorem critical_inverse_power_phase {x : ℝ} (hx : 0 < x) (t : ℝ) :
    1 / (x : ℂ) ^ criticalPoint t * criticalGammaPhase t =
      ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        exp (((criticalGammaArgument t - t * Real.log x : ℝ) : ℂ) * I) := by
  rw [criticalGammaPhase_eq_exp_argument, one_div,
    cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), ← exp_neg, ← exp_add,
    Real.rpow_def_of_pos hx, ofReal_exp, ← exp_add]
  congr 1
  rw [← ofReal_log hx.le]
  apply Complex.ext <;> simp [criticalPoint, mul_re, mul_im]
  ring

theorem source_sums_normalized (t : ℝ) (m : ℕ) :
    ((∑ n ∈ Finset.range m, 1 / (n + 1 : ℂ) ^ criticalPoint t) +
      sourceChi (criticalPoint t) *
        (∑ n ∈ Finset.range m, (n + 1 : ℂ) ^ (criticalPoint t - 1))) *
        criticalGammaPhase t = (sourceRealMainSum t m : ℂ) := by
  have hc :
      (∑ n ∈ Finset.range m, (n + 1 : ℂ) ^ (criticalPoint t - 1)) =
        conj (∑ n ∈ Finset.range m, 1 / (n + 1 : ℂ) ^ criticalPoint t) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro n _
    exact_mod_cast critical_inverse_power_conj (by positivity : 0 < (n + 1 : ℝ)) t
  rw [hc, add_mul]
  have hp (A : ℂ) :
      sourceChi (criticalPoint t) * conj A * criticalGammaPhase t =
        conj (A * criticalGammaPhase t) := by
    rw [map_mul, ← sourceChi_mul_phase]
    ring
  rw [hp, Complex.add_conj]
  congr 1
  rw [Finset.sum_mul, re_sum]
  unfold sourceRealMainSum
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  have hn := critical_inverse_power_phase (by positivity : 0 < (n + 1 : ℝ)) t
  push_cast at hn
  rw [hn]
  simp [exp_re]

theorem normalizedCriticalZeta_expanded {m : ℕ} (hm : 0 < m)
    {t R : ℝ} (ht : 0 < t) (hR : (m : ℝ) < R) (hR' : R < m + 1) :
    normalizedCriticalZeta t = sourceRealMainSum t m +
      (rsHankelPrefactor (criticalPoint t) *
        rsHankelTiltedC1 (criticalPoint t) m (Real.log R) * criticalGammaPhase t).re := by
  have hz := zeta_eq_source_sums_add_expanded_hankel hm
    (show 0 < (criticalPoint t).im from ht) hR hR'
  have he := normalizedCriticalZeta_ofReal t
  rw [hz, add_mul, ← sourceChi, source_sums_normalized] at he
  exact_mod_cast congrArg Complex.re he

theorem hankel_phase_exact {t : ℝ} (ht : 0 < t) :
    rsHankelPrefactor (criticalPoint t) * criticalGammaPhase t =
      conj (criticalGammaPhase t) /
        (exp (Real.pi * I * criticalPoint t) - 1) := by
  have hj : exp (Real.pi * I * criticalPoint t) - 1 ≠ 0 := by
    intro h
    have hs := rsHankel_jump_ne_zero (show 0 < (criticalPoint t).im from ht)
    apply hs
    have he := sub_eq_zero.mp h
    rw [show 2 * Real.pi * I * criticalPoint t =
      Real.pi * I * criticalPoint t + Real.pi * I * criticalPoint t by ring, exp_add, he]
    ring
  apply (eq_div_iff hj).mpr
  rw [show rsHankelPrefactor (criticalPoint t) * criticalGammaPhase t *
      (exp (Real.pi * I * criticalPoint t) - 1) =
    (rsHankelPrefactor (criticalPoint t) *
      (exp (Real.pi * I * criticalPoint t) - 1)) * criticalGammaPhase t by ring,
    rsHankel_second_prefactor (show 0 < (criticalPoint t).im from ht)]
  exact sourceChi_mul_phase t

#print axioms source_sums_normalized
#print axioms normalizedCriticalZeta_expanded
#print axioms hankel_phase_exact

end LiuWang.Proof.Campaign20260915.ZetaRealNormalization
