import LiuWang.Proof.Campaign20260915.ZetaLowWindowCertificate.LowHeightRemainder
import LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.FiniteEvaluator
import LiuWang.Proof.Campaign20260915.ZetaRealNormalization.SourceSums

set_option autoImplicit false
noncomputable section
open Complex Finset

namespace LiuWang.Proof.Campaign20260915.ZetaLowWindowCertificate

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator
open LiuWang.Proof.Campaign20260915.ZetaRealNormalization

def emCorrection (s : ℂ) (N m : ℕ) : ℂ :=
  (N : ℂ) ^ (1 - s) / (s - 1) - (N : ℂ) ^ (-s) / 2 +
    ∑ j ∈ range m, risingProduct s (j + 1) *
      ((bernoulli (j + 2) : ℂ) / (j + 2).factorial) *
        (N : ℂ) ^ (-s - (j + 1 : ℕ))

theorem eulerMaclaurinApprox_eq_partialSum_add_correction (s : ℂ) (N m : ℕ) :
    eulerMaclaurinApprox s N m = zetaPartialSum s N + emCorrection s N m := by
  rw [eulerMaclaurinApprox_eq_sum]
  unfold abelApprox emCorrection
  ring

theorem critical_partialSum_re_eq_half_mainSum (t : ℝ) (N : ℕ) :
    (zetaPartialSum (criticalPoint t) N * criticalGammaPhase t).re =
      finiteMainSum t N / 2 := by
  simp only [zetaPartialSum, sum_mul, re_sum, finiteMainSum, sum_div]
  apply sum_congr rfl
  intro j _
  have hp := critical_inverse_power_phase (x := (j + 1 : ℝ)) (by positivity) t
  push_cast at hp
  rw [cpow_neg, ← one_div, hp]
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, exp_ofReal_mul_I_re,
    sourceTerm, Nat.cast_add, Nat.cast_one]
  rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, ← one_div]
  have hc : Real.cos (criticalGammaArgument t - t * Real.log (j + 1)) =
      Real.cos (t * Real.log (j + 1) - criticalGammaArgument t) := by
    rw [← Real.cos_neg (t * Real.log (j + 1) - criticalGammaArgument t)]
    congr 1
    ring
  rw [hc]
  ring

def lowEMCorrection (t : ℝ) : ℝ :=
  (emCorrection (criticalPoint t) (lowPrefix t) 63 * criticalGammaPhase t).re

theorem low_normalized_finiteMainSum_error {t : ℝ} (ht : |t| ≤ 12600) :
    |normalizedCriticalZeta t -
      (finiteMainSum t (lowPrefix t) / 2 + lowEMCorrection t)| ≤
        1 / 1000000000000000000 := by
  have he := low_normalized_order64_remainder ht
  rw [eulerMaclaurinApprox_eq_partialSum_add_correction, add_mul, add_re,
    critical_partialSum_re_eq_half_mainSum] at he
  exact he

theorem low_evaluate_error {D : ℕ} (hD : 1 ≤ D) (cache : ℕ → SharedEntry)
    {t : ℝ} (htlo : |t| ≤ 12600)
    (hcache : ∀ n, 1 ≤ n → n ≤ lowPrefix t → EntryValid n (cache n))
    {t₀ θ₀ dt dθ : ℚ}
    (ht : |t - (t₀ : ℝ)| ≤ (dt : ℝ))
    (hθ : |criticalGammaArgument t - (θ₀ : ℝ)| ≤ (dθ : ℝ))
    (hfit : ∀ n, 1 ≤ n → n ≤ lowPrefix t → PhaseFits (cache n) t₀ θ₀) :
    |normalizedCriticalZeta t -
      ((evaluate D cache t₀ θ₀ (lowPrefix t) : ℝ) / 2 + lowEMCorrection t)| ≤
        (evaluationRadius D cache t₀ dt dθ (lowPrefix t) : ℝ) / 2 +
          1 / 1000000000000000000 := by
  have he := evaluate_error hD cache hcache ht hθ hfit
  have hh := low_normalized_finiteMainSum_error htlo
  have hs := abs_sub_le (normalizedCriticalZeta t)
    (finiteMainSum t (lowPrefix t) / 2 + lowEMCorrection t)
    ((evaluate D cache t₀ θ₀ (lowPrefix t) : ℝ) / 2 + lowEMCorrection t)
  have hid :
      finiteMainSum t (lowPrefix t) / 2 + lowEMCorrection t -
        ((evaluate D cache t₀ θ₀ (lowPrefix t) : ℝ) / 2 + lowEMCorrection t) =
      (finiteMainSum t (lowPrefix t) -
        (evaluate D cache t₀ θ₀ (lowPrefix t) : ℝ)) / 2 := by ring
  rw [hid, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hs
  linarith

#print axioms critical_partialSum_re_eq_half_mainSum
#print axioms low_normalized_finiteMainSum_error
#print axioms low_evaluate_error

end LiuWang.Proof.Campaign20260915.ZetaLowWindowCertificate
