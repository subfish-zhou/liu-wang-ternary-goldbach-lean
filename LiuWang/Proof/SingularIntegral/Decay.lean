import LiuWang.Proof.SingularIntegral.Window
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# 仅用于绝对可积性的固定参数界

一次分部积分给出原窗的 `|η| ‖Jρ(η)‖` 上界。
这里的常数是有限区间上的具体范数积分，不是渐近阈值，也不是
Lemma 4.2 的分段尖锐常数。两个衰减因子及第三个有界因子足够。
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set FourierTransform
open scoped Interval Topology
open AnalyticNumberTheory.LargeSieve LiuWang.Proof.Interfaces

namespace LiuWang.Proof.SingularIntegral

def weightMass (N : ℕ) (rho : ℂ) : ℝ :=
  ∫ t in sourceWindowLower N..(N : ℝ), ‖(t : ℂ) ^ (rho - 1)‖

def weightVariation (N : ℕ) (rho : ℂ) : ℝ :=
  (‖(N : ℂ) ^ (rho - 1)‖ + ‖(sourceWindowLower N : ℂ) ^ (rho - 1)‖ +
    ∫ t in sourceWindowLower N..(N : ℝ), ‖(rho - 1) * (t : ℂ) ^ (rho - 1 - 1)‖) /
    (2 * Real.pi)

theorem weightMass_nonneg (N : ℕ) (rho : ℂ) : 0 ≤ weightMass N rho :=
  intervalIntegral.integral_nonneg (window_lower_le N) (fun _ _ => norm_nonneg _)

theorem weightVariation_nonneg (N : ℕ) (rho : ℂ) : 0 ≤ weightVariation N rho := by
  unfold weightVariation
  exact div_nonneg (add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
    (intervalIntegral.integral_nonneg (window_lower_le N) (fun _ _ => norm_nonneg _)))
    (le_of_lt (mul_pos (by norm_num) Real.pi_pos))

theorem Jrho_norm_le_mass (N : ℕ) (rho : ℂ) (eta : ℝ) :
    ‖Jrho N rho eta‖ ≤ weightMass N rho := by
  simpa only [Jrho, weightMass, norm_mul, charReal_norm, mul_one] using
    (intervalIntegral.norm_integral_le_integral_norm
      (f := fun t : ℝ => (t : ℂ) ^ (rho - 1) * charReal (eta * t)) (window_lower_le N))

theorem cpow_hasDerivAt {t : ℝ} (ht : 0 < t) (z : ℂ) :
    HasDerivAt (fun s : ℝ => (s : ℂ) ^ z) (z * (t : ℂ) ^ (z - 1)) t := by
  by_cases hz : z = 0
  · simp only [hz, Complex.cpow_zero, zero_mul]
    exact hasDerivAt_const t 1
  · exact hasDerivAt_ofReal_cpow_const ht.ne' hz

theorem charReal_mul_hasDerivAt (eta t : ℝ) :
    HasDerivAt (fun s : ℝ => charReal (eta * s))
      ((2 * Real.pi * eta : ℝ) * Complex.I * charReal (eta * t)) t := by
  have h := (((hasDerivAt_id (t : ℂ)).const_mul
    ((2 * Real.pi * eta : ℝ) * Complex.I)).cexp).comp_ofReal
  convert h using 1
  · ext s
    simp [charReal, Complex.ofReal_mul, Complex.ofReal_ofNat]
    congr 1
    ring
  · simp [charReal, Complex.ofReal_mul, Complex.ofReal_ofNat]
    rw [mul_comm (Complex.exp _)]
    congr 2
    ring

theorem Jrho_integrationByParts {N : ℕ} (hN : 0 < N) (rho : ℂ) (eta : ℝ) :
    ((2 * Real.pi * eta : ℝ) * Complex.I) * Jrho N rho eta =
      (N : ℂ) ^ (rho - 1) * charReal (eta * N) -
      (sourceWindowLower N : ℂ) ^ (rho - 1) * charReal (eta * sourceWindowLower N) -
      ∫ t in sourceWindowLower N..(N : ℝ),
        ((rho - 1) * (t : ℂ) ^ (rho - 1 - 1)) * charReal (eta * t) := by
  have hw : ∀ t ∈ Set.uIcc (sourceWindowLower N) (N : ℝ),
      HasDerivAt (fun s : ℝ => (s : ℂ) ^ (rho - 1))
        ((rho - 1) * (t : ℂ) ^ (rho - 1 - 1)) t := by
    intro t ht
    rw [uIcc_of_le (window_lower_le N)] at ht
    exact cpow_hasDerivAt ((window_lower_pos hN).trans_le ht.1) _
  have hd := (cpow_intervalIntegrable hN (rho - 1 - 1)).const_mul (rho - 1)
  have he : IntervalIntegrable
      (fun t : ℝ => ((2 * Real.pi * eta : ℝ) * Complex.I) * charReal (eta * t))
      volume (sourceWindowLower N) N :=
    (continuous_const.mul
      (charReal_continuous.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul hw
    (fun t _ => charReal_mul_hasDerivAt eta t) hd he
  simp only [Complex.ofReal_natCast] at h
  convert h using 1
  simp only [Jrho, ← intervalIntegral.integral_const_mul]
  congr 1
  ext t
  ring

theorem Jrho_abs_mul_norm_le_variation {N : ℕ} (hN : 0 < N) (rho : ℂ) (eta : ℝ) :
    |eta| * ‖Jrho N rho eta‖ ≤ weightVariation N rho := by
  have h := congrArg norm (Jrho_integrationByParts hN rho eta)
  have hb := norm_sub_le
    ((N : ℂ) ^ (rho - 1) * charReal (eta * N) -
      (sourceWindowLower N : ℂ) ^ (rho - 1) * charReal (eta * sourceWindowLower N))
    (∫ t in sourceWindowLower N..(N : ℝ),
      ((rho - 1) * (t : ℂ) ^ (rho - 1 - 1)) * charReal (eta * t))
  have hc := norm_sub_le
    ((N : ℂ) ^ (rho - 1) * charReal (eta * N))
    ((sourceWindowLower N : ℂ) ^ (rho - 1) * charReal (eta * sourceWindowLower N))
  have hi := intervalIntegral.norm_integral_le_integral_norm
    (μ := volume)
    (f := fun t : ℝ => ((rho - 1) * (t : ℂ) ^ (rho - 1 - 1)) * charReal (eta * t))
    (window_lower_le N)
  simp only [norm_mul, charReal_norm, mul_one] at hc hi
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hn : ‖((2 * Real.pi * eta : ℝ) : ℂ) * Complex.I‖ = 2 * Real.pi * |eta| := by
    norm_num [norm_mul, Complex.norm_real, abs_mul, abs_of_pos Real.pi_pos]
  rw [norm_mul, hn] at h
  unfold weightVariation
  apply (le_div_iff₀ hp).2
  simp only [norm_mul]
  nlinarith

theorem Jrho_continuous {N : ℕ} (hN : 0 < N) (rho : ℂ) :
    Continuous (Jrho N rho) := by
  have hf : Continuous (𝓕 (windowWeight N rho)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by fun_prop) (windowWeight_integrable hN rho)
  have heq : Jrho N rho = fun eta => 𝓕 (windowWeight N rho) (-eta) :=
    funext (Jrho_eq_fourier_neg N rho)
  rw [heq]
  exact hf.comp continuous_neg

theorem Jrho_pair_integrable {N : ℕ} (hN : 0 < N) (rho₁ rho₂ : ℂ) :
    Integrable (fun eta : ℝ => Jrho N rho₁ eta * Jrho N rho₂ eta) := by
  let C := weightMass N rho₁ * weightMass N rho₂ +
    weightVariation N rho₁ * weightVariation N rho₂
  refine (integrable_inv_one_add_sq.const_mul C).mono'
    ((Jrho_continuous hN rho₁).mul (Jrho_continuous hN rho₂)).aestronglyMeasurable ?_
  filter_upwards with eta
  rw [norm_mul]
  have hm := mul_le_mul (Jrho_norm_le_mass N rho₁ eta) (Jrho_norm_le_mass N rho₂ eta)
    (norm_nonneg _) (weightMass_nonneg N rho₁)
  have hd := mul_le_mul (Jrho_abs_mul_norm_le_variation hN rho₁ eta)
    (Jrho_abs_mul_norm_le_variation hN rho₂ eta)
    (mul_nonneg (abs_nonneg _) (norm_nonneg _)) (weightVariation_nonneg N rho₁)
  change ‖Jrho N rho₁ eta‖ * ‖Jrho N rho₂ eta‖ ≤ C / (1 + eta ^ 2)
  apply (le_div_iff₀ (by positivity : 0 < 1 + eta ^ 2)).2
  dsimp [C]
  have heq : |eta| * ‖Jrho N rho₁ eta‖ * (|eta| * ‖Jrho N rho₂ eta‖) =
      ‖Jrho N rho₁ eta‖ * ‖Jrho N rho₂ eta‖ * eta ^ 2 := by
    calc
      _ = ‖Jrho N rho₁ eta‖ * ‖Jrho N rho₂ eta‖ * |eta| ^ 2 := by ring
      _ = _ := by rw [sq_abs]
  rw [heq] at hd
  nlinarith

theorem Jrho_triple_integrable {N : ℕ} (hN : 0 < N) (rho₁ rho₂ rho₃ : ℂ) :
    Integrable (fun eta : ℝ =>
      charReal (-(N : ℝ) * eta) * Jrho N rho₁ eta * Jrho N rho₂ eta * Jrho N rho₃ eta) := by
  refine ((Jrho_pair_integrable hN rho₁ rho₂).norm.mul_const (weightMass N rho₃)).mono'
    ((((charReal_continuous.comp (continuous_const.mul continuous_id)).mul
      (Jrho_continuous hN rho₁)).mul (Jrho_continuous hN rho₂)).mul
      (Jrho_continuous hN rho₃)).aestronglyMeasurable ?_
  filter_upwards with eta
  simp only [norm_mul, charReal_norm, one_mul]
  exact mul_le_mul_of_nonneg_left (Jrho_norm_le_mass N rho₃ eta)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

end LiuWang.Proof.SingularIntegral
