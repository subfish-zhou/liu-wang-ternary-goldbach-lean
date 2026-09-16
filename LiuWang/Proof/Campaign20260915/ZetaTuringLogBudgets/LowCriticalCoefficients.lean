import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.CriticalPhiGrowth

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell
open LiuWang.Proof.Campaign20260915.ZetaJnCentral

def lowCriticalCoefficient : ℕ → ℝ
  | 0 => 1
  | 1 => 1 / 8
  | 2 => 1 / 8
  | n + 3 => (8 * lowCriticalCoefficient n +
      ((n : ℝ) + 5 / 2) * lowCriticalCoefficient (n + 2)) / (8 * ((n : ℝ) + 3))

theorem lowCriticalCoefficient_nonneg (n : ℕ) : 0 ≤ lowCriticalCoefficient n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | n
    · norm_num [lowCriticalCoefficient]
    · norm_num [lowCriticalCoefficient]
    · norm_num [lowCriticalCoefficient]
    · rw [lowCriticalCoefficient]
      have h0 := ih n (by omega)
      have h2 := ih (n + 2) (by omega)
      positivity

theorem scaledCoefficient_low_bound {eta : ℝ} (he : 8 ≤ eta) (n : ℕ) :
    ‖scaledCoefficient eta n‖ ≤ lowCriticalCoefficient n := by
  have he0 : 0 < eta := by linarith
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | n
    · rw [scaledCoefficient, sourceSaddle_scaled_zero]
      norm_num [lowCriticalCoefficient]
    · rw [scaledCoefficient, sourceSaddle_scaled_one he0, lowCriticalCoefficient]
      norm_num [norm_div, norm_mul, abs_of_pos he0]
      have hi : eta⁻¹ ≤ 1 / 8 := by
        rw [inv_eq_one_div]
        exact one_div_le_one_div_of_le (by norm_num) he
      linarith
    · rw [scaledCoefficient, sourceSaddle_scaled_two he0, lowCriticalCoefficient]
      norm_num [norm_div, norm_mul, norm_pow, abs_of_pos he0]
      rw [div_le_iff₀ (by positivity : 0 < 8 * eta ^ 2)]
      nlinarith
    · have hr := scaled_recurrence_weighted he0 n 0
      simp only [Nat.zero_add, pow_one, pow_zero, one_mul, norm_mul, norm_real,
        Real.norm_eq_abs, abs_of_pos he0] at hr
      have h0 := ih n (by omega)
      have h2 := ih (n + 2) (by omega)
      have hpi : 2 * Real.pi ≤ 8 := by linarith [Real.pi_lt_four]
      have hterm0 := mul_le_mul hpi h0 (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
      have hterm2 := mul_le_mul_of_nonneg_left h2
        (by positivity : 0 ≤ (n : ℝ) + 5 / 2)
      have hscale := mul_le_mul_of_nonneg_right he
        (show 0 ≤ ((n : ℝ) + 3) * ‖scaledCoefficient eta (n + 3)‖ by positivity)
      rw [lowCriticalCoefficient, le_div_iff₀ (by positivity : 0 < 8 * ((n : ℝ) + 3))]
      nlinarith

theorem lowCritical_correction_scalar :
    (∑ n ∈ Finset.range 11,
      lowCriticalCoefficient (n + 1) * exactGaussianBudget Real.pi n) ≤ 1 / 4 := by
  apply (Finset.sum_le_sum (fun n _ => mul_le_mul_of_nonneg_left
    (exactGaussianBudget_rational n) (lowCriticalCoefficient_nonneg (n + 1)))).trans
  norm_num [Finset.sum_range_succ, lowCriticalCoefficient, rationalGaussianMoment]

theorem lowCritical_correction_integral {eta : ℝ} {m : ℕ}
    (he : 8 ≤ eta) (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) :
    ‖∑ n ∈ Finset.range 11, scaledCoefficient eta (n + 1) *
      (∫ y : ℝ in (eta / 2)..(-eta / 2), gaussianMonomial eta m n y)‖ ≤ 1 / 4 := by
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun n _ => ?_)).trans lowCritical_correction_scalar
  rw [norm_mul, intervalIntegral.integral_symm (-eta / 2) (eta / 2), norm_neg]
  exact mul_le_mul (scaledCoefficient_low_bound he (n + 1))
    (gaussianMonomial_exact_interval eta m n hm0 hm1 (by linarith))
    (norm_nonneg _) (lowCriticalCoefficient_nonneg (n + 1))

theorem lowCritical_J1_from_J12 {eta : ℝ} {m : ℕ}
    (he : 8 ≤ eta) (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) :
    ‖∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta m 1 y‖ ≤
      ‖∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta m 12 y‖ + 1 / 4 := by
  have hs := jn_finite_remainder_split (by linarith : 0 < eta) hm0 hm1 0 11
  simp only [Nat.zero_add, Nat.reduceAdd] at hs
  rw [hs]
  exact (norm_add_le _ _).trans (add_le_add le_rfl (lowCritical_correction_integral he hm0 hm1))

#print axioms scaledCoefficient_low_bound
#print axioms lowCritical_correction_scalar
#print axioms lowCritical_correction_integral
#print axioms lowCritical_J1_from_J12

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
