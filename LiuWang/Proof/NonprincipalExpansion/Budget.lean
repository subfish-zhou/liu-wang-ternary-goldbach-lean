import LiuWang.Proof.NonprincipalExpansion.Kernel
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Abel 误差的端点、相位积分和闭窗单项分账

相位导数范数为 `2*pi*|eta|`；精确积分 `t` 保留二分之一。
闭下端点单项复用已验大端点比较支付，不重造对数幂链。
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators Interval
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.OscillatoryBounds
open LiuWang.Proof.VaughanTypeI (norm_charReal_eq_one)
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.NonprincipalExpansion

theorem norm_phaseDerivative (η t : ℝ) :
    ‖phaseDerivative η t‖ = 2 * Real.pi * |η| := by
  rw [phaseDerivative, norm_mul, norm_charReal_eq_one, one_mul, norm_frequency]

theorem norm_phase_error_integral_le {a b C : ℝ} (hab : a ≤ b)
    (η : ℝ) (F : ℝ → ℂ)
    (hF : ∀ t ∈ Set.Icc a b, ‖F t‖ ≤ C * t) :
    ‖∫ t in a..b, phaseDerivative η t * F t‖ ≤
      Real.pi * |η| * C * (b ^ 2 - a ^ 2) := by
  have hi : IntervalIntegrable (fun t => (2 * Real.pi * |η| * C) * t)
      volume a b := (continuous_const.mul continuous_id).intervalIntegrable a b
  calc
    _ ≤ ∫ t in a..b, (2 * Real.pi * |η| * C) * t := by
      apply intervalIntegral.norm_integral_le_of_norm_le hab
        (Filter.Eventually.of_forall fun t ht => ?_) hi
      rw [norm_mul, norm_phaseDerivative]
      calc
        _ ≤ (2 * Real.pi * |η|) * (C * t) :=
          mul_le_mul_of_nonneg_left (hF t ⟨ht.1.le, ht.2⟩) (by positivity)
        _ = _ := by ring
    _ = Real.pi * |η| * C * (b ^ 2 - a ^ 2) := by
      rw [intervalIntegral.integral_const_mul, integral_id]
      ring

theorem norm_abelTransform_le (N : ℕ) (η : ℝ) (F : ℝ → ℂ) {C : ℝ}
    (hF : ∀ t ∈ Set.Icc (sourceWindowLower N) (N : ℝ), ‖F t‖ ≤ C * t) :
    ‖abelTransform N η F‖ ≤
      C * ((N : ℝ) + sourceWindowLower N) +
        Real.pi * |η| * C * ((N : ℝ) ^ 2 - sourceWindowLower N ^ 2) := by
  have hb : ‖charReal (η * N) * F N‖ ≤ C * N := by
    rw [norm_mul, norm_charReal_eq_one, one_mul]
    exact hF N ⟨lower_le N, le_rfl⟩
  have ha : ‖charReal (η * sourceWindowLower N) * F (sourceWindowLower N)‖ ≤
      C * sourceWindowLower N := by
    rw [norm_mul, norm_charReal_eq_one, one_mul]
    exact hF _ ⟨le_rfl, lower_le N⟩
  unfold abelTransform
  calc
    _ ≤ (‖charReal (η * N) * F N‖ +
        ‖charReal (η * sourceWindowLower N) * F (sourceWindowLower N)‖) +
        ‖∫ t in sourceWindowLower N..(N : ℝ), phaseDerivative η t * F t‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ C * N + C * sourceWindowLower N +
        Real.pi * |η| * C * ((N : ℝ) ^ 2 - sourceWindowLower N ^ 2) :=
      add_le_add (add_le_add hb ha) (norm_phase_error_integral_le (lower_le N) η F hF)
    _ = _ := by ring

theorem norm_lowerTerm_le_log {N q : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    (chi : Character q) (η : ℝ) :
    ‖lowerTerm N (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * chi n) η‖ ≤
      sourceL N := by
  unfold lowerTerm
  split_ifs with he
  · have ha1 : 1 ≤ sourceWindowLower N := by
      linarith [(PerronBudget.source_cutoff_bounds hN le_rfl (lower_le N)).1]
    have hfpos : (0 : ℝ) < (⌊sourceWindowLower N⌋₊ : ℝ) := by
      rw [he]
      linarith
    rw [norm_mul, norm_charReal_eq_one, mul_one]
    calc
      _ ≤ ArithmeticFunction.vonMangoldt ⌊sourceWindowLower N⌋₊ := by
        simpa only [twistedMangoldtSequence, mul_comm] using
          norm_twistedMangoldtSequence_le_vonMangoldt chi ⌊sourceWindowLower N⌋₊
      _ ≤ Real.log (⌊sourceWindowLower N⌋₊ : ℝ) := ArithmeticFunction.vonMangoldt_le_log
      _ ≤ sourceL N := Real.log_le_log hfpos
        ((Nat.floor_le (lower_nonneg N)).trans (lower_le N))
  · simpa using (sourceL_pos hN).le

theorem lowerTerm_cost_source_le {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    sourceL N ≤ 0.000001 * (N : ℝ) / sourceT N * sourceL N ^ 2 := by
  have hT0 := sourceT_pos hN
  have hT1 : 1 ≤ sourceT N := one_le_pow₀ (one_le_sourceL hN)
  have hpay : 1 ≤ 0.000001 * (N : ℝ) / sourceT N := by
    apply (le_div_iff₀ hT0).mpr
    have hh := PerronBudget.million_sourceT_sq_le_endpoint hN (lower_le N)
    nlinarith [mul_nonneg (sub_nonneg.mpr hT1) hT0.le]
  have hL := one_le_sourceL hN
  calc
    _ ≤ sourceL N ^ 2 := by nlinarith
    _ ≤ _ := by
      simpa using mul_le_mul_of_nonneg_right hpay (sq_nonneg (sourceL N))

theorem norm_lowerTerm_source_le {N q : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    (chi : Character q) (η : ℝ) :
    ‖lowerTerm N (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * chi n) η‖ ≤
      0.000001 * (N : ℝ) / sourceT N * sourceL N ^ 2 :=
  (norm_lowerTerm_le_log hN chi η).trans (lowerTerm_cost_source_le hN)

theorem source_abel_budget {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) (η : ℝ) :
    (1.374172 / sourceT N * sourceL N ^ 2) *
        ((N : ℝ) + sourceWindowLower N) +
      Real.pi * |η| * (1.374172 / sourceT N * sourceL N ^ 2) *
        ((N : ℝ) ^ 2 - sourceWindowLower N ^ 2) +
      0.000001 * (N : ℝ) / sourceT N * sourceL N ^ 2 ≤
    (1.3756 + 4.3287 * (N : ℝ) * |η|) * (N : ℝ) / sourceT N * sourceL N ^ 2 := by
  have hT0 := sourceT_pos hN
  have hscale : 0 ≤ (N : ℝ) / sourceT N * sourceL N ^ 2 := by positivity
  have hquad : 0 ≤ (N : ℝ) ^ 2 - sourceWindowLower N ^ 2 := by
    have := lower_le N
    have := lower_nonneg N
    nlinarith
  have hpi :
      Real.pi * |η| * (1.374172 / sourceT N * sourceL N ^ 2) *
          ((N : ℝ) ^ 2 - sourceWindowLower N ^ 2) ≤
        3.15 * |η| * (1.374172 / sourceT N * sourceL N ^ 2) * (N : ℝ) ^ 2 := by
    apply (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right Real.pi_lt_d2.le (abs_nonneg η))
        (by positivity)) hquad).trans
    exact mul_le_mul_of_nonneg_left (sub_le_self _ (sq_nonneg _)) (by positivity)
  calc
    _ ≤ (1.374172 / sourceT N * sourceL N ^ 2) *
          ((N : ℝ) + sourceWindowLower N) +
        3.15 * |η| * (1.374172 / sourceT N * sourceL N ^ 2) * (N : ℝ) ^ 2 +
        0.000001 * (N : ℝ) / sourceT N * sourceL N ^ 2 :=
      add_le_add (add_le_add le_rfl hpi) le_rfl
    _ = (1.375547172 + 4.3286418 * (N : ℝ) * |η|) *
        ((N : ℝ) / sourceT N * sourceL N ^ 2) := by
      unfold sourceWindowLower
      ring
    _ ≤ _ := by
      have hcoef : 1.375547172 + 4.3286418 * (N : ℝ) * |η| ≤
          1.3756 + 4.3287 * (N : ℝ) * |η| := by
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N) (abs_nonneg η)]
      simpa only [mul_assoc, mul_div_assoc] using
        mul_le_mul_of_nonneg_right hcoef hscale

end LiuWang.Proof.NonprincipalExpansion
