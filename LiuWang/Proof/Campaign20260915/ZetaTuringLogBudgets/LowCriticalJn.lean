import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.CriticalPhiGrowth

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaJnCentral

theorem criticalGaussian_third_budget :
    exactGaussianBudget (Real.pi / 3) 0 ≤ 23 / 16 ∧
      exactGaussianBudget (Real.pi / 3) 2 ≤ 39 / 32 := by
  have hb : 0 < Real.pi / 3 := by positivity
  have hb1 : 1 ≤ Real.pi / 3 := by linarith [Real.pi_gt_three]
  have h0 : gaussianAbsoluteMoment (Real.pi / 3) 0 ≤ 7 / 4 := by
    rw [gaussianAbsoluteMoment_zero hb, show Real.pi / (Real.pi / 3) = 3 by field_simp]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
  have h1 : gaussianAbsoluteMoment (Real.pi / 3) 1 ≤ 1 := by
    rw [gaussianAbsoluteMoment_one, div_le_one hb]
    exact hb1
  have hhalf : 1 / (2 * (Real.pi / 3)) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have h2 : gaussianAbsoluteMoment (Real.pi / 3) 2 ≤ 7 / 8 := by
    rw [gaussianAbsoluteMoment_step hb 0]
    norm_num only [Nat.cast_zero, zero_add]
    exact (mul_le_mul hhalf h0 (gaussianAbsoluteMoment_nonneg hb 0) (by norm_num)).trans
      (by norm_num)
  have h3 : gaussianAbsoluteMoment (Real.pi / 3) 3 ≤ 1 := by
    rw [gaussianAbsoluteMoment_step hb 1]
    norm_num only [Nat.cast_one]
    have hfactor : (1 + 1 : ℝ) / (2 * (Real.pi / 3)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    have hh : (1 + 1 : ℝ) / (2 * (Real.pi / 3)) *
        gaussianAbsoluteMoment (Real.pi / 3) 1 ≤ 1 * 1 :=
      mul_le_mul hfactor h1 (gaussianAbsoluteMoment_nonneg hb 1) (by norm_num)
    norm_num at hh ⊢
    exact hh
  have hi : 1 / (Real.sqrt 2 * Real.pi) ≤ 1 / 4 :=
    inverse_descent_constant_rational.trans (by norm_num)
  have hp0 := mul_le_mul h0 hi (by positivity : 0 ≤ 1 / (Real.sqrt 2 * Real.pi))
    (by norm_num : (0 : ℝ) ≤ 7 / 4)
  have hp2 := mul_le_mul h2 hi (by positivity : 0 ≤ 1 / (Real.sqrt 2 * Real.pi))
    (by norm_num : (0 : ℝ) ≤ 7 / 8)
  simp only [mul_one_div] at hp0 hp2
  unfold exactGaussianBudget
  norm_num only [Nat.reduceAdd]
  constructor <;> linarith

theorem critical_firstOrder_gaussian_budget :
    Real.exp (3 / 8) *
      (3 / 4 * exactGaussianBudget (Real.pi / 3) 0 +
        4 * Real.pi / 3 * exactGaussianBudget (Real.pi / 3) 2) ≤ 12 := by
  have hb : 0 < Real.pi / 3 := by positivity
  have hE (n : ℕ) : 0 ≤ exactGaussianBudget (Real.pi / 3) n := by
    unfold exactGaussianBudget
    exact add_nonneg (gaussianAbsoluteMoment_nonneg hb (n + 1))
      (div_nonneg (gaussianAbsoluteMoment_nonneg hb n) (by positivity))
  have hpi : 4 * Real.pi / 3 ≤ 16 / 3 := by linarith [Real.pi_lt_four]
  have h2 := mul_le_mul hpi criticalGaussian_third_budget.2 (hE 2) (by norm_num)
  have hsum : 3 / 4 * exactGaussianBudget (Real.pi / 3) 0 +
      4 * Real.pi / 3 * exactGaussianBudget (Real.pi / 3) 2 ≤ 485 / 64 := by
    linarith [criticalGaussian_third_budget.1]
  have hnonneg := add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) (hE 0))
    (mul_nonneg (by positivity : 0 ≤ 4 * Real.pi / 3) (hE 2))
  exact (mul_le_mul exp_three_eighths_le hsum
    hnonneg
    (by norm_num : (0 : ℝ) ≤ 3 / 2)).trans (by norm_num)

theorem critical_J1_growth_budget {eta : ℝ} {m : ℕ}
    (he : 0 < eta) (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) :
    ‖∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta m 1 y‖ ≤ 12 / eta := by
  let B : ℝ → ℝ := fun y => 3 / 4 * exactGaussianWeight (Real.pi / 3) 0 y +
    4 * Real.pi / 3 * exactGaussianWeight (Real.pi / 3) 2 y
  have hb : 0 < Real.pi / 3 := by positivity
  have hB : Integrable B :=
    ((exactGaussianWeight_integrable hb 0).const_mul _).add
      ((exactGaussianWeight_integrable hb 2).const_mul _)
  have hBn (y : ℝ) : 0 ≤ B y := by
    dsimp [B, exactGaussianWeight]
    positivity
  have hmaj := hB.const_mul (Real.exp (3 / 8) / eta)
  have hpoint (y : ℝ) (hy : y ∈ Set.Icc (-eta / 2) (eta / 2)) :
      ‖rsJnIntegrand (1 / 2) eta m 1 y‖ ≤ Real.exp (3 / 8) / eta * B y := by
    have h := jn_one_pointwise (1 / 2) he (abs_le.mpr (by
      simpa only [Set.mem_Icc, neg_div] using hy)) hm0 hm1
    norm_num only [show (3 / 4 : ℝ) * |1 / 2 - 1| = 3 / 8 by norm_num] at h
    apply h.trans_eq
    dsimp [B, firstOrderPolynomial, exactGaussianWeight]
    norm_num only [show |(1 / 2 : ℝ) - 1| = 1 / 2 by norm_num, pow_zero, sq_abs, neg_div]
    ring
  rw [intervalIntegral.integral_symm (-eta / 2) (eta / 2), norm_neg]
  calc
    _ ≤ ∫ y : ℝ in (-eta / 2)..(eta / 2), Real.exp (3 / 8) / eta * B y :=
      intervalIntegral.norm_integral_le_of_norm_le (by linarith)
        (Filter.Eventually.of_forall (fun y hy => hpoint y ⟨hy.1.le, hy.2⟩))
        hmaj.intervalIntegrable
    _ ≤ ∫ y : ℝ, Real.exp (3 / 8) / eta * B y := by
      rw [intervalIntegral.integral_of_le (by linarith : -eta / 2 ≤ eta / 2)]
      exact setIntegral_le_integral hmaj (Filter.Eventually.of_forall
        (fun y => mul_nonneg (by positivity) (hBn y)))
    _ = (Real.exp (3 / 8) *
        (3 / 4 * exactGaussianBudget (Real.pi / 3) 0 +
          4 * Real.pi / 3 * exactGaussianBudget (Real.pi / 3) 2)) / eta := by
      rw [integral_const_mul]
      dsimp only [B]
      rw [integral_add ((exactGaussianWeight_integrable hb 0).const_mul _)
        ((exactGaussianWeight_integrable hb 2).const_mul _),
        integral_const_mul, integral_const_mul, exactGaussianWeight_integral hb,
        exactGaussianWeight_integral hb]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right critical_firstOrder_gaussian_budget he.le

theorem critical_floor_J1_growth_budget {eta : ℝ} (he : 8 ≤ eta) :
    ‖∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta ⌊eta⌋₊ 1 y‖ ≤ 3 / 2 := by
  have he0 : 0 < eta := by linarith
  apply (critical_J1_growth_budget he0 (Nat.zero_le_self_sub_floor he0.le)
    (Nat.self_sub_floor_lt_one eta).le).trans
  rw [div_le_iff₀ he0]
  linarith

#print axioms criticalGaussian_third_budget
#print axioms critical_firstOrder_gaussian_budget
#print axioms critical_J1_growth_budget
#print axioms critical_floor_J1_growth_budget

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
