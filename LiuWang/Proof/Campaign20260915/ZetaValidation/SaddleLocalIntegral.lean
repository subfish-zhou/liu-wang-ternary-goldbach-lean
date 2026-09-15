import LiuWang.Proof.Campaign20260915.ZetaValidation.SaddleWeightedIntegral

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def rsLocalPrefactor (sigma eta : ℝ) (m : ℕ) : ℂ :=
  (eta : ℂ) ^ (((sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) - 1) *
    exp (-2 * Real.pi * I * m * eta)

def rsLocalPolynomialIntegrand (sigma eta : ℝ) (m N : ℕ) (y : ℝ) : ℂ :=
  rsDescentDirection * rsGaussianKernel eta m (rsDescentPoint eta y) *
    ∑ n ∈ Finset.range N, rsSaddleCoefficient sigma (rsSaddleScale * eta) n *
      ((rsSaddleScale : ℂ) * (rsDescentPoint eta y - eta)) ^ n

theorem rsDescent_no_integer (eta y : ℝ) (he : ∀ n : ℤ, eta ≠ n) :
    ¬∃ n : ℤ, rsDescentPoint eta y = n := by
  rintro ⟨n, hn⟩
  have hi := congrArg Complex.im hn
  simp [rsDescentPoint, rsDescentDirection] at hi
  have hy : y = 0 := by
    simpa using hi
  rw [hy] at hn
  have hr := congrArg Complex.re hn
  simp [rsDescentPoint] at hr
  exact he n hr

theorem rsGaussian_descent_continuous (eta : ℝ) (m : ℕ) (he : ∀ n : ℤ, eta ≠ n) :
    Continuous (fun y : ℝ => rsGaussianKernel eta m (rsDescentPoint eta y)) := by
  unfold rsGaussianKernel
  apply Continuous.div
  · unfold rsDescentPoint
    fun_prop
  · unfold rsHankelDenominator rsDescentPoint
    fun_prop
  · intro y
    exact mt (rsHankelDenominator_zero_iff _).mp (rsDescent_no_integer eta y he)

theorem rsLocalPolynomial_continuous (sigma eta : ℝ) (m N : ℕ)
    (he : ∀ n : ℤ, eta ≠ n) : Continuous (rsLocalPolynomialIntegrand sigma eta m N) := by
  unfold rsLocalPolynomialIntegrand
  apply (continuous_const.mul (rsGaussian_descent_continuous eta m he)).mul
  unfold rsDescentPoint
  fun_prop

theorem rsJn_local_integrable (sigma : ℝ) (m N : ℕ) {eta : ℝ}
    (he : 0 < eta) (hint : ∀ n : ℤ, eta ≠ n) :
    IntervalIntegrable (rsJnIntegrand sigma eta m N) volume (eta / 2) (-eta / 2) := by
  apply ContinuousOn.intervalIntegrable
  intro y hy
  rw [uIcc_of_ge (by linarith : -eta / 2 ≤ eta / 2)] at hy
  have hye : |y| < eta := abs_lt.mpr (by constructor <;> linarith [hy.1, hy.2])
  have hz : ‖(rsSaddleScale : ℂ) * (rsDescentPoint eta y - eta)‖ < rsSaddleScale * eta := by
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos rsSaddleScale_pos,
      rsDescentPoint_distance]
    exact mul_lt_mul_of_pos_left hye rsSaddleScale_pos
  have hw : ContinuousAt (fun y : ℝ => rsSaddleWeight sigma (rsSaddleScale * eta)
      ((rsSaddleScale : ℂ) * (rsDescentPoint eta y - eta))) y := by
    exact ContinuousAt.comp (f := fun y : ℝ =>
      (rsSaddleScale : ℂ) * (rsDescentPoint eta y - eta))
      (rsSaddle_analytic sigma (mul_pos rsSaddleScale_pos he) hz).continuousAt
      (by unfold rsDescentPoint; fun_prop)
  apply ContinuousAt.continuousWithinAt
  unfold rsJnIntegrand rsSaddleRemainder
  exact (continuousAt_const.mul (rsGaussian_descent_continuous eta m hint).continuousAt).mul
    (hw.sub (by unfold rsDescentPoint; fun_prop))

theorem rsHankel_local_truncation_pointwise (sigma : ℝ) (m N : ℕ) {eta y : ℝ}
    (he : 0 < eta) (hy : |y| < eta) :
    rsDescentDirection *
      rsHankelKernel ((sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) m
        (rsDescentPoint eta y) =
      rsLocalPrefactor sigma eta m *
        (rsLocalPolynomialIntegrand sigma eta m N y + rsJnIntegrand sigma eta m N y) := by
  rw [rsHankelKernel_saddle_factor sigma m he (by rw [rsDescentPoint_distance]; exact hy)]
  unfold rsLocalPrefactor rsLocalPolynomialIntegrand rsJnIntegrand rsSaddleRemainder
  ring

theorem rsHankel_local_truncation (sigma : ℝ) (m N : ℕ) {eta : ℝ}
    (he : 0 < eta) (hint : ∀ n : ℤ, eta ≠ n) :
    (∫ y : ℝ in (eta / 2)..(-eta / 2), rsDescentDirection *
      rsHankelKernel ((sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) m
        (rsDescentPoint eta y)) =
      rsLocalPrefactor sigma eta m *
        ((∫ y : ℝ in (eta / 2)..(-eta / 2), rsLocalPolynomialIntegrand sigma eta m N y) +
          ∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand sigma eta m N y) := by
  have hp := (rsLocalPolynomial_continuous sigma eta m N hint).intervalIntegrable
    (μ := volume) (eta / 2) (-eta / 2)
  have hr := rsJn_local_integrable sigma m N he hint
  rw [← intervalIntegral.integral_add hp hr, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro y hy
  rw [uIcc_of_ge (by linarith : -eta / 2 ≤ eta / 2)] at hy
  exact rsHankel_local_truncation_pointwise sigma m N he
    (abs_lt.mpr (by constructor <;> linarith [hy.1, hy.2]))

theorem rsHankel_local_integrable (sigma : ℝ) (m : ℕ) {eta : ℝ}
    (he : 0 < eta) (hint : ∀ n : ℤ, eta ≠ n) :
    IntervalIntegrable (fun y : ℝ => rsDescentDirection *
      rsHankelKernel ((sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) m
        (rsDescentPoint eta y)) volume (eta / 2) (-eta / 2) := by
  have hp := (rsLocalPolynomial_continuous sigma eta m 0 hint).intervalIntegrable
    (μ := volume) (eta / 2) (-eta / 2)
  have hr := rsJn_local_integrable sigma m 0 he hint
  refine ((hp.add hr).const_mul (rsLocalPrefactor sigma eta m)).congr ?_
  intro y hy
  have hy := uIoc_subset_uIcc hy
  rw [uIcc_of_ge (by linarith : -eta / 2 ≤ eta / 2)] at hy
  exact (rsHankel_local_truncation_pointwise sigma m 0 he
    (abs_lt.mpr (by constructor <;> linarith [hy.1, hy.2]))).symm

end LiuWang.Proof.Campaign20260915.ZetaValidation
