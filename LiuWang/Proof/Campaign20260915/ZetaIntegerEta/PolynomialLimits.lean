import LiuWang.Proof.Campaign20260915.ZetaIntegerEta.EndpointLimits

set_option autoImplicit false
noncomputable section
open Complex Filter Set MeasureTheory
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaIntegerEta
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

theorem saddleCoefficient_continuousAt (sigma : ℝ) (k : ℕ) {lambda : ℝ}
    (hl : 0 < lambda) : ContinuousAt (fun x : ℝ => rsSaddleCoefficient sigma x k) lambda := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | k
    · simp only [rsSaddle_coefficient_zero]
      exact continuousAt_const
    rcases k with _ | k
    · have he : (fun x : ℝ => rsSaddleCoefficient sigma x 1) =ᶠ[𝓝 lambda]
          (fun x : ℝ => ((sigma - 1 : ℝ) : ℂ) / x) := by
        filter_upwards [isOpen_Ioi.mem_nhds hl] with x hx
        exact rsSaddle_coefficient_one sigma hx
      exact (continuousAt_const.div Complex.continuous_ofReal.continuousAt
        (ofReal_ne_zero.mpr hl.ne')).congr he.symm
    rcases k with _ | k
    · have he : (fun x : ℝ => rsSaddleCoefficient sigma x 2) =ᶠ[𝓝 lambda]
          (fun x : ℝ => (((sigma - 1) * (sigma - 2) : ℝ) : ℂ) /
            (2 * (x : ℂ) ^ 2)) := by
        filter_upwards [isOpen_Ioi.mem_nhds hl] with x hx
        exact rsSaddle_coefficient_two sigma hx
      apply ContinuousAt.congr _ he.symm
      exact continuousAt_const.div (by fun_prop)
        (mul_ne_zero (by norm_num) (pow_ne_zero _ (ofReal_ne_zero.mpr hl.ne')))
    have he : (fun x : ℝ => rsSaddleCoefficient sigma x (k + 3)) =ᶠ[𝓝 lambda]
        (fun x : ℝ =>
          (-(((k + 3 : ℕ) : ℂ) - sigma) * rsSaddleCoefficient sigma x (k + 2) +
            I * rsSaddleCoefficient sigma x k) / (((k + 3 : ℕ) : ℂ) * x)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hl] with x hx
      apply (eq_div_iff (mul_ne_zero (by exact_mod_cast (show k + 3 ≠ 0 by omega))
        (ofReal_ne_zero.mpr hx.ne'))).mpr
      simpa only [mul_comm] using rsSaddle_coefficient_recurrence sigma hx k
    apply ContinuousAt.congr _ he.symm
    exact ((continuousAt_const.mul (ih (k + 2) (by omega))).add
      (continuousAt_const.mul (ih k (by omega)))).div (by fun_prop)
        (mul_ne_zero (by exact_mod_cast (show k + 3 ≠ 0 by omega)) (ofReal_ne_zero.mpr hl.ne'))

theorem sourcePolynomialExpression_continuousAt (sigma : ℝ) (m N : ℕ) {eta : ℝ}
    (he : 0 < eta) :
    ContinuousAt (fun x : ℝ => sourceGaussianPhase x m *
      ∑ k ∈ Finset.range N, rsSaddleCoefficient sigma (rsSaddleScale * x) k *
        (rsSaddleScale : ℂ) ^ k * correctionMoment k (sourcePhiParameter x m)) eta := by
  apply ContinuousAt.mul (by unfold sourceGaussianPhase; fun_prop)
  apply tendsto_finsetSum
  intro k _
  have hc := (saddleCoefficient_continuousAt sigma k (mul_pos rsSaddleScale_pos he)).comp
    (by fun_prop : ContinuousAt (fun x : ℝ => rsSaddleScale * x) eta)
  have hm : Continuous (fun x : ℝ => correctionMoment k (sourcePhiParameter x m)) := by
    apply (correctionMoment_continuous k).comp
    unfold sourcePhiParameter
    fun_prop
  exact (hc.mul continuousAt_const).mul hm.continuousAt

-- These are limits of the noninteger integrals, not integrals on a pole-crossing line.
theorem actual_polynomial_tendsto_left (sigma : ℝ) (n N : ℕ) :
    Tendsto (fun eta : ℝ => -(∫ y : ℝ,
      rsLocalPolynomialIntegrand sigma eta ⌊eta⌋₊ N y))
      (𝓝[<] ((n : ℝ) + 1))
      (𝓝 (sourceGaussianPhase ((n : ℝ) + 1) n *
        ∑ k ∈ Finset.range N, rsSaddleCoefficient sigma (rsSaddleScale * ((n : ℝ) + 1)) k *
          (rsSaddleScale : ℂ) ^ k * correctionMoment k 1)) := by
  have hc := (sourcePolynomialExpression_continuousAt sigma n N
    (show 0 < (n : ℝ) + 1 by positivity)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Iio ((n : ℝ) + 1)))
  have hp : sourcePhiParameter ((n : ℝ) + 1) n = 1 := by
    unfold sourcePhiParameter
    ring
  rw [hp, ofReal_one] at hc
  apply hc.congr'
  filter_upwards [Ioo_mem_nhdsLT (show (n : ℝ) < n + 1 by linarith)] with eta he
  rw [Nat.floor_eq_on_Ico n eta ⟨he.1.le, he.2⟩,
    sourceLocalPolynomial_integral sigma (by linarith [he.1] : 0 < eta - n)
      (by linarith [he.2] : eta - n < 1) N]

theorem actual_polynomial_tendsto_right (sigma : ℝ) {n : ℕ} (hn : 0 < n) (N : ℕ) :
    Tendsto (fun eta : ℝ => -(∫ y : ℝ,
      rsLocalPolynomialIntegrand sigma eta ⌊eta⌋₊ N y))
      (𝓝[>] (n : ℝ))
      (𝓝 (sourceGaussianPhase n n *
        ∑ k ∈ Finset.range N, rsSaddleCoefficient sigma (rsSaddleScale * n) k *
          (rsSaddleScale : ℂ) ^ k * correctionMoment k (-1))) := by
  have hc := (sourcePolynomialExpression_continuousAt sigma n N
    (show (0 : ℝ) < n by exact_mod_cast hn)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (n : ℝ)))
  have hp : sourcePhiParameter n n = -1 := by simp [sourcePhiParameter]
  rw [hp, ofReal_neg, ofReal_one] at hc
  apply hc.congr'
  filter_upwards [Ioo_mem_nhdsGT (show (n : ℝ) < n + 1 by linarith)] with eta he
  rw [Nat.floor_eq_on_Ico n eta ⟨he.1.le, he.2⟩,
    sourceLocalPolynomial_integral sigma (by linarith [he.1] : 0 < eta - n)
      (by linarith [he.2] : eta - n < 1) N]

theorem sourceGaussianPhase_endpoint_jump (n : ℕ) :
    sourceGaussianPhase ((n : ℝ) + 1) n =
      -sourceGaussianPhase ((n : ℝ) + 1) (n + 1) := by
  unfold sourceGaussianPhase
  have he : ((n : ℝ) + 1 - n : ℝ) = 1 := by ring
  have he' : (n : ℝ) + 1 - ((n + 1 : ℕ) : ℝ) = 0 := by push_cast; ring
  rw [he, he']
  norm_num only [ofReal_one, ofReal_zero, one_pow, zero_pow (by norm_num : 2 ≠ 0), zero_add]
  rw [show -(Real.pi : ℂ) * I * (9 / 8) =
    -(Real.pi * I) + -(Real.pi : ℂ) * I * (1 / 8) by ring, exp_add, exp_neg, exp_pi_mul_I]
  simp

theorem actual_polynomial_one_tendsto_left (sigma : ℝ) (n : ℕ) :
    Tendsto (fun eta : ℝ => -(∫ y : ℝ,
      rsLocalPolynomialIntegrand sigma eta ⌊eta⌋₊ 1 y))
      (𝓝[<] ((n : ℝ) + 1))
      (𝓝 (-sourceGaussianPhase ((n : ℝ) + 1) (n + 1) * (Real.cos (Real.pi / 8) : ℂ))) := by
  have hm : correctionMoment 0 1 = (Real.cos (Real.pi / 8) : ℂ) := by
    simpa only [ofReal_one, rsPhi_endpoint_one] using
      correctionMoment_zero_phi (by norm_num : |(1 : ℝ)| < 3 / 2)
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    sourceSaddle_scaled_zero, one_mul, hm, sourceGaussianPhase_endpoint_jump] using
      actual_polynomial_tendsto_left sigma n 1

theorem actual_polynomial_one_tendsto_right (sigma : ℝ) {n : ℕ} (hn : 0 < n) :
    Tendsto (fun eta : ℝ => -(∫ y : ℝ,
      rsLocalPolynomialIntegrand sigma eta ⌊eta⌋₊ 1 y))
      (𝓝[>] (n : ℝ))
      (𝓝 (sourceGaussianPhase n n * (Real.cos (Real.pi / 8) : ℂ))) := by
  have hm : correctionMoment 0 (-1) = (Real.cos (Real.pi / 8) : ℂ) := by
    simpa only [ofReal_neg, ofReal_one, rsPhi_endpoint_neg_one] using
      correctionMoment_zero_phi (by norm_num : |(-1 : ℝ)| < 3 / 2)
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    sourceSaddle_scaled_zero, one_mul, hm] using actual_polynomial_tendsto_right sigma hn 1

theorem strict_height_eventually (H eta : ℝ) (h : H < eta ^ 2) :
    ∀ᶠ x : ℝ in 𝓝 eta, H < x ^ 2 :=
  (show ContinuousAt (fun x : ℝ => x ^ 2) eta by fun_prop).eventually
    (Ioi_mem_nhds h)

end LiuWang.Proof.Campaign20260915.ZetaIntegerEta
