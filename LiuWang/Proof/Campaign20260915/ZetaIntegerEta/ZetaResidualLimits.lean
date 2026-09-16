import LiuWang.Proof.Campaign20260915.ZetaIntegerEta.EndpointAudit

set_option autoImplicit false
noncomputable section
open Complex Filter Set MeasureTheory
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaIntegerEta
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

def actualZetaPolynomialResidual (sigma eta : ℝ) (m N : ℕ) : ℂ :=
  let s : ℂ := (sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2
  riemannZeta s - sourceFiniteSums s m +
    rsHankelPrefactor s * rsLocalPrefactor sigma eta m *
      (sourceGaussianPhase eta m *
        ∑ k ∈ Finset.range N, rsSaddleCoefficient sigma (rsSaddleScale * eta) k *
          (rsSaddleScale : ℂ) ^ k * correctionMoment k (sourcePhiParameter eta m))

theorem localPrefactor_continuousAt (sigma : ℝ) (m : ℕ) {eta : ℝ} (he : 0 < eta) :
    ContinuousAt (fun x : ℝ => rsLocalPrefactor sigma x m) eta := by
  unfold rsLocalPrefactor
  apply ContinuousAt.mul _ (by fun_prop)
  apply Complex.continuous_ofReal.continuousAt.cpow (by fun_prop)
  exact mem_slitPlane_iff.mpr (Or.inl he)

theorem actualZetaPolynomialResidual_continuousAt (sigma : ℝ) (m N : ℕ)
    {eta : ℝ} (he : 0 < eta) :
    ContinuousAt (fun x : ℝ => actualZetaPolynomialResidual sigma x m N) eta := by
  let s : ℝ → ℂ := fun x => (sigma : ℂ) + I * ((rsSaddleScale * x : ℝ) : ℂ) ^ 2
  have hs : Continuous s := by dsimp [s]; fun_prop
  have ht : 0 < (s eta).im := by
    simpa only [s, ← ofReal_pow, add_im, ofReal_im, mul_im, I_re, I_im,
      zero_mul, one_mul, zero_add, ofReal_re] using
        sq_pos_of_pos (mul_pos rsSaddleScale_pos he)
  have hz : s eta ≠ 1 := by
    intro h
    rw [h] at ht
    norm_num at ht
  exact (((differentiableAt_riemannZeta hz).continuousAt.comp hs.continuousAt).sub
    ((sourceFiniteSums_continuousAt m ht).comp hs.continuousAt)).add
      ((((rsHankelPrefactor_differentiableAt ht).continuousAt.comp hs.continuousAt).mul
        (localPrefactor_continuousAt sigma m he)).mul
          (sourcePolynomialExpression_continuousAt sigma m N he))

theorem actualZetaPolynomialResidual_tendsto_left (sigma : ℝ) (n N : ℕ) :
    Tendsto (fun eta : ℝ => actualZetaPolynomialResidual sigma eta ⌊eta⌋₊ N)
      (𝓝[<] ((n : ℝ) + 1)) (𝓝 (actualZetaPolynomialResidual sigma ((n : ℝ) + 1) n N)) := by
  have h := (actualZetaPolynomialResidual_continuousAt sigma n N
    (show 0 < (n : ℝ) + 1 by positivity)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Iio ((n : ℝ) + 1)))
  apply h.congr'
  filter_upwards [floor_eventually_left n] with eta he
  rw [he]

theorem actualZetaPolynomialResidual_tendsto_right (sigma : ℝ) {n : ℕ}
    (hn : 0 < n) (N : ℕ) :
    Tendsto (fun eta : ℝ => actualZetaPolynomialResidual sigma eta ⌊eta⌋₊ N)
      (𝓝[≥] (n : ℝ)) (𝓝 (actualZetaPolynomialResidual sigma n n N)) := by
  have h := (actualZetaPolynomialResidual_continuousAt sigma n N
    (show (0 : ℝ) < n by exact_mod_cast hn)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ici (n : ℝ)))
  apply h.congr'
  filter_upwards [floor_eventually_right n] with eta he
  rw [he]

theorem actualZetaPolynomialResidual_norm_tendsto_right (sigma : ℝ) {n : ℕ}
    (hn : 0 < n) (N : ℕ) :
    Tendsto (fun eta : ℝ => ‖actualZetaPolynomialResidual sigma eta ⌊eta⌋₊ N‖)
      (𝓝[≥] (n : ℝ)) (𝓝 ‖actualZetaPolynomialResidual sigma n n N‖) :=
  (actualZetaPolynomialResidual_tendsto_right sigma hn N).norm

theorem actualZetaPolynomialResidual_eq_integral (sigma : ℝ) {eta : ℝ} {m : ℕ}
    (h0 : 0 < eta - m) (h1 : eta - m < 1) (N : ℕ) :
    let s : ℂ := (sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2
    actualZetaPolynomialResidual sigma eta m N =
      riemannZeta s - sourceFiniteSums s m -
        rsHankelPrefactor s * rsLocalPrefactor sigma eta m *
          (∫ y : ℝ, rsLocalPolynomialIntegrand sigma eta m N y) := by
  dsimp only
  rw [actualZetaPolynomialResidual, ← sourceLocalPolynomial_integral sigma h0 h1 N]
  ring

theorem actualZetaPolynomialResidual_eq_expanded (sigma : ℝ) {eta : ℝ} {m : ℕ}
    (he : 0 < eta) (hm : 0 < m) (N : ℕ) {R : ℝ}
    (hR : (m : ℝ) < R) (hR' : R < m + 1) :
    let s : ℂ := (sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2
    actualZetaPolynomialResidual sigma eta m N =
      rsHankelPrefactor s *
        (rsHankelTiltedC1 s m (Real.log R) +
          rsLocalPrefactor sigma eta m *
            (sourceGaussianPhase eta m *
              ∑ k ∈ Finset.range N, rsSaddleCoefficient sigma (rsSaddleScale * eta) k *
                (rsSaddleScale : ℂ) ^ k * correctionMoment k (sourcePhiParameter eta m))) := by
  dsimp only
  have ht : 0 < (((sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) : ℂ).im := by
    simpa only [← ofReal_pow, add_im, ofReal_im, mul_im, I_re, I_im,
      zero_mul, one_mul, zero_add, ofReal_re] using
        sq_pos_of_pos (mul_pos rsSaddleScale_pos he)
  rw [actualZetaPolynomialResidual, ← expanded_hankel_remainder hm ht hR hR']
  ring

#print axioms localPrefactor_continuousAt
#print axioms actualZetaPolynomialResidual_continuousAt
#print axioms actualZetaPolynomialResidual_tendsto_left
#print axioms actualZetaPolynomialResidual_tendsto_right
#print axioms actualZetaPolynomialResidual_norm_tendsto_right
#print axioms actualZetaPolynomialResidual_eq_integral
#print axioms actualZetaPolynomialResidual_eq_expanded

end LiuWang.Proof.Campaign20260915.ZetaIntegerEta
