import LiuWang.Proof.Campaign20260915.ZetaIntegerEta.EndpointAudit
import LiuWang.Proof.Campaign20260915.ZetaValidation.CentralInfiniteContour

set_option autoImplicit false
noncomputable section
open Complex Filter Set MeasureTheory
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaIntegerEta
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

def sourceZetaPolynomialRemainder (sigma eta : ℝ) (m N : ℕ) : ℂ :=
  let s : ℂ := (sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2
  riemannZeta s - sourceFiniteSums s m -
    rsHankelPrefactor s * rsLocalPrefactor sigma eta m *
      (sourceGaussianPhase eta m *
        ∑ k ∈ Finset.range N, rsSaddleCoefficient sigma (rsSaddleScale * eta) k *
          (rsSaddleScale : ℂ) ^ k * correctionMoment k (sourcePhiParameter eta m))

theorem sourceZetaPolynomialRemainder_continuousAt (sigma : ℝ) (m N : ℕ)
    {eta : ℝ} (he : 0 < eta) :
    ContinuousAt (fun x : ℝ => sourceZetaPolynomialRemainder sigma x m N) eta := by
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
  have hp : ContinuousAt (fun x : ℝ => rsLocalPrefactor sigma x m) eta := by
    unfold rsLocalPrefactor
    apply ContinuousAt.mul _ (by fun_prop)
    exact Complex.continuous_ofReal.continuousAt.cpow (by fun_prop)
      (mem_slitPlane_iff.mpr (Or.inl he))
  exact (((differentiableAt_riemannZeta hz).continuousAt.comp hs.continuousAt).sub
    ((sourceFiniteSums_continuousAt m ht).comp hs.continuousAt)).sub
      ((((rsHankelPrefactor_differentiableAt ht).continuousAt.comp hs.continuousAt).mul hp).mul
        (sourcePolynomialExpression_continuousAt sigma m N he))

theorem sourceZetaPolynomialRemainder_tendsto_left (sigma : ℝ) (n N : ℕ) :
    Tendsto (fun eta : ℝ => sourceZetaPolynomialRemainder sigma eta ⌊eta⌋₊ N)
      (𝓝[<] ((n : ℝ) + 1)) (𝓝 (sourceZetaPolynomialRemainder sigma ((n : ℝ) + 1) n N)) := by
  have h := (sourceZetaPolynomialRemainder_continuousAt sigma n N
    (show 0 < (n : ℝ) + 1 by positivity)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Iio ((n : ℝ) + 1)))
  apply h.congr'
  filter_upwards [floor_eventually_left n] with eta he
  rw [he]

theorem sourceZetaPolynomialRemainder_tendsto_right (sigma : ℝ) {n : ℕ}
    (hn : 0 < n) (N : ℕ) :
    Tendsto (fun eta : ℝ => sourceZetaPolynomialRemainder sigma eta ⌊eta⌋₊ N)
      (𝓝[≥] (n : ℝ)) (𝓝 (sourceZetaPolynomialRemainder sigma n n N)) := by
  have h := (sourceZetaPolynomialRemainder_continuousAt sigma n N
    (show (0 : ℝ) < n by exact_mod_cast hn)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ici (n : ℝ)))
  apply h.congr'
  filter_upwards [floor_eventually_right n] with eta he
  rw [he]

theorem sourceZetaPolynomialRemainder_norm_tendsto_right (sigma : ℝ) {n : ℕ}
    (hn : 0 < n) (N : ℕ) :
    Tendsto (fun eta : ℝ => ‖sourceZetaPolynomialRemainder sigma eta ⌊eta⌋₊ N‖)
      (𝓝[≥] (n : ℝ)) (𝓝 ‖sourceZetaPolynomialRemainder sigma n n N‖) :=
  (sourceZetaPolynomialRemainder_tendsto_right sigma hn N).norm

theorem sourceZetaPolynomialRemainder_eq_integral (sigma : ℝ) {eta : ℝ} {m : ℕ}
    (h0 : 0 < eta - m) (h1 : eta - m < 1) (N : ℕ) :
    let s : ℂ := (sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2
    sourceZetaPolynomialRemainder sigma eta m N =
      riemannZeta s - sourceFiniteSums s m +
        rsHankelPrefactor s * rsLocalPrefactor sigma eta m *
          (∫ y : ℝ, rsLocalPolynomialIntegrand sigma eta m N y) := by
  dsimp only
  rw [sourceZetaPolynomialRemainder, ← sourceLocalPolynomial_integral sigma h0 h1 N]
  ring

theorem sourceZetaPolynomialRemainder_eq_C2 (sigma : ℝ) (hs : sigma ≤ 1)
    {eta : ℝ} {m : ℕ} (hm : 0 < m) (h0 : 0 < eta - m) (h1 : eta - m < 1) (N : ℕ) :
    let s : ℂ := (sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2
    sourceZetaPolynomialRemainder sigma eta m N =
      rsHankelPrefactor s *
        (rsSourceC2 s eta m + rsLocalPrefactor sigma eta m *
          (∫ y : ℝ, rsLocalPolynomialIntegrand sigma eta m N y)) := by
  dsimp only
  have he : 0 < eta := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have ht : 0 < (((sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) : ℂ).im := by
    simpa only [← ofReal_pow, add_im, ofReal_im, mul_im, I_re, I_im,
      zero_mul, one_mul, zero_add, ofReal_re] using
        sq_pos_of_pos (mul_pos rsSaddleScale_pos he)
  have hs' : (((sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) : ℂ).re ≤ 1 := by
    simpa only [← ofReal_pow, add_re, ofReal_re, mul_re, I_re, I_im,
      ofReal_im, zero_mul, mul_zero, sub_zero, add_zero] using hs
  have hz := zeta_eq_source_sums_add_C2 hm ht hs'
    (by linarith : (m : ℝ) < eta) (by linarith : eta < m + 1)
  change riemannZeta _ = sourceFiniteSums _ m + _ at hz
  rw [sourceZetaPolynomialRemainder_eq_integral sigma h0 h1 N, hz]
  ring

theorem actual_C2_polynomial_remainder_tendsto_right (sigma : ℝ) (hs : sigma ≤ 1)
    {n : ℕ} (hn : 0 < n) (N : ℕ) :
    Tendsto (fun eta : ℝ =>
      let s : ℂ := (sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2
      rsHankelPrefactor s *
        (rsSourceC2 s eta ⌊eta⌋₊ + rsLocalPrefactor sigma eta ⌊eta⌋₊ *
          (∫ y : ℝ, rsLocalPolynomialIntegrand sigma eta ⌊eta⌋₊ N y)))
      (𝓝[>] (n : ℝ)) (𝓝 (sourceZetaPolynomialRemainder sigma n n N)) := by
  have h := (sourceZetaPolynomialRemainder_tendsto_right sigma hn N).mono_left
    (nhdsWithin_mono _ (show Ioi (n : ℝ) ⊆ Ici (n : ℝ) by
      intro x hx
      simp only [mem_Ioi, mem_Ici] at hx ⊢
      exact hx.le))
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsGT (show (n : ℝ) < n + 1 by linarith)] with eta he
  rw [Nat.floor_eq_on_Ico n eta ⟨he.1.le, he.2⟩]
  exact sourceZetaPolynomialRemainder_eq_C2 sigma hs hn
    (by linarith [he.1]) (by linarith [he.2]) N

theorem actual_C2_polynomial_remainder_tendsto_left (sigma : ℝ) (hs : sigma ≤ 1)
    {n : ℕ} (hn : 0 < n) (N : ℕ) :
    Tendsto (fun eta : ℝ =>
      let s : ℂ := (sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2
      rsHankelPrefactor s *
        (rsSourceC2 s eta ⌊eta⌋₊ + rsLocalPrefactor sigma eta ⌊eta⌋₊ *
          (∫ y : ℝ, rsLocalPolynomialIntegrand sigma eta ⌊eta⌋₊ N y)))
      (𝓝[<] ((n : ℝ) + 1)) (𝓝 (sourceZetaPolynomialRemainder sigma ((n : ℝ) + 1) n N)) := by
  apply (sourceZetaPolynomialRemainder_tendsto_left sigma n N).congr'
  filter_upwards [Ioo_mem_nhdsLT (show (n : ℝ) < n + 1 by linarith)] with eta he
  rw [Nat.floor_eq_on_Ico n eta ⟨he.1.le, he.2⟩]
  exact sourceZetaPolynomialRemainder_eq_C2 sigma hs hn
    (by linarith [he.1]) (by linarith [he.2]) N

#print axioms sourceZetaPolynomialRemainder_continuousAt
#print axioms sourceZetaPolynomialRemainder_tendsto_left
#print axioms sourceZetaPolynomialRemainder_tendsto_right
#print axioms sourceZetaPolynomialRemainder_norm_tendsto_right
#print axioms sourceZetaPolynomialRemainder_eq_integral
#print axioms sourceZetaPolynomialRemainder_eq_C2
#print axioms actual_C2_polynomial_remainder_tendsto_right
#print axioms actual_C2_polynomial_remainder_tendsto_left

end LiuWang.Proof.Campaign20260915.ZetaIntegerEta
