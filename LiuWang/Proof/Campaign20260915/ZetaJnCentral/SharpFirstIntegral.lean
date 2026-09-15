import LiuWang.Proof.Campaign20260915.ZetaJnCentral.FirstCoefficients
import LiuWang.Proof.Campaign20260915.ZetaJnCentral.MediumBudget
import LiuWang.Proof.Campaign20260915.ZetaJnCentral.SharpSeventhIntegral

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem jn_one_correction_budget {eta : ℝ} {m : ℕ} (he : 11 ≤ eta)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) :
    ‖∑ n ∈ Finset.range 11, scaledCoefficient eta (n + 1) *
      (∫ y : ℝ in (eta / 2)..(-eta / 2), gaussianMonomial eta m n y)‖ ≤ (77 / 125) / eta := by
  have he0 : 0 < eta := by linarith
  have hb (n : ℕ) (hn : n ∈ Finset.range 11) :
      ‖scaledCoefficient eta (n + 1) *
        (∫ y : ℝ in (eta / 2)..(-eta / 2), gaussianMonomial eta m n y)‖ ≤
        firstCoefficientEnvelope n * exactGaussianBudget Real.pi n / eta := by
    have hcoef := scaled_weighted_to_norm he0 (n + 1) 1
      (by simpa only [pow_one] using firstCoefficientEnvelope_bound he n (Finset.mem_range.mp hn))
    simp only [pow_one] at hcoef
    rw [norm_mul, intervalIntegral.integral_symm (-eta / 2) (eta / 2), norm_neg]
    exact (mul_le_mul hcoef
      (gaussianMonomial_exact_interval eta m n hm0 hm1 (by linarith))
      (norm_nonneg _) (div_nonneg (firstCoefficientEnvelope_nonneg n) he0.le)).trans_eq (by ring)
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum hb).trans
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right first_correction_scalar he0.le

theorem jn_one_sharp {eta : ℝ} {m : ℕ} (he : 11 ≤ eta)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) :
    ‖∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta m 1 y‖ ≤
      (731 / 1000) / eta := by
  have hs := jn_finite_remainder_split (by linarith : 0 < eta) hm0 hm1 0 11
  simp only [Nat.zero_add, Nat.reduceAdd] at hs
  rw [hs]
  apply (norm_add_le _ _).trans
  exact (add_le_add (jn_medium_source_budget he hm0 hm1)
    (jn_one_correction_budget he hm0 hm1)).trans_eq (by ring)

theorem jn_floor_one_sharp {eta : ℝ} (he : 11 ≤ eta) :
    IntervalIntegrable (rsJnIntegrand (1 / 2) eta ⌊eta⌋₊ 1) volume (eta / 2) (-eta / 2) ∧
    ‖∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand (1 / 2) eta ⌊eta⌋₊ 1 y‖ ≤
      (731 / 1000) / eta := by
  have he0 : 0 < eta := by linarith
  have h0 := Nat.zero_le_self_sub_floor he0.le
  have h1 := (Nat.self_sub_floor_lt_one eta).le
  exact ⟨jn_local_integrable (1 / 2) he0 h0 h1 0, jn_one_sharp he h0 h1⟩

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
