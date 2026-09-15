import LiuWang.Proof.SourceRoute.MajorException.AllInteractions

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.SourceRoute.MajorException

theorem source_linear_decimal :
    (2.8959 : ℝ)*2.82682*0.0000025636 ≤ 0.000021 := by norm_num

theorem source_quadratic_decimal :
    (8.2914 : ℝ)*0.00013 ≤ 0.00108 := by norm_num

theorem source_cubic_decimal :
    (3.35804 : ℝ)*0.028 ≤ 0.09403 := by norm_num

def sourceCaseIICost : ℝ :=
  0.00000005 + 0.00000002 + 0.00000002 +
    0.000021 + 0.00000004 + 0.00318 + 0.00108 + 0.0001 + 0.09403

theorem sourceCaseIICost_exact : sourceCaseIICost = (0.09841113 : ℝ) := by
  norm_num [sourceCaseIICost]

theorem source_remainder_ratio {L : ℝ} (hL : 3100 ≤ L) :
    3/L^9 ≤ (0.000001 : ℝ) := by
  have h1 : 1 ≤ L := by linarith
  have hpow : L^2 ≤ L^9 := pow_le_pow_right₀ h1 (by decide)
  have hsq : (3100 : ℝ)^2 ≤ L^2 :=
    pow_le_pow_left₀ (by norm_num) hL 2
  apply (div_le_iff₀ (by positivity : 0 < L^9)).mpr
  nlinarith

theorem source_caseII_scalar {L X : ℝ} (hL : 3100 ≤ L) (hX : 0 ≤ X) :
    0.5577*X ≤ (0.656145-sourceCaseIICost)*X - 3*X/L^9 := by
  have h := mul_le_mul_of_nonneg_right (source_remainder_ratio hL) hX
  rw [div_mul_eq_mul_div] at h
  rw [sourceCaseIICost_exact]
  nlinarith

theorem lambda_model_remainder_ratio {L : ℝ} (hL : 3100 ≤ L) :
    6760/L^4 ≤ (0.000001 : ℝ) := by
  have hpow : (3100 : ℝ)^4 ≤ L^4 :=
    pow_le_pow_left₀ (by norm_num) hL 4
  apply (div_le_iff₀ (by positivity : 0 < L^4)).mpr
  nlinarith

theorem lambda_model_caseII_scalar {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    0.5577*(N : ℝ)^2 ≤ (0.65617-sourceCaseIICost)*(N : ℝ)^2 -
      6760*(N : ℝ)^2/sourceL N^4 := by
  have h := mul_le_mul_of_nonneg_right
    (lambda_model_remainder_ratio (sourceL_ge_3100 hN)) (sq_nonneg (N : ℝ))
  rw [div_mul_eq_mul_div] at h
  rw [sourceCaseIICost_exact]
  nlinarith

end LiuWang.Proof.SourceRoute.MajorException
