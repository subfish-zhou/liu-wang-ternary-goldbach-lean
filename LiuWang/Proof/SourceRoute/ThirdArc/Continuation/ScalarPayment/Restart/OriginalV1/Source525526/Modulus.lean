import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source525526.Scalar
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524.FrozenDensity

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source525526

theorem modulus_scalar {L : ℝ} {q : ℕ} (hL : 3100 ≤ L)
    (hq : L ^ (3 : ℕ) ≤ (q : ℝ)) (hq1 : (q : ℝ) ≤ L ^ (6 : ℕ)) (K d : ℝ) :
    originalScalar K d L (Real.log q / Real.log L) = logScalar K d L (Real.log q) := by
  have hl : Real.log L ≠ 0 := (Real.log_pos (by linarith : 1 < L)).ne'
  have _hqparam := Source524.modulus_parameter hL hq hq1
  rw [originalScalar_eq_logScalar (by linarith) K d, div_mul_cancel₀ _ hl]

theorem original_weight_le_scalar {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N) (K d : ℝ) (hK : 0 ≤ K)
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q) :
    ((N : ℝ) * Real.sqrt q / q.totient) *
      (lowCoefficient (59 / 60) * (K *
        Real.exp (-d * sourceL N / Real.log ((q : ℝ) * lowHeight)))) ≤
      (N : ℝ) / sourceL N * originalScalar K d (sourceL N)
        (Real.log q / Real.log (sourceL N)) := by
  have hL := sourceL_ge_3100 hN
  have hL0 : sourceL N ≠ 0 := by linarith
  have hqR : (0 : ℝ) < q := (pow_pos (by linarith : 0 < sourceL N) 3).trans_le hq
  have hw := Source524.sqrt_totient_original (Nat.cast_pos.mp hqR) htotient
  have hc := lowCoefficient_nonneg (by norm_num : (0 : ℝ) < 59 / 60)
  have hh : Real.log ((q : ℝ) * lowHeight) = Real.log q + Real.log lowHeight :=
    Real.log_mul hqR.ne' lowHeight_pos.ne'
  have h := mul_le_mul_of_nonneg_left hw
    (show 0 ≤ (N : ℝ) * lowCoefficient (59 / 60) * K *
      Real.exp (-d * sourceL N / Real.log ((q : ℝ) * lowHeight)) by positivity)
  rw [modulus_scalar hL hq hq1 K d]
  unfold logScalar
  rw [hh] at h ⊢
  have heq : (N : ℝ) / sourceL N *
      (K * lowCoefficient (59 / 60) * sourceL N * Source524.logNu (Real.log q) *
        Real.exp (-(1 / 2 : ℝ) * Real.log q) *
          Real.exp (-d * sourceL N / (Real.log q + Real.log lowHeight))) =
      (N : ℝ) * lowCoefficient (59 / 60) * K *
        Real.exp (-d * sourceL N / (Real.log q + Real.log lowHeight)) *
          (Source524.logNu (Real.log q) * Real.exp (-(1 / 2 : ℝ) * Real.log q)) := by
    field_simp
  rw [heq]
  simp only [div_eq_mul_inv] at h ⊢
  nlinarith only [h]

theorem original_weight525_paid {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q) :
    ((N : ℝ) * Real.sqrt q / q.totient) *
      (lowCoefficient (59 / 60) * (14000 *
        Real.exp (-0.2067 * sourceL N / Real.log ((q : ℝ) * lowHeight)))) ≤
      (3 / 100000 : ℝ) * (N : ℝ) / sourceL N := by
  have hL := sourceL_ge_3100 hN
  have hx := Source524.modulus_parameter hL hq hq1
  have h := mul_le_mul_of_nonneg_left
    (scalar525_paid (sourceL N) _ hL hx.1 hx.2.1)
    (show 0 ≤ (N : ℝ) / sourceL N from div_nonneg (Nat.cast_nonneg _) (by linarith))
  have hw := original_weight_le_scalar hN hq hq1 14000 0.2067 (by norm_num) htotient
  change _ ≤ (N : ℝ) / sourceL N * scalar525 (sourceL N) _ at hw
  simp only [div_eq_mul_inv] at h hw ⊢
  nlinarith only [h, hw]

theorem original_weight526_paid {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q) :
    ((N : ℝ) * Real.sqrt q / q.totient) *
      (lowCoefficient (59 / 60) * (2 *
        Real.exp (-0.10367089 * sourceL N / Real.log ((q : ℝ) * lowHeight)))) ≤
      (3 / 100000 : ℝ) * (N : ℝ) / sourceL N := by
  have hL := sourceL_ge_3100 hN
  have hx := Source524.modulus_parameter hL hq hq1
  have h := mul_le_mul_of_nonneg_left
    (scalar526_paid (sourceL N) _ hL hx.1 hx.2.1)
    (show 0 ≤ (N : ℝ) / sourceL N from div_nonneg (Nat.cast_nonneg _) (by linarith))
  have hw := original_weight_le_scalar hN hq hq1 2 0.10367089 (by norm_num) htotient
  change _ ≤ (N : ℝ) / sourceL N * scalar526 (sourceL N) _ at hw
  simp only [div_eq_mul_inv] at h hw ⊢
  nlinarith only [h, hw]

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source525526
