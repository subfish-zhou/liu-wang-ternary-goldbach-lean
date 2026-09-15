import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Consumer

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem upper_of_taylor {z t b : ℝ} (ht : 0 < t)
    (hTaylor : t ≤ expTaylor (z / 128)) (hpow : 1 ≤ b * t ^ (128 : ℕ)) :
    expNegUpper z ≤ b := by
  unfold expNegUpper
  have hp := pow_le_pow_left₀ ht.le hTaylor 128
  exact (one_div_le_one_div_of_le (pow_pos ht _) hp).trans
    ((div_le_iff₀ (pow_pos ht _)).mpr hpow)

theorem lower_of_taylor {z t b : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 128)
    (hTaylor : expTaylor (z / 128) + 1 / 1000000000000000000 ≤ t)
    (hb : 0 ≤ b) (hpow : b * t ^ (128 : ℕ) ≤ 1) :
    b ≤ expNegLower z := by
  have hbase := (expTaylor_bounds (x := z / 128) (by positivity) (by linarith)).1
  have h0 : 0 < expTaylor (z / 128) + 1 / 1000000000000000000 := by linarith
  have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0.le hTaylor 128) hb
  exact (le_div_iff₀ (pow_pos h0 _)).mpr (hp.trans hpow)

theorem upper_cell_of_exp {A u v b₁ b₂ b : ℝ} (huv : u ≤ v)
    (h₁ : expNegUpper (-tangent A ((u + v) / 2) u) ≤ b₁)
    (h₂ : expNegUpper (-tangent A ((u + v) / 2) v) ≤ b₂)
    (hb : (v - u) / 2 * (b₁ + b₂) ≤ b) :
    cellUpper A u v ≤ b :=
  (mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (by linarith : 0 ≤ (v - u) / 2)).trans hb

theorem lower_cell_of_exp {A u v e b : ℝ} (huv : u ≤ v)
    (he : e ≤ expNegLower (-((phase A u + phase A v) / 2)))
    (hb : b ≤ (v - u) * e) :
    b ≤ cellLower A u v :=
  hb.trans (mul_le_mul_of_nonneg_left he (sub_nonneg.mpr huv))

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
