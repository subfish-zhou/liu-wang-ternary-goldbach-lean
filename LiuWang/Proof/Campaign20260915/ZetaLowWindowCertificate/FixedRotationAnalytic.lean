import LiuWang.Proof.Campaign20260915.ZetaLowWindowCertificate.EMCorrection
import LiuWang.Proof.Campaign20260915.ZetaValidation.PrecisionPhase
import LiuWang.Proof.Campaign20260915.ZetaValidation.RationalEvaluation

set_option autoImplicit false
noncomputable section
open Complex
open scoped ComplexConjugate

namespace LiuWang.Proof.Campaign20260915.ZetaLowWindowCertificate

open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem fixed_angle_input_error {t t₀ ℓ ℓ₀ dt dℓ θ : ℝ}
    (ht : |t - t₀| ≤ dt) (hℓ : |ℓ - ℓ₀| ≤ dℓ) :
    |(t * ℓ - θ) - (t₀ * ℓ₀ - θ)| ≤
      dt * |ℓ₀| + (|t₀| + dt) * dℓ := by
  have hdt : 0 ≤ dt := (abs_nonneg _).trans ht
  have htB : |t| ≤ |t₀| + dt := by
    have h := abs_add_le (t - t₀) t₀
    rw [sub_add_cancel] at h
    linarith
  have hA := mul_le_mul_of_nonneg_right ht (abs_nonneg ℓ₀)
  have hB := mul_le_mul htB hℓ (abs_nonneg _) (by positivity)
  have hsum := abs_add_le ((t - t₀) * ℓ₀) (t * (ℓ - ℓ₀))
  rw [abs_mul, abs_mul] at hsum
  have hid : (t * ℓ - θ) - (t₀ * ℓ₀ - θ) =
      (t - t₀) * ℓ₀ + t * (ℓ - ℓ₀) := by ring
  rw [hid]
  exact hsum.trans (add_le_add hA hB)

theorem fixed_angle_rounded_error {t ℓ : ℝ} {t₀ ℓ₀ θ₀ dt dℓ : ℚ}
    (ht : |t - (t₀ : ℝ)| ≤ (dt : ℝ))
    (hℓ : |ℓ - (ℓ₀ : ℝ)| ≤ (dℓ : ℝ)) :
    |t * ℓ - (θ₀ : ℝ) -
      (roundRationalAt (10 ^ 24) (t₀ * ℓ₀ - θ₀) : ℝ)| ≤
      ((dt * |ℓ₀| + (|t₀| + dt) * dℓ + 1 / 10 ^ 24 : ℚ) : ℝ) := by
  have hi := fixed_angle_input_error (θ := (θ₀ : ℝ)) ht hℓ
  have hr := roundRationalAt_error (D := 10 ^ 24) (by norm_num) (t₀ * ℓ₀ - θ₀)
  have hs := abs_sub_le (t * ℓ - (θ₀ : ℝ))
    ((t₀ * ℓ₀ - θ₀ : ℚ) : ℝ)
    (roundRationalAt (10 ^ 24) (t₀ * ℓ₀ - θ₀) : ℝ)
  push_cast at hr hs ⊢
  rw [abs_sub_comm ((t₀ : ℝ) * (ℓ₀ : ℝ) - (θ₀ : ℝ))] at hs
  exact hs.trans (add_le_add hi (by norm_num at hr ⊢; exact hr))

theorem rounded_unit_phase_error {a E : ℝ} {q : ℚ}
    (ha : |a - (q : ℝ)| ≤ E) (hq : |q / 2 ^ 32| ≤ 1) :
    ‖exp ((a : ℂ) * I) -
      (unitPhaseAt (10 ^ 40) 40 32 (q / 2 ^ 32)).toComplex‖ ≤
      E + 1 / (10 : ℝ) ^ 24 := by
  have hs := unitPhaseAt_original_scale hq (k := 32) le_rfl
  have hid : (2 : ℝ) ^ 32 * ((q / 2 ^ 32 : ℚ) : ℝ) = (q : ℝ) := by
    push_cast
    ring
  rw [hid] at hs
  exact (norm_sub_le_norm_sub_add_norm_sub _ (exp (((q : ℝ) : ℂ) * I)) _).trans
    (add_le_add ((unitPhase_distance_le _ _).trans ha) hs)

theorem fixed_rotated_nat_power {n : ℕ} (hn : 1 ≤ n) (t θ : ℝ) :
    (n : ℂ) ^ (-criticalPoint t) * exp ((θ : ℂ) * I) =
      ((1 / Real.sqrt (n : ℝ) : ℝ) : ℂ) *
        conj (exp (((t * Real.log (n : ℝ) - θ : ℝ) : ℂ) * I)) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have he : -criticalPoint t = -(1 / 2 : ℂ) + (-t : ℂ) * I := by
    apply Complex.ext <;> simp [criticalPoint]
  rw [he, cpow_add _ _ hnC, cpow_neg_half_of_nat hn, cpow_def_of_ne_zero hnC]
  have hlog : log (n : ℂ) = ((Real.log (n : ℝ) : ℝ) : ℂ) := by
    simpa only [ofReal_natCast] using (Complex.ofReal_log (Nat.cast_nonneg n)).symm
  rw [hlog, mul_assoc, ← exp_add, ← exp_conj]
  congr 2
  simp only [map_mul, conj_ofReal, conj_I]
  push_cast
  ring

theorem fixed_rotated_power_error {n : ℕ} (hn : 1 ≤ n)
    {t θ w ew ep : ℝ} {v : ℂ} (hw : 0 ≤ w)
    (he : |1 / Real.sqrt (n : ℝ) - w| ≤ ew)
    (hp : ‖exp (((t * Real.log (n : ℝ) - θ : ℝ) : ℂ) * I) - v‖ ≤ ep) :
    ‖(n : ℂ) ^ (-criticalPoint t) * exp ((θ : ℂ) * I) -
      (w : ℂ) * conj v‖ ≤ ew + w * ep := by
  rw [fixed_rotated_nat_power hn]
  let u := exp (((t * Real.log (n : ℝ) - θ : ℝ) : ℂ) * I)
  have hu : ‖conj u‖ = 1 := by
    rw [norm_conj]
    exact Complex.norm_exp_ofReal_mul_I _
  have hconj : ‖conj u - conj v‖ ≤ ep := by
    rw [← map_sub, norm_conj]
    exact hp
  have hid : ((1 / Real.sqrt (n : ℝ) : ℝ) : ℂ) * conj u - (w : ℂ) * conj v =
      ((1 / Real.sqrt (n : ℝ) - w : ℝ) : ℂ) * conj u +
        (w : ℂ) * (conj u - conj v) := by push_cast; ring
  change ‖((1 / Real.sqrt (n : ℝ) : ℝ) : ℂ) * conj u - (w : ℂ) * conj v‖ ≤ _
  rw [hid]
  calc
    _ ≤ ‖((1 / Real.sqrt (n : ℝ) - w : ℝ) : ℂ) * conj u‖ +
        ‖(w : ℂ) * (conj u - conj v)‖ := norm_add_le _ _
    _ = |1 / Real.sqrt (n : ℝ) - w| + w * ‖conj u - conj v‖ := by
      rw [norm_mul, norm_mul, hu, mul_one, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hw]
    _ ≤ _ := add_le_add he (mul_le_mul_of_nonneg_left hconj hw)

#print axioms fixed_angle_rounded_error
#print axioms fixed_rotated_nat_power
#print axioms fixed_rotated_power_error

end LiuWang.Proof.Campaign20260915.ZetaLowWindowCertificate
