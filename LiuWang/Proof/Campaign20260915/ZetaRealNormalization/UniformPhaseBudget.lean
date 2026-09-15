import LiuWang.Proof.Campaign20260915.ZetaRealNormalization.HeightInterface
import LiuWang.Proof.Campaign20260915.ZetaValidation.StirlingRational

set_option autoImplicit false
noncomputable section
open Complex

namespace LiuWang.Proof.Campaign20260915.ZetaRealNormalization
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

theorem arctan_abs_le (x : ℝ) : |Real.arctan x| ≤ |x| := by
  have hb (y : ℝ) (_ : y ∈ Set.univ) : ‖deriv Real.arctan y‖ ≤ (1 : ℝ) := by
    rw [Real.deriv_arctan, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (div_le_one (by positivity : 0 < 1 + y ^ 2)).mpr (by nlinarith [sq_nonneg y])
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun y (_ : y ∈ Set.univ) => Real.differentiableAt_arctan y) hb
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ 0) (Set.mem_univ x)
  simpa only [Real.arctan_zero, sub_zero, one_mul, Real.norm_eq_abs] using h

theorem source_stirling_offset {t : ℝ} (ht : 0 < t) :
    criticalGammaStirlingArgument t - sourceLeadingArgument (sourceHeightScale t) =
      t / 4 * Real.log (1 + 1 / (4 * t ^ 2)) + Real.arctan (1 / (2 * t)) / 4 := by
  have hm : 1 / 16 + t ^ 2 / 4 = (t / 2) ^ 2 * (1 + 1 / (4 * t ^ 2)) := by
    field_simp
    ring
  have hl : Real.log (1 / 16 + t ^ 2 / 4) =
      2 * Real.log (t / 2) + Real.log (1 + 1 / (4 * t ^ 2)) := by
    rw [hm, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    norm_num
  have hp : Real.log (t / (2 * Real.pi)) = Real.log (t / 2) - Real.log Real.pi := by
    rw [show t / (2 * Real.pi) = (t / 2) / Real.pi by ring,
      Real.log_div (by positivity) Real.pi_ne_zero]
  rw [criticalGammaStirlingArgument_elementary ht, sourceLeadingArgument_heightScale ht.le, hl, hp]
  ring

theorem source_stirling_offset_bounds {t : ℝ} (ht : 0 < t) :
    0 ≤ criticalGammaStirlingArgument t - sourceLeadingArgument (sourceHeightScale t) ∧
      criticalGammaStirlingArgument t - sourceLeadingArgument (sourceHeightScale t) ≤
        3 / (16 * t) := by
  rw [source_stirling_offset ht]
  have hx : 0 ≤ 1 / (4 * t ^ 2) := by positivity
  have hl0 : 0 ≤ Real.log (1 + 1 / (4 * t ^ 2)) := Real.log_nonneg (by linarith)
  have ha0 : 0 ≤ Real.arctan (1 / (2 * t)) := Real.arctan_nonneg.mpr (by positivity)
  have hl : Real.log (1 + 1 / (4 * t ^ 2)) ≤ 1 / (4 * t ^ 2) := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 1 / (4 * t ^ 2))
    linarith
  have ha : Real.arctan (1 / (2 * t)) ≤ 1 / (2 * t) := by
    simpa only [abs_of_nonneg ha0, abs_of_pos (by positivity : 0 < 1 / (2 * t))] using
      arctan_abs_le (1 / (2 * t))
  constructor
  · positivity
  · calc
      _ ≤ t / 4 * (1 / (4 * t ^ 2)) + (1 / (2 * t)) / 4 :=
        add_le_add (mul_le_mul_of_nonneg_left hl (by positivity))
          (div_le_div_of_nonneg_right ha (by norm_num))
      _ = _ := by field_simp; ring

theorem sourceHeightScale_time {eta : ℝ} (he : 0 ≤ eta) :
    sourceHeightScale (sourceTime eta) = eta := by
  rw [sourceHeightScale, sourceTime_eq,
    show 2 * Real.pi * eta ^ 2 / (2 * Real.pi) = eta ^ 2 by field_simp,
    Real.sqrt_sq he]

theorem sourceGammaPhaseBudget_uniform {eta : ℝ} (he : 0 < eta) :
    sourceGammaPhaseBudget eta ≤ 7 / (16 * sourceTime eta) := by
  have hb := source_stirling_offset_bounds (sourceTime_pos he)
  rw [sourceHeightScale_time he.le] at hb
  unfold sourceGammaPhaseBudget
  rw [abs_sub_comm, abs_of_nonneg hb.1]
  calc
    _ ≤ 3 / (16 * sourceTime eta) + 1 / (4 * sourceTime eta) :=
      add_le_add hb.2 le_rfl
    _ = _ := by ring

theorem sourcePhaseBudget_uniform {eta : ℝ} (he : 0 < eta) :
    sourcePhaseBudget eta ≤ 7 / (16 * sourceTime eta) +
      Real.exp (-Real.pi * sourceTime eta) := by
  exact add_le_add (sourceGammaPhaseBudget_uniform he) le_rfl

theorem sourceRealPhaseBudget_uniform {eta : ℝ} (he : 0 < eta) :
    sourceRealPhaseBudget eta ≤ 49 / (512 * sourceTime eta ^ 2) +
      Real.exp (-Real.pi * sourceTime eta) := by
  have hn : 0 ≤ sourceGammaPhaseBudget eta := by
    unfold sourceGammaPhaseBudget
    have ht := sourceTime_pos he
    positivity
  have hs := pow_le_pow_left₀ hn (sourceGammaPhaseBudget_uniform he) 2
  unfold sourceRealPhaseBudget
  calc
    _ ≤ (7 / (16 * sourceTime eta)) ^ 2 / 2 + Real.exp (-Real.pi * sourceTime eta) :=
      add_le_add (div_le_div_of_nonneg_right hs (by norm_num)) le_rfl
    _ = _ := by ring

def sourceSevenUniformBudget (eta z : ℝ) : ℝ :=
  (49 / (512 * sourceTime eta ^ 2) + Real.exp (-Real.pi * sourceTime eta)) *
      |sourceRealCorrection eta z| +
    (7 / (16 * sourceTime eta) + Real.exp (-Real.pi * sourceTime eta)) *
      |sourceImaginaryCorrection eta z| +
    sourceExtraDerivativeBudget eta z

theorem sourceSevenRealBudget_uniform {eta : ℝ} (he : 0 < eta) (z : ℝ) :
    sourceSevenRealBudget eta z ≤ sourceSevenUniformBudget eta z := by
  exact add_le_add (add_le_add
    (mul_le_mul_of_nonneg_right (sourceRealPhaseBudget_uniform he) (abs_nonneg _))
    (mul_le_mul_of_nonneg_right (sourcePhaseBudget_uniform he) (abs_nonneg _))) le_rfl

theorem normalized_source_seven_uniform_budget {eta : ℝ} {m : ℕ}
    (h0 : 0 < eta - m) (h1 : eta - m < 1) :
    |sourceSevenNormalized eta m -
      sourceSignedAmplitude eta m * sourceRealCorrection eta (sourcePhiParameter eta m)| ≤
        eta ^ (-(1 / 2 : ℝ)) * sourceSevenUniformBudget eta (sourcePhiParameter eta m) := by
  have he : 0 < eta := by linarith [Nat.cast_nonneg (α := ℝ) m]
  exact (normalized_source_seven_real_budget h0 h1).trans
    (mul_le_mul_of_nonneg_left (sourceSevenRealBudget_uniform he _)
      (Real.rpow_nonneg he.le _))

theorem normalized_central_seven_uniform_budget {eta : ℝ}
    (he : 1 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    |sourceCentralNormalized eta - sourceJnNormalized eta -
      sourceSignedAmplitude eta ⌊eta⌋₊ * sourceRealCorrection eta (sourcePhiParameter eta ⌊eta⌋₊)| ≤
      eta ^ (-(1 / 2 : ℝ)) *
        (120000 / eta * Real.exp (-Real.pi * eta ^ 2 / 8) +
          sourceSevenUniformBudget eta (sourcePhiParameter eta ⌊eta⌋₊)) := by
  exact (normalized_central_seven_real_budget he hint).trans
    (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (sourceSevenRealBudget_uniform (by linarith : 0 < eta) _))
      (Real.rpow_nonneg (by linarith : 0 ≤ eta) _))

theorem normalized_zeta_seven_uniform_budget_at_height {t : ℝ} {m : ℕ}
    (ht : 0 < t) (hm : 0 < m)
    (h0 : 0 < sourceHeightScale t - m) (h1 : sourceHeightScale t - m < 1) :
    |normalizedCriticalZeta t -
      (sourceRealMainSum t m +
        sourceSignedAmplitude (sourceHeightScale t) m *
          sourceRealCorrection (sourceHeightScale t) (sourcePhiParameter (sourceHeightScale t) m))| ≤
      |sourceExpandedResidual (sourceHeightScale t) m| +
        sourceHeightScale t ^ (-(1 / 2 : ℝ)) *
          sourceSevenUniformBudget (sourceHeightScale t) (sourcePhiParameter (sourceHeightScale t) m) := by
  have he := sourceHeightScale_pos ht
  have h := normalized_zeta_source_seven_real_budget hm h0 h1
  rw [sourceTime_heightScale ht.le] at h
  exact h.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (sourceSevenRealBudget_uniform he _) (Real.rpow_nonneg he.le _)))

#print axioms sourceGammaPhaseBudget_uniform
#print axioms normalized_central_seven_uniform_budget
#print axioms normalized_zeta_seven_uniform_budget_at_height

end LiuWang.Proof.Campaign20260915.ZetaRealNormalization
