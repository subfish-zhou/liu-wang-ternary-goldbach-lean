import LiuWang.Proof.Campaign20260915.ZetaMordell.SiegelOrientation

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory
open scoped Real ComplexConjugate

namespace LiuWang.Proof.Campaign20260915.ZetaMordell

theorem siegelPowerKernel_unweight (n : ℕ) (u : ℂ) (t : ℝ) :
    siegelLine t ^ n * siegelKernel u t =
      ((2 * Real.pi * I : ℂ) ^ n)⁻¹ * siegelWeightedKernel n u t := by
  have hq : (2 * Real.pi * I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  rw [siegelWeightedKernel, mul_pow]
  field_simp
  ring

theorem siegelPowerKernel_integrable (n : ℕ) (u : ℂ) :
    Integrable (fun t : ℝ => siegelLine t ^ n * siegelKernel u t) := by
  simp_rw [siegelPowerKernel_unweight]
  exact (siegelWeightedKernel_integrable n u).const_mul _

theorem siegelIntegral_power_moment (n : ℕ) (u : ℂ) :
    (∫ t : ℝ, siegelLine t ^ n * siegelKernel u t) =
      ((2 * Real.pi * I : ℂ) ^ n)⁻¹ * iteratedDeriv n siegelIntegral u := by
  simp_rw [siegelPowerKernel_unweight]
  rw [integral_const_mul, siegelIntegral_iteratedDeriv]
  rfl

theorem siegelCenteredKernel_expansion (n : ℕ) (u c : ℂ) (t : ℝ) :
    (siegelLine t - c) ^ n * siegelKernel u t =
      ∑ j ∈ Finset.range (n + 1),
        ((-c) ^ (n - j) * (n.choose j : ℂ)) * (siegelLine t ^ j * siegelKernel u t) := by
  rw [sub_eq_add_neg, add_pow, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem siegelCenteredKernel_integrable (n : ℕ) (u c : ℂ) :
    Integrable (fun t : ℝ => (siegelLine t - c) ^ n * siegelKernel u t) := by
  simp_rw [siegelCenteredKernel_expansion]
  exact integrable_finsetSum _ (fun j _ => (siegelPowerKernel_integrable j u).const_mul _)

theorem siegelIntegral_centered_moment (n : ℕ) (u c : ℂ) :
    (∫ t : ℝ, (siegelLine t - c) ^ n * siegelKernel u t) =
      ∑ j ∈ Finset.range (n + 1),
        ((-c) ^ (n - j) * (n.choose j : ℂ)) *
          (((2 * Real.pi * I : ℂ) ^ j)⁻¹ * iteratedDeriv j siegelIntegral u) := by
  simp_rw [siegelCenteredKernel_expansion]
  rw [integral_finsetSum _ (fun j _ => (siegelPowerKernel_integrable j u).const_mul _)]
  simp_rw [integral_const_mul, siegelIntegral_power_moment]

-- This is the actual integral in (30), with z = 2u / sqrt(2*pi), not a new Phi.
def correctionKernel (z : ℂ) (t : ℝ) : ℂ :=
  exp (Real.pi * I * (siegelLine t ^ 2 - 2 * (siegelLine t - (z + 1) / 2) ^ 2 + 1 / 8)) /
    (exp (2 * Real.pi * I * siegelLine t) - 1) * (-1 + I)

def correctionIntegral (z : ℂ) : ℂ := ∫ t : ℝ, correctionKernel z t

def correctionFactor (z : ℂ) : ℂ :=
  exp (Real.pi * I * (1 / 8 - (z + 1) ^ 2 / 2))

theorem correctionKernel_normalization (z : ℂ) (t : ℝ) :
    correctionKernel z t = correctionFactor z * siegelKernel (z + 1 / 2) t := by
  let B : ℂ := Real.pi * I * siegelLine t
  have hd : exp (2 * Real.pi * I * siegelLine t) - 1 =
      exp B * (exp B - exp (-B)) := by
    have h1 : exp B * exp (-B) = 1 := by rw [← exp_add]; simp
    have h2 : exp B * exp B = exp (2 * Real.pi * I * siegelLine t) := by
      rw [← exp_add]
      congr 1
      dsimp [B]
      ring
    rw [mul_sub, h1, h2]
  have hn :
      exp (Real.pi * I * (siegelLine t ^ 2 - 2 * (siegelLine t - (z + 1) / 2) ^ 2 + 1 / 8)) =
        correctionFactor z *
          exp (-Real.pi * I * siegelLine t ^ 2 + 2 * Real.pi * I * (z + 1 / 2) * siegelLine t) *
            exp B := by
    unfold correctionFactor
    rw [← exp_add, ← exp_add]
    congr 1
    dsimp [B]
    ring
  unfold correctionKernel
  rw [hd, hn, mul_comm (exp B) (exp B - exp (-B)),
    mul_div_mul_right _ _ (exp_ne_zero B)]
  dsimp only [B]
  simp only [siegelKernel, neg_mul]
  ring

theorem correctionKernel_integrable (z : ℂ) : Integrable (correctionKernel z) := by
  change Integrable (fun t : ℝ => correctionKernel z t)
  simp_rw [correctionKernel_normalization]
  exact (siegelKernel_integrable (z + 1 / 2)).const_mul _

theorem correctionIntegral_normalization (z : ℂ) :
    correctionIntegral z = correctionFactor z * siegelIntegral (z + 1 / 2) := by
  unfold correctionIntegral siegelIntegral
  simp_rw [correctionKernel_normalization]
  rw [integral_const_mul]

theorem correctionCenteredKernel_integrable (n : ℕ) (z : ℂ) :
    Integrable (fun t : ℝ => (siegelLine t - (z + 1) / 2) ^ n * correctionKernel z t) := by
  simp_rw [correctionKernel_normalization,
    show ∀ t : ℝ, (siegelLine t - (z + 1) / 2) ^ n *
      (correctionFactor z * siegelKernel (z + 1 / 2) t) =
      correctionFactor z * ((siegelLine t - (z + 1) / 2) ^ n * siegelKernel (z + 1 / 2) t)
      from fun t => by ring]
  exact (siegelCenteredKernel_integrable n (z + 1 / 2) ((z + 1) / 2)).const_mul _

theorem correctionIntegral_centered_moment (n : ℕ) (z : ℂ) :
    (∫ t : ℝ, (siegelLine t - (z + 1) / 2) ^ n * correctionKernel z t) =
      correctionFactor z * ∑ j ∈ Finset.range (n + 1),
        ((-((z + 1) / 2)) ^ (n - j) * (n.choose j : ℂ)) *
          (((2 * Real.pi * I : ℂ) ^ j)⁻¹ * iteratedDeriv j siegelIntegral (z + 1 / 2)) := by
  simp_rw [correctionKernel_normalization,
    show ∀ t : ℝ, (siegelLine t - (z + 1) / 2) ^ n *
      (correctionFactor z * siegelKernel (z + 1 / 2) t) =
      correctionFactor z * ((siegelLine t - (z + 1) / 2) ^ n * siegelKernel (z + 1 / 2) t)
      from fun t => by ring]
  rw [integral_const_mul, siegelIntegral_centered_moment]

theorem correctionKernel_generating_identity (z h : ℂ) (t : ℝ) :
    correctionKernel (z + h) t * exp (Real.pi * I * h ^ 2 / 2) =
      correctionKernel z t * exp (2 * Real.pi * I * (siegelLine t - (z + 1) / 2) * h) := by
  unfold correctionKernel
  rw [show exp (Real.pi * I * (siegelLine t ^ 2 -
      2 * (siegelLine t - (z + h + 1) / 2) ^ 2 + 1 / 8)) /
      (exp (2 * Real.pi * I * siegelLine t) - 1) * (-1 + I) *
      exp (Real.pi * I * h ^ 2 / 2) =
      (exp (Real.pi * I * (siegelLine t ^ 2 -
        2 * (siegelLine t - (z + h + 1) / 2) ^ 2 + 1 / 8)) *
        exp (Real.pi * I * h ^ 2 / 2)) /
          (exp (2 * Real.pi * I * siegelLine t) - 1) * (-1 + I) by ring,
    ← exp_add]
  rw [show Real.pi * I * (siegelLine t ^ 2 -
      2 * (siegelLine t - (z + h + 1) / 2) ^ 2 + 1 / 8) +
      Real.pi * I * h ^ 2 / 2 =
      Real.pi * I * (siegelLine t ^ 2 - 2 * (siegelLine t - (z + 1) / 2) ^ 2 + 1 / 8) +
        2 * Real.pi * I * (siegelLine t - (z + 1) / 2) * h by ring, exp_add]
  ring

theorem correctionGeneratingKernel_integrable (z h : ℂ) :
    Integrable (fun t : ℝ => correctionKernel z t *
      exp (2 * Real.pi * I * (siegelLine t - (z + 1) / 2) * h)) := by
  simp_rw [← correctionKernel_generating_identity]
  exact (correctionKernel_integrable (z + h)).mul_const _

theorem correctionIntegral_generating_identity (z h : ℂ) :
    correctionIntegral (z + h) * exp (Real.pi * I * h ^ 2 / 2) =
      ∫ t : ℝ, correctionKernel z t *
        exp (2 * Real.pi * I * (siegelLine t - (z + 1) / 2) * h) := by
  unfold correctionIntegral
  rw [← integral_mul_const]
  simp_rw [correctionKernel_generating_identity]

end LiuWang.Proof.Campaign20260915.ZetaMordell
