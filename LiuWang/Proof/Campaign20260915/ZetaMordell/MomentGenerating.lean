import LiuWang.Proof.Campaign20260915.ZetaMordell.PhiBridge

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory
open scoped Real

namespace LiuWang.Proof.Campaign20260915.ZetaMordell

def correctionMoment (n : ℕ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, (siegelLine t - (z + 1) / 2) ^ n * correctionKernel z t

def correctionGenerating (z h : ℂ) : ℂ :=
  correctionIntegral (z + h) * exp (Real.pi * I * h ^ 2 / 2)

theorem correctionGenerating_analytic (z h : ℂ) :
    AnalyticAt ℂ (correctionGenerating z) h :=
  ((correctionIntegral_analytic (z + h)).comp (by fun_prop)).mul ((by fun_prop :
    AnalyticAt ℂ (fun w : ℂ => Real.pi * I * w ^ 2 / 2) h).cexp)

theorem correctionGenerating_normalization (z h : ℂ) :
    correctionGenerating z h = correctionFactor z *
      (siegelIntegral ((z + 1 / 2) + h) * exp ((-Real.pi * I * (z + 1)) * h)) := by
  unfold correctionGenerating
  rw [correctionIntegral_normalization]
  unfold correctionFactor
  have he : exp (Real.pi * I * (1 / 8 - (z + h + 1) ^ 2 / 2)) *
      exp (Real.pi * I * h ^ 2 / 2) =
      exp (Real.pi * I * (1 / 8 - (z + 1) ^ 2 / 2)) *
        exp ((-Real.pi * I * (z + 1)) * h) := by
    rw [← exp_add, ← exp_add]
    congr 1
    ring
  rw [show z + h + (1 / 2 : ℂ) = (z + 1 / 2) + h by ring,
    mul_right_comm, he]
  ring

private theorem weighted_power_cancel {q : ℂ} (hq : q ≠ 0)
    {j n : ℕ} (hj : j ≤ n) (c B D : ℂ) :
    q ^ n * ((-c) ^ (n - j) * B * ((q ^ j)⁻¹ * D)) =
      B * D * (-q * c) ^ (n - j) := by
  rw [show q ^ n = q ^ (n - j) * q ^ j by rw [← pow_add, Nat.sub_add_cancel hj],
    show -q * c = (-c) * q by ring, mul_pow]
  field_simp

theorem correctionMoment_generating_deriv (n : ℕ) (z : ℂ) :
    (2 * Real.pi * I : ℂ) ^ n * correctionMoment n z =
      iteratedDeriv n (correctionGenerating z) 0 := by
  have he : correctionGenerating z = fun h : ℂ => correctionFactor z *
      (siegelIntegral ((z + 1 / 2) + h) * exp ((-Real.pi * I * (z + 1)) * h)) :=
    funext (correctionGenerating_normalization z)
  have hs : AnalyticAt ℂ (fun h : ℂ => siegelIntegral ((z + 1 / 2) + h)) 0 :=
    (siegelIntegral_analytic _).comp (by fun_prop)
  have hg : AnalyticAt ℂ (fun h : ℂ => exp ((-Real.pi * I * (z + 1)) * h)) 0 :=
    (by fun_prop : AnalyticAt ℂ (fun h : ℂ => (-Real.pi * I * (z + 1)) * h) 0).cexp
  rw [he, iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_mul hs.contDiffAt hg.contDiffAt]
  simp_rw [iteratedDeriv_comp_const_add, iteratedDeriv_cexp_const_mul]
  simp only [add_zero, mul_zero, exp_zero, mul_one]
  unfold correctionMoment
  rw [correctionIntegral_centered_moment,
    show (2 * Real.pi * I : ℂ) ^ n * (correctionFactor z *
      ∑ j ∈ Finset.range (n + 1), (-((z + 1) / 2)) ^ (n - j) * (n.choose j : ℂ) *
        (((2 * Real.pi * I : ℂ) ^ j)⁻¹ * iteratedDeriv j siegelIntegral (z + 1 / 2))) =
      correctionFactor z * ((2 * Real.pi * I : ℂ) ^ n *
        ∑ j ∈ Finset.range (n + 1), (-((z + 1) / 2)) ^ (n - j) * (n.choose j : ℂ) *
          (((2 * Real.pi * I : ℂ) ^ j)⁻¹ * iteratedDeriv j siegelIntegral (z + 1 / 2))) by ring,
    Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [weighted_power_cancel mordellFrequency_ne_zero (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
  congr 2
  ring

end LiuWang.Proof.Campaign20260915.ZetaMordell
