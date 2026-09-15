import LiuWang.Proof.Campaign20260915.ZetaMordell.MomentGenerating

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory
open scoped Real

namespace LiuWang.Proof.Campaign20260915.ZetaMordell

open LiuWang.Proof.Campaign20260915.ZetaValidation

def gaussianJet (c : ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n (fun h : ℂ => exp (c * h ^ 2)) 0

theorem gaussianJet_zero (c : ℂ) : gaussianJet c 0 = 1 := by
  simp [gaussianJet]

theorem gaussianJet_succ (c : ℂ) (n : ℕ) :
    gaussianJet c (n + 1) = 2 * c *
      ∑ j ∈ Finset.range (n + 1),
        (n.choose j : ℂ) * (if j = 1 then 1 else 0) * gaussianJet c (n - j) := by
  have hd : deriv (fun h : ℂ => exp (c * h ^ 2)) =
      fun h : ℂ => (2 * c) * (h * exp (c * h ^ 2)) := by
    funext h
    have hder := (((hasDerivAt_id h).pow 2).const_mul c).cexp
    simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] at hder
    rw [hder.deriv]
    ring
  have hg : AnalyticAt ℂ (fun h : ℂ => exp (c * h ^ 2)) 0 :=
    (by fun_prop : AnalyticAt ℂ (fun h : ℂ => c * h ^ 2) 0).cexp
  rw [gaussianJet, iteratedDeriv_succ', hd, iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_mul (by fun_prop) hg.contDiffAt]
  simp only [iteratedDeriv_fun_id_zero, gaussianJet]

theorem gaussianJet_one (c : ℂ) : gaussianJet c 1 = 0 := by
  rw [show 1 = 0 + 1 by rfl, gaussianJet_succ]
  norm_num [Finset.sum_range_succ]

theorem gaussianJet_rec (c : ℂ) (n : ℕ) :
    gaussianJet c (n + 2) = 2 * c * (n + 1) * gaussianJet c n := by
  rw [show n + 2 = (n + 1) + 1 by omega, gaussianJet_succ]
  simp [mul_ite, ite_mul, Finset.sum_ite_eq', Nat.choose_one_right]
  ring

theorem gaussianJet_two (c : ℂ) : gaussianJet c 2 = 2 * c := by
  simpa [gaussianJet_zero] using gaussianJet_rec c 0

theorem gaussianJet_three (c : ℂ) : gaussianJet c 3 = 0 := by
  simpa [gaussianJet_one] using gaussianJet_rec c 1

theorem gaussianJet_four (c : ℂ) : gaussianJet c 4 = 12 * c ^ 2 := by
  rw [show 4 = 2 + 2 by rfl, gaussianJet_rec, gaussianJet_two]
  norm_num
  ring

theorem gaussianJet_five (c : ℂ) : gaussianJet c 5 = 0 := by
  simpa [gaussianJet_three] using gaussianJet_rec c 3

theorem gaussianJet_six (c : ℂ) : gaussianJet c 6 = 120 * c ^ 3 := by
  rw [show 6 = 4 + 2 by rfl, gaussianJet_rec, gaussianJet_four]
  norm_num
  ring

theorem gaussianJet_even (c : ℂ) (n : ℕ) :
    gaussianJet c (2 * n) = ((2 * n).factorial : ℂ) / (n.factorial : ℂ) * c ^ n := by
  induction n with
  | zero => norm_num [gaussianJet_zero]
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 2 by omega, gaussianJet_rec, ih]
    have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have hn1 : (n : ℂ) + 1 ≠ 0 := by
      exact_mod_cast (Nat.succ_ne_zero n)
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat, pow_succ]
    field_simp
    ring

theorem gaussianJet_odd (c : ℂ) (n : ℕ) : gaussianJet c (2 * n + 1) = 0 := by
  induction n with
  | zero => simpa using gaussianJet_one c
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, gaussianJet_rec, ih, mul_zero]

theorem correctionMoment_phi_derivatives (n : ℕ) {z : ℝ} (hz : |z| < 3 / 2) :
    (2 * Real.pi * I : ℂ) ^ n * correctionMoment n z =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℂ) *
        ((iteratedDeriv j rsPhi z : ℝ) : ℂ) * gaussianJet (Real.pi * I / 2) (n - j) := by
  rw [correctionMoment_generating_deriv]
  have hc : AnalyticAt ℂ (fun h : ℂ => correctionIntegral ((z : ℂ) + h)) 0 :=
    (correctionIntegral_analytic _).comp (by fun_prop)
  have hg : AnalyticAt ℂ (fun h : ℂ => exp ((Real.pi * I / 2) * h ^ 2)) 0 :=
    (by fun_prop : AnalyticAt ℂ (fun h : ℂ => (Real.pi * I / 2) * h ^ 2) 0).cexp
  have he : correctionGenerating (z : ℂ) = fun h : ℂ =>
      correctionIntegral ((z : ℂ) + h) * exp ((Real.pi * I / 2) * h ^ 2) := by
    funext h
    unfold correctionGenerating
    congr 2
    ring
  rw [he, iteratedDeriv_fun_mul hc.contDiffAt hg.contDiffAt]
  simp_rw [iteratedDeriv_comp_const_add]
  simp only [add_zero, gaussianJet]
  apply Finset.sum_congr rfl
  intro j _
  rw [correctionIntegral_iteratedDeriv_eq_rsPhi j hz]

def correctionDerivPolynomial (n : ℕ) (w : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1),
    ((n.choose j : ℂ) * (2 * Real.pi * I) ^ j *
      gaussianJet (-Real.pi * I / 2) (n - j)) * w ^ j

theorem correctionGenerating_inverse (z h : ℂ) :
    correctionIntegral (z + h) =
      correctionGenerating z h * exp ((-Real.pi * I / 2) * h ^ 2) := by
  unfold correctionGenerating
  rw [mul_assoc, ← exp_add,
    show Real.pi * I * h ^ 2 / 2 + (-Real.pi * I / 2) * h ^ 2 = 0 by ring,
    exp_zero, mul_one]

theorem correctionIntegral_deriv_moment_sum (n : ℕ) (z : ℂ) :
    iteratedDeriv n correctionIntegral z =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℂ) *
        ((2 * Real.pi * I : ℂ) ^ j * correctionMoment j z) *
          gaussianJet (-Real.pi * I / 2) (n - j) := by
  have he : (fun h : ℂ => correctionIntegral (z + h)) =
      fun h : ℂ => correctionGenerating z h * exp ((-Real.pi * I / 2) * h ^ 2) :=
    funext (correctionGenerating_inverse z)
  have h := congrArg (fun f : ℂ → ℂ => iteratedDeriv n f 0) he
  have hg : AnalyticAt ℂ (fun h : ℂ => exp ((-Real.pi * I / 2) * h ^ 2)) 0 :=
    (by fun_prop : AnalyticAt ℂ (fun h : ℂ => (-Real.pi * I / 2) * h ^ 2) 0).cexp
  rw [iteratedDeriv_comp_const_add,
    iteratedDeriv_fun_mul (correctionGenerating_analytic z 0).contDiffAt hg.contDiffAt] at h
  simpa only [add_zero, ← correctionMoment_generating_deriv, gaussianJet] using h

theorem correctionDerivPolynomial_kernel (n : ℕ) (z : ℂ) (t : ℝ) :
    correctionDerivPolynomial n (siegelLine t - (z + 1) / 2) * correctionKernel z t =
      ∑ j ∈ Finset.range (n + 1),
        ((n.choose j : ℂ) * (2 * Real.pi * I) ^ j *
          gaussianJet (-Real.pi * I / 2) (n - j)) *
            ((siegelLine t - (z + 1) / 2) ^ j * correctionKernel z t) := by
  simp only [correctionDerivPolynomial, Finset.sum_mul, mul_assoc]

theorem correctionDerivPolynomial_integrable (n : ℕ) (z : ℂ) :
    Integrable (fun t : ℝ =>
      correctionDerivPolynomial n (siegelLine t - (z + 1) / 2) * correctionKernel z t) := by
  simp_rw [correctionDerivPolynomial_kernel]
  exact integrable_finsetSum _ (fun j _ => (correctionCenteredKernel_integrable j z).const_mul _)

theorem correctionDerivPolynomial_integral (n : ℕ) (z : ℂ) :
    (∫ t : ℝ, correctionDerivPolynomial n (siegelLine t - (z + 1) / 2) * correctionKernel z t) =
      iteratedDeriv n correctionIntegral z := by
  simp_rw [correctionDerivPolynomial_kernel]
  rw [integral_finsetSum _ (fun j _ => (correctionCenteredKernel_integrable j z).const_mul _),
    correctionIntegral_deriv_moment_sum]
  simp_rw [integral_const_mul]
  apply Finset.sum_congr rfl
  intro j _
  unfold correctionMoment
  ring

theorem correctionDerivPolynomial_zero (w : ℂ) : correctionDerivPolynomial 0 w = 1 := by
  norm_num [correctionDerivPolynomial, gaussianJet_zero, Finset.sum_range_succ]

theorem correctionDerivPolynomial_two (w : ℂ) :
    correctionDerivPolynomial 2 w = (2 * Real.pi * I) ^ 2 * w ^ 2 - Real.pi * I := by
  norm_num [correctionDerivPolynomial, Finset.sum_range_succ,
    gaussianJet_zero, gaussianJet_one, gaussianJet_two]
  ring

theorem correctionDerivPolynomial_three (w : ℂ) :
    correctionDerivPolynomial 3 w =
      (2 * Real.pi * I) ^ 3 * w ^ 3 - 3 * Real.pi * I * (2 * Real.pi * I) * w := by
  norm_num [correctionDerivPolynomial, Finset.sum_range_succ,
    gaussianJet_zero, gaussianJet_one, gaussianJet_two, gaussianJet_three]
  ring

theorem correctionDerivPolynomial_six (w : ℂ) :
    correctionDerivPolynomial 6 w =
      (2 * Real.pi * I) ^ 6 * w ^ 6 -
        15 * Real.pi * I * (2 * Real.pi * I) ^ 4 * w ^ 4 +
        45 * (Real.pi * I) ^ 2 * (2 * Real.pi * I) ^ 2 * w ^ 2 -
        15 * (Real.pi * I) ^ 3 := by
  norm_num [correctionDerivPolynomial, Finset.sum_range_succ,
    gaussianJet_zero, gaussianJet_one, gaussianJet_two, gaussianJet_three,
    gaussianJet_four, gaussianJet_five, gaussianJet_six, Nat.choose]
  ring

theorem correctionPolynomial_integral_phiOne {z : ℝ} (hz : |z| < 3 / 2) :
    (∫ t : ℝ, (correctionDerivPolynomial 3 (siegelLine t - ((z : ℂ) + 1) / 2) /
      (12 * Real.pi ^ 2)) * correctionKernel z t) = (rsPhiOne z : ℂ) := by
  simp_rw [show ∀ t : ℝ,
    correctionDerivPolynomial 3 (siegelLine t - ((z : ℂ) + 1) / 2) / (12 * Real.pi ^ 2) *
      correctionKernel z t =
    (correctionDerivPolynomial 3 (siegelLine t - ((z : ℂ) + 1) / 2) *
      correctionKernel z t) / (12 * Real.pi ^ 2) from fun t => by ring]
  rw [integral_div, correctionDerivPolynomial_integral]
  exact correctionIntegral_third_deriv_phiOne hz

theorem correctionPolynomial_integral_phiTwo {z : ℝ} (hz : |z| < 3 / 2) :
    (∫ t : ℝ,
      (correctionDerivPolynomial 2 (siegelLine t - ((z : ℂ) + 1) / 2) / (16 * Real.pi ^ 2) +
        correctionDerivPolynomial 6 (siegelLine t - ((z : ℂ) + 1) / 2) / (288 * Real.pi ^ 4)) *
          correctionKernel z t) = (rsPhiTwo z : ℂ) := by
  simp_rw [add_mul, div_mul_eq_mul_div]
  rw [integral_add ((correctionDerivPolynomial_integrable 2 z).div_const _)
    ((correctionDerivPolynomial_integrable 6 z).div_const _),
    integral_div, integral_div, correctionDerivPolynomial_integral, correctionDerivPolynomial_integral]
  exact correctionIntegral_derivs_phiTwo hz

theorem correctionPhiOne_polynomial (w : ℂ) :
    correctionDerivPolynomial 3 w / (12 * Real.pi ^ 2) =
      w / 2 - (2 / 3 : ℂ) * Real.pi * I * w ^ 3 := by
  rw [correctionDerivPolynomial_three]
  have hp : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring_nf
  simp only [I_sq, I_pow_three]
  ring

theorem correctionPhiTwo_polynomial (w : ℂ) :
    correctionDerivPolynomial 2 w / (16 * Real.pi ^ 2) +
      correctionDerivPolynomial 6 w / (288 * Real.pi ^ 4) =
      -(2 / 9 : ℂ) * Real.pi ^ 2 * w ^ 6 - (5 / 6 : ℂ) * Real.pi * I * w ^ 4 +
        (3 / 8 : ℂ) * w ^ 2 - I / (96 * Real.pi) := by
  rw [correctionDerivPolynomial_two, correctionDerivPolynomial_six]
  have hp : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring_nf
  norm_num [pow_succ]
  rw [I_pow_eq_pow_mod 5, I_pow_eq_pow_mod 6]
  norm_num
  ring

theorem correctionIntegral_phiOne {z : ℝ} (hz : |z| < 3 / 2) :
    (∫ t : ℝ, ((siegelLine t - ((z : ℂ) + 1) / 2) / 2 -
      (2 / 3 : ℂ) * Real.pi * I * (siegelLine t - ((z : ℂ) + 1) / 2) ^ 3) *
        correctionKernel z t) = (rsPhiOne z : ℂ) := by
  simpa only [correctionPhiOne_polynomial] using correctionPolynomial_integral_phiOne hz

theorem correctionIntegral_phiTwo {z : ℝ} (hz : |z| < 3 / 2) :
    (∫ t : ℝ,
      (-(2 / 9 : ℂ) * Real.pi ^ 2 * (siegelLine t - ((z : ℂ) + 1) / 2) ^ 6 -
        (5 / 6 : ℂ) * Real.pi * I * (siegelLine t - ((z : ℂ) + 1) / 2) ^ 4 +
        (3 / 8 : ℂ) * (siegelLine t - ((z : ℂ) + 1) / 2) ^ 2 - I / (96 * Real.pi)) *
          correctionKernel z t) = (rsPhiTwo z : ℂ) := by
  simpa only [correctionPhiTwo_polynomial] using correctionPolynomial_integral_phiTwo hz

theorem correctionPhiOne_integrable (z : ℂ) :
    Integrable (fun t : ℝ =>
      ((siegelLine t - (z + 1) / 2) / 2 -
        (2 / 3 : ℂ) * Real.pi * I * (siegelLine t - (z + 1) / 2) ^ 3) *
          correctionKernel z t) := by
  have h := (correctionDerivPolynomial_integrable 3 z).div_const (12 * Real.pi ^ 2 : ℂ)
  simpa only [← div_mul_eq_mul_div, correctionPhiOne_polynomial] using h

theorem correctionPhiTwo_integrable (z : ℂ) :
    Integrable (fun t : ℝ =>
      (-(2 / 9 : ℂ) * Real.pi ^ 2 * (siegelLine t - (z + 1) / 2) ^ 6 -
        (5 / 6 : ℂ) * Real.pi * I * (siegelLine t - (z + 1) / 2) ^ 4 +
        (3 / 8 : ℂ) * (siegelLine t - (z + 1) / 2) ^ 2 - I / (96 * Real.pi)) *
          correctionKernel z t) := by
  have h := ((correctionDerivPolynomial_integrable 2 z).div_const (16 * Real.pi ^ 2 : ℂ)).add
    ((correctionDerivPolynomial_integrable 6 z).div_const (288 * Real.pi ^ 4 : ℂ))
  change Integrable (fun t : ℝ =>
    (correctionDerivPolynomial 2 (siegelLine t - (z + 1) / 2) * correctionKernel z t) /
        (16 * Real.pi ^ 2) +
      (correctionDerivPolynomial 6 (siegelLine t - (z + 1) / 2) * correctionKernel z t) /
        (288 * Real.pi ^ 4)) at h
  simpa only [← div_mul_eq_mul_div, ← add_mul, correctionPhiTwo_polynomial] using h

end LiuWang.Proof.Campaign20260915.ZetaMordell
