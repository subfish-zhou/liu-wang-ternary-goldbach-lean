import LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1.EulerTransport
import LiuWang.Proof.ZeroRegionFamily.Sharp.ZeroSumBudget
import LiuWang.Proof.DirichletZeroCount.Transport

/-! The full signed zero sum in LWD (2.4), (2.7), (2.8), with ordinary-L multiplicities. -/

set_option autoImplicit false
noncomputable section

open Complex Complex.Hadamard
open scoped Classical
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1

def NontrivialZeroIndex {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) :=
  Σ rho : {z : ℂ // z.re ∈ Set.Ioo (0 : ℝ) 1}, Fin (analyticOrderNatAt chi.LFunction rho)

def zeroSum {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (sigma t : ℝ) : ℝ :=
  ∑' p : NontrivialZeroIndex chi, dampedZeroKernel sigma t p.1

def primitiveIndexEquiv {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    [NeZero chi.conductor] (hc : chi ≠ 1) :
    NontrivialZeroIndex chi ≃ NontrivialZeroIndex chi.primitiveCharacter :=
  Equiv.sigmaCongrRight (fun rho =>
    finCongr (analyticOrderNatAt_LFunction_eq_primitive chi hc rho.2.1))

theorem zeroSum_eq_primitive {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    [NeZero chi.conductor] (hc : chi ≠ 1) (sigma t : ℝ) :
    zeroSum chi sigma t = zeroSum chi.primitiveCharacter sigma t :=
  (primitiveIndexEquiv chi hc).tsum_eq (fun p => dampedZeroKernel sigma t p.1)

theorem completed_multiplicity {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) {rho : ℂ} (hr : 0 < rho.re) :
    (MeromorphicOn.divisor (symmetricCompletedLFunction chi) Set.univ rho).toNat =
      analyticOrderNatAt chi.LFunction rho := by
  rw [divisor_univ_eq_analyticOrderNatAt_int (differentiable_symmetricCompletedLFunction hc)]
  simpa using analyticOrderNatAt_symmetricCompletedLFunction_eq_LFunction hc hr

def completedIndexEquiv {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) (hp : chi.IsPrimitive) :
    SymmetricCompletedZeroIndex chi ≃ NontrivialZeroIndex chi where
  toFun p :=
    ⟨⟨divisorZeroIndex₀_val p,
      symmetricCompletedLFunction_divisorZeroIndex₀_re_mem_Ioo hc hp p⟩,
      Fin.cast (completed_multiplicity hc
        (symmetricCompletedLFunction_divisorZeroIndex₀_re_mem_Ioo hc hp p).1) p.1.2⟩
  invFun p :=
    ⟨⟨p.1, Fin.cast (completed_multiplicity hc p.1.2.1).symm p.2⟩,
      by
        intro hz
        have hh : (p.1 : ℂ).re = 0 := congrArg Complex.re hz
        linarith [p.1.2.1]⟩
  left_inv p := by
    apply Subtype.ext
    apply Sigma.ext rfl
    exact (Fin.heq_ext_iff rfl).mpr rfl
  right_inv p := by
    apply Sigma.ext rfl
    exact (Fin.heq_ext_iff rfl).mpr rfl

theorem zeroSum_eq_completed {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) (hp : chi.IsPrimitive) (sigma t : ℝ) :
    zeroSum chi sigma t = primitiveZeroSum chi sigma t :=
  ((completedIndexEquiv hc hp).tsum_eq
    (fun p => dampedZeroKernel sigma t p.1)).symm

theorem zeroSum_summable {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    Summable (fun p : NontrivialZeroIndex chi => dampedZeroKernel sigma t p.1) := by
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hpr := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hc
  have hh : Summable (fun p : NontrivialZeroIndex chi.primitiveCharacter =>
      dampedZeroKernel sigma t p.1) := by
    apply (completedIndexEquiv hpr chi.primitiveCharacter_isPrimitive).summable_iff.mp
    exact summable_dampedZeroKernel hpr chi.primitiveCharacter_isPrimitive hs t
  exact (primitiveIndexEquiv chi hc).summable_iff.mpr hh

def parityShift {q : ℕ} (chi : DirichletCharacter ℂ q) : ℝ :=
  (1 - (chi (-1)).re) / 2

def gammaTerm (delta sigma t : ℝ) : ℝ :=
  ((digamma (((sigma : ℂ) + I * t + delta) / 2)).re -
    stechkinK * (digamma (((stechkinSigma sigma : ℂ) + I * t + delta) / 2)).re) / 2

theorem gammaDifference_eq {q : ℕ} (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    gammaDifferenceAt chi sigma t =
      -kappa * Real.log Real.pi + gammaTerm (parityShift chi) sigma t := by
  have he (u delta : ℝ) :
      ((u : ℂ) + I * t + delta) / 2 =
        (((u + delta) / 2 : ℝ) : ℂ) + I * (t / 2 : ℝ) := by push_cast; ring
  rw [kappa_eq]
  rcases chi.even_or_odd with hc | hc
  · have hd : parityShift chi = 0 := by
      unfold parityShift
      rw [show chi (-1) = 1 from hc]
      norm_num
    rw [gammaDifference_even hc hs, hd]
    simp only [gammaTerm, he, add_zero]
  · have hd : parityShift chi = 1 := by
      unfold parityShift
      rw [show chi (-1) = -1 from hc]
      norm_num
    rw [gammaDifference_odd hc hs, hd]
    simp only [gammaTerm, he]

theorem l25_primitive_identity {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) (hp : chi.IsPrimitive) {sigma : ℝ}
    (hs : 1 < sigma) (t : ℝ) :
    f chi sigma t = kappa * Real.log ((q : ℝ) / Real.pi) +
      gammaTerm (parityShift chi) sigma t - zeroSum chi sigma t := by
  have hi := damped_kernel_identity hc hp hs (hs.trans_le (stechkinSigma_ge hs)) stechkinK t
  have hg := gammaDifference_eq chi hs t
  rw [f_eq_damped, zeroSum_eq_completed hc hp,
    Real.log_div (Nat.cast_ne_zero.mpr (NeZero.ne q)) Real.pi_ne_zero]
  dsimp [primitiveZeroSum, dampedZeroKernel, gammaDifferenceAt] at *
  rw [kappa_eq] at *
  dsimp [stechkinConductorCoeff] at *
  linarith

theorem l25_primitive_of_gamma_estimate {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    {sigma : ℝ} (hs : sigma ∈ Set.Ioo (1 : ℝ) 1.15) (t : ℝ)
    (hgamma : gammaTerm (parityShift chi) sigma t ≤
      kappa * Real.log (max 1 |t|) + 0.3918) :
    f chi sigma t ≤ kappa * Real.log ((q : ℝ) * max 1 |t|) -
      kappa * Real.log Real.pi + 0.3918 - zeroSum chi sigma t := by
  rw [l25_primitive_identity hc hp hs.1,
    Real.log_div (Nat.cast_ne_zero.mpr (NeZero.ne q)) Real.pi_ne_zero,
    Real.log_mul (Nat.cast_ne_zero.mpr (NeZero.ne q))
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))]
  linarith

theorem l25_imprimitive_of_gamma_estimate {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor] (hc : chi ≠ 1)
    {sigma : ℝ} (hs : sigma ∈ Set.Ioo (1 : ℝ) 1.15) (t : ℝ)
    (hgamma : gammaTerm (parityShift chi.primitiveCharacter) sigma t ≤
      kappa * Real.log (max 1 |t|) + 0.3918) :
    f chi sigma t ≤ kappa * Real.log ((chi.conductor : ℝ) * max 1 |t|) -
      kappa * Real.log Real.pi + 0.3918 - zeroSum chi sigma t +
        badS chi.conductor q sigma := by
  have hpr := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hc
  have hp := l25_primitive_of_gamma_estimate hpr chi.primitiveCharacter_isPrimitive hs t hgamma
  have he := (le_abs_self (f chi sigma t - f chi.primitiveCharacter sigma t)).trans
    (abs_f_sub_primitive_le chi hc hs.1 t)
  rw [zeroSum_eq_primitive chi hc]
  linarith

end LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1
