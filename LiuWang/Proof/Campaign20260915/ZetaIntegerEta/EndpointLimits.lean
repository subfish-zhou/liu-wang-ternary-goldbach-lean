import LiuWang.Proof.Campaign20260915.ZetaMordell.SourceMainTerm
import Mathlib.Topology.Algebra.Order.Floor

set_option autoImplicit false
noncomputable section
open Complex Filter Set
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaIntegerEta
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

theorem floor_eventually_left (n : ℕ) :
    ∀ᶠ eta : ℝ in 𝓝[<] ((n : ℝ) + 1), ⌊eta⌋₊ = n := by
  filter_upwards [Ico_mem_nhdsLT (show (n : ℝ) < n + 1 by linarith)] with eta he
  exact Nat.floor_eq_on_Ico n eta he

theorem floor_eventually_right (n : ℕ) :
    ∀ᶠ eta : ℝ in 𝓝[≥] (n : ℝ), ⌊eta⌋₊ = n := by
  filter_upwards [Ico_mem_nhdsGE (show (n : ℝ) < n + 1 by linarith)] with eta he
  exact Nat.floor_eq_on_Ico n eta he

theorem sourcePhiParameter_tendsto_left (n : ℕ) :
    Tendsto (fun eta : ℝ => sourcePhiParameter eta ⌊eta⌋₊)
      (𝓝[<] ((n : ℝ) + 1)) (𝓝 1) := by
  have h : Tendsto (fun eta : ℝ => sourcePhiParameter eta n)
      (𝓝[<] ((n : ℝ) + 1)) (𝓝 1) := by
    have hc : ContinuousAt (fun eta : ℝ => sourcePhiParameter eta n) ((n : ℝ) + 1) := by
      unfold sourcePhiParameter
      fun_prop
    convert hc.tendsto.mono_left nhdsWithin_le_nhds using 1
    norm_num [sourcePhiParameter]
  apply h.congr'
  filter_upwards [floor_eventually_left n] with eta he
  rw [he]

theorem sourcePhiParameter_tendsto_right (n : ℕ) :
    Tendsto (fun eta : ℝ => sourcePhiParameter eta ⌊eta⌋₊)
      (𝓝[≥] (n : ℝ)) (𝓝 (-1)) := by
  have h : Tendsto (fun eta : ℝ => sourcePhiParameter eta n)
      (𝓝[≥] (n : ℝ)) (𝓝 (-1)) := by
    have hc : ContinuousAt (fun eta : ℝ => sourcePhiParameter eta n) (n : ℝ) := by
      unfold sourcePhiParameter
      fun_prop
    simpa [sourcePhiParameter] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply h.congr'
  filter_upwards [floor_eventually_right n] with eta he
  rw [he]

theorem rsPhi_endpoint_one : rsPhi 1 = Real.cos (Real.pi / 8) := by
  have h := rsPhi_cos_identity (z := 1) (by norm_num)
  have hc : Real.cos (Real.pi * (4 * (1 : ℝ) ^ 2 + 3) / 8) =
      -Real.cos (Real.pi / 8) := by
    rw [show Real.pi * (4 * (1 : ℝ) ^ 2 + 3) / 8 =
      Real.pi - Real.pi / 8 by ring, Real.cos_pi_sub]
  rw [hc] at h
  simpa using h

theorem rsPhi_endpoint_neg_one : rsPhi (-1) = Real.cos (Real.pi / 8) := by
  rw [rsPhi_even, rsPhi_endpoint_one]

theorem phi_deriv_tendsto_left (n k : ℕ) :
    Tendsto (fun eta : ℝ => iteratedDeriv k rsPhi (sourcePhiParameter eta ⌊eta⌋₊))
      (𝓝[<] ((n : ℝ) + 1)) (𝓝 (iteratedDeriv k rsPhi 1)) := by
  have hc := (rsPhi_iterated_deriv_analytic (z := 1) (by norm_num) k).continuousAt
  simpa only [iteratedDeriv_eq_iterate, Function.comp_def] using
    hc.tendsto.comp (sourcePhiParameter_tendsto_left n)

theorem phi_deriv_tendsto_right (n k : ℕ) :
    Tendsto (fun eta : ℝ => iteratedDeriv k rsPhi (sourcePhiParameter eta ⌊eta⌋₊))
      (𝓝[≥] (n : ℝ)) (𝓝 ((-1 : ℝ) ^ k * iteratedDeriv k rsPhi 1)) := by
  have hc := (rsPhi_iterated_deriv_analytic (z := -1) (by norm_num) k).continuousAt
  have h := hc.tendsto.comp (sourcePhiParameter_tendsto_right n)
  simpa only [← iteratedDeriv_eq_iterate, rsPhi_deriv_parity, Function.comp_def] using h

theorem phi_tendsto_left (n : ℕ) :
    Tendsto (fun eta : ℝ => rsPhi (sourcePhiParameter eta ⌊eta⌋₊))
      (𝓝[<] ((n : ℝ) + 1)) (𝓝 (Real.cos (Real.pi / 8))) := by
  simpa [rsPhi_endpoint_one] using phi_deriv_tendsto_left n 0

theorem phi_tendsto_right (n : ℕ) :
    Tendsto (fun eta : ℝ => rsPhi (sourcePhiParameter eta ⌊eta⌋₊))
      (𝓝[≥] (n : ℝ)) (𝓝 (Real.cos (Real.pi / 8))) := by
  simpa [rsPhi_endpoint_one] using phi_deriv_tendsto_right n 0

theorem phiOne_tendsto_left (n : ℕ) :
    Tendsto (fun eta : ℝ => rsPhiOne (sourcePhiParameter eta ⌊eta⌋₊))
      (𝓝[<] ((n : ℝ) + 1)) (𝓝 (rsPhiOne 1)) :=
  (rsPhiOne_analytic (z := 1) (by norm_num)).continuousAt.tendsto.comp
    (sourcePhiParameter_tendsto_left n)

theorem phiOne_tendsto_right (n : ℕ) :
    Tendsto (fun eta : ℝ => rsPhiOne (sourcePhiParameter eta ⌊eta⌋₊))
      (𝓝[≥] (n : ℝ)) (𝓝 (-rsPhiOne 1)) := by
  simpa only [rsPhiOne_odd, Function.comp_def] using
    (rsPhiOne_analytic (z := -1) (by norm_num)).continuousAt.tendsto.comp
      (sourcePhiParameter_tendsto_right n)

theorem phiTwo_tendsto_left (n : ℕ) :
    Tendsto (fun eta : ℝ => rsPhiTwo (sourcePhiParameter eta ⌊eta⌋₊))
      (𝓝[<] ((n : ℝ) + 1)) (𝓝 (rsPhiTwo 1)) :=
  (rsPhiTwo_analytic (z := 1) (by norm_num)).continuousAt.tendsto.comp
    (sourcePhiParameter_tendsto_left n)

theorem phiTwo_tendsto_right (n : ℕ) :
    Tendsto (fun eta : ℝ => rsPhiTwo (sourcePhiParameter eta ⌊eta⌋₊))
      (𝓝[≥] (n : ℝ)) (𝓝 (rsPhiTwo 1)) := by
  simpa only [rsPhiTwo_even, Function.comp_def] using
    (rsPhiTwo_analytic (z := -1) (by norm_num)).continuousAt.tendsto.comp
      (sourcePhiParameter_tendsto_right n)

theorem correctionMoment_continuous (k : ℕ) : Continuous (correctionMoment k) := by
  have he : correctionMoment k = fun z : ℂ =>
      correctionFactor z * ∑ j ∈ Finset.range (k + 1),
        ((-((z + 1) / 2)) ^ (k - j) * (k.choose j : ℂ)) *
          (((2 * Real.pi * I : ℂ) ^ j)⁻¹ * iteratedDeriv j siegelIntegral (z + 1 / 2)) :=
    funext (correctionIntegral_centered_moment k)
  rw [he]
  apply Continuous.mul (by unfold correctionFactor; fun_prop)
  apply continuous_finsetSum
  intro j _
  have hc : Continuous (iteratedDeriv j siegelIntegral) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    simpa only [iteratedDeriv_eq_iterate] using ((siegelIntegral_analytic z).iterated_deriv j).continuousAt
  exact (by fun_prop : Continuous (fun z : ℂ =>
    (-((z + 1) / 2)) ^ (k - j) * (k.choose j : ℂ))).mul
      ((hc.comp (by fun_prop)).const_mul _)

theorem correctionMoment_tendsto_left (n k : ℕ) :
    Tendsto (fun eta : ℝ => correctionMoment k (sourcePhiParameter eta ⌊eta⌋₊))
      (𝓝[<] ((n : ℝ) + 1)) (𝓝 (correctionMoment k 1)) := by
  exact (correctionMoment_continuous k).continuousAt.tendsto.comp
    (Complex.continuous_ofReal.continuousAt.tendsto.comp (sourcePhiParameter_tendsto_left n))

theorem correctionMoment_tendsto_right (n k : ℕ) :
    Tendsto (fun eta : ℝ => correctionMoment k (sourcePhiParameter eta ⌊eta⌋₊))
      (𝓝[≥] (n : ℝ)) (𝓝 (correctionMoment k (-1))) := by
  have h := ((correctionMoment_continuous k).comp Complex.continuous_ofReal).continuousAt
    (x := (-1 : ℝ))
  simpa only [Function.comp_def, ofReal_neg, ofReal_one] using
    h.tendsto.comp (sourcePhiParameter_tendsto_right n)

theorem signed_phi_correction_jump (n : ℕ) (a b c : ℝ) :
    (-1 : ℝ) ^ (n + 1) * (a * rsPhi (-1) + b * rsPhiOne (-1) + c * rsPhiTwo (-1)) -
      (-1 : ℝ) ^ n * (a * rsPhi 1 + b * rsPhiOne 1 + c * rsPhiTwo 1) =
        -2 * (-1 : ℝ) ^ n * (a * Real.cos (Real.pi / 8) + c * rsPhiTwo 1) := by
  rw [rsPhi_even, rsPhiOne_odd, rsPhiTwo_even, rsPhi_endpoint_one, pow_succ]
  ring

end LiuWang.Proof.Campaign20260915.ZetaIntegerEta
