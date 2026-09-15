import LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.Recovery
import Mathlib.Analysis.MeanInequalities

/-! Finite-family Holder with the original 1/phi normalization, including both endpoints. -/

set_option autoImplicit false
noncomputable section

open Finset MeasureTheory Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.NonprincipalDensityAdvance

namespace LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis

theorem normalized_geometric_sum {ι : Type*} (S : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) (hb : ∀ i ∈ S, 0 ≤ b i)
    {D theta : ℝ} (hD : 0 < D) (ht : theta ∈ Set.Icc 0 1) :
    (∑ i ∈ S, (a i) ^ (1 - theta) * (b i) ^ theta) / D ≤
      ((∑ i ∈ S, a i) / D) ^ (1 - theta) * ((∑ i ∈ S, b i) / D) ^ theta := by
  have hsum : (∑ i ∈ S, (a i) ^ (1 - theta) * (b i) ^ theta) ≤
      (∑ i ∈ S, a i) ^ (1 - theta) * (∑ i ∈ S, b i) ^ theta := by
    by_cases h0 : theta = 0
    · simp [h0]
    by_cases h1 : theta = 1
    · simp [h1]
    have ht0 : 0 < theta := lt_of_le_of_ne ht.1 (Ne.symm h0)
    have ht1 : theta < 1 := lt_of_le_of_ne ht.2 h1
    have hp : ((1 - theta)⁻¹).HolderConjugate theta⁻¹ := by
      apply Real.holderConjugate_iff.mpr
      refine ⟨?_, by simp⟩
      rw [one_lt_inv₀ (by linarith : 0 < 1 - theta)]
      linarith
    have h := Real.inner_le_Lp_mul_Lq_of_nonneg S hp
      (f := fun i => (a i) ^ (1 - theta)) (g := fun i => (b i) ^ theta)
      (fun i hi => Real.rpow_nonneg (ha i hi) _)
      (fun i hi => Real.rpow_nonneg (hb i hi) _)
    have hleft : (∑ i ∈ S, ((a i) ^ (1 - theta)) ^ (1 - theta)⁻¹) = ∑ i ∈ S, a i := by
      apply sum_congr rfl
      intro i hi
      rw [← Real.rpow_mul (ha i hi), mul_inv_cancel₀ (by linarith : 1 - theta ≠ 0), Real.rpow_one]
    have hright : (∑ i ∈ S, ((b i) ^ theta) ^ theta⁻¹) = ∑ i ∈ S, b i := by
      apply sum_congr rfl
      intro i hi
      rw [← Real.rpow_mul (hb i hi), mul_inv_cancel₀ ht0.ne', Real.rpow_one]
    simpa only [hleft, hright, one_div, inv_inv] using h
  rw [Real.div_rpow (sum_nonneg ha) hD.le, Real.div_rpow (sum_nonneg hb) hD.le,
    div_mul_div_comm, ← Real.rpow_add hD, sub_add_cancel, Real.rpow_one]
  exact div_le_div_of_nonneg_right hsum hD.le

theorem cosine_endpoint_geometric_budget (q : ℕ) [NeZero q] {y theta : ℝ}
    (hy : 2 ≤ y) (ht : theta ∈ Set.Icc 0 1) {M : ℕ} (hM : 2 ≤ M) :
    (∑ chi ∈ nonprincipalCharacters q,
      (∫ t : ℝ, ‖cosineDetector chi ((q : ℝ) * y) y ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) ^ (1 - theta) *
      (∫ t : ℝ, ‖cosineDetector chi ((q : ℝ) * y) y ((1 : ℂ) + t * Complex.I)‖ ^ 2) ^ theta) / q.totient ≤
      (256 * criticalBudget q ((q : ℝ) * y) M y) ^ (1 - theta) *
        (4620288 * (1 + Real.log ((q : ℝ) * y)) ^ 5 / q) ^ theta := by
  have hphi : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  have h := normalized_geometric_sum (nonprincipalCharacters q)
    (fun chi => ∫ t : ℝ, ‖cosineDetector chi ((q : ℝ) * y) y ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2)
    (fun chi => ∫ t : ℝ, ‖cosineDetector chi ((q : ℝ) * y) y ((1 : ℂ) + t * Complex.I)‖ ^ 2)
    (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
    (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)) hphi ht
  have hL0 : 0 ≤ cosineMean q ((q : ℝ) * y) (1 / 2) y :=
    div_nonneg (sum_nonneg fun _ _ => integral_nonneg (fun _ => sq_nonneg _)) (Nat.cast_nonneg _)
  have hR0 : 0 ≤ cosineMean q ((q : ℝ) * y) 1 y :=
    div_nonneg (sum_nonneg fun _ _ => integral_nonneg (fun _ => sq_nonneg _)) (Nat.cast_nonneg _)
  have hL := Real.rpow_le_rpow (z := 1 - theta) hL0
    (cosine_critical_fixed_X q hy hM) (by linarith [ht.2])
  have hR := Real.rpow_le_rpow hR0 (cosine_right_fixed_X q hy) ht.1
  have hm := mul_le_mul hL hR (Real.rpow_nonneg hR0 _)
    (Real.rpow_nonneg (mul_nonneg (by norm_num) (criticalBudget_nonneg q _ M (by linarith))) _)
  apply h.trans
  simpa only [cosineMean, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using hm

end LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis
