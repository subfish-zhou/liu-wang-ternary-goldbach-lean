import LiuWang.Proof.SourceRoute.Density.Restart.ProductRight
import Mathlib.Analysis.Complex.JensenFormula

/-! The reflection of the whole product, not a product of individual reflections. -/

set_option autoImplicit false

noncomputable section

open Complex Set Metric
open scoped ComplexConjugate

namespace LiuWang.Proof.SourceRoute.Density.Restart

def productReflection (q : ℕ) [NeZero q] (X U : ℝ) (s : ℂ) : ℂ :=
  familyProduct q X (s + U * I) + familyProduct q X (s - U * I)

theorem productReflection_differentiable (q : ℕ) [NeZero q] (X U : ℝ) :
    Differentiable ℂ (productReflection q X U) :=
  ((familyProduct_differentiable q X).comp (differentiable_id.add_const _)).add
    ((familyProduct_differentiable q X).comp (differentiable_id.sub_const _))

theorem productReflection_real (q : ℕ) [NeZero q] (X U x : ℝ) :
    productReflection q X U x = (2 * (familyProduct q X ((x : ℂ) + U * I)).re : ℝ) := by
  have he : (x : ℂ) - U * I = conj ((x : ℂ) + U * I) := by simp [sub_eq_add_neg]
  rw [productReflection, he, familyProduct_conj]
  exact Complex.add_conj _

theorem productReflection_real_zero_iff (q : ℕ) [NeZero q] (X U x : ℝ) :
    productReflection q X U x = 0 ↔ (familyProduct q X ((x : ℂ) + U * I)).re = 0 := by
  rw [productReflection_real, ofReal_eq_zero]
  simp

theorem productReflection_source_center (q : ℕ) [NeZero q] {X : ℝ}
    (hX : 100000 ≤ X) (hqX : (q : ℝ) ≤ X) (U : ℝ) :
    199499 / 100000 ≤ (productReflection q X U 2).re := by
  have hr := familyProduct_right_re q hX hqX (s := (2 : ℂ) + U * I) (by simp)
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, productReflection_real]
  simp only [ofReal_re, ofReal_ofNat]
  linarith

theorem productReflection_center_ne_zero (q : ℕ) [NeZero q] {X : ℝ}
    (hX : 100000 ≤ X) (hqX : (q : ℝ) ≤ X) (U : ℝ) :
    productReflection q X U 2 ≠ 0 := by
  intro hz
  have h := productReflection_source_center q hX hqX U
  rw [hz, zero_re] at h
  norm_num at h

theorem productReflection_order_finite (q : ℕ) [NeZero q] {X : ℝ}
    (hX : 100000 ≤ X) (hqX : (q : ℝ) ≤ X) (U : ℝ) (s : ℂ) :
    analyticOrderAt (productReflection q X U) s ≠ ⊤ :=
  Complex.Hadamard.analyticOrderAt_ne_top_of_exists_ne_zero
    (productReflection_differentiable q X U) ⟨2, productReflection_center_ne_zero q hX hqX U⟩ s

def productReflectedZeros (q : ℕ) [NeZero q] (X U r : ℝ) : Finset ℂ :=
  ((MeromorphicOn.divisor (productReflection q X U) (closedBall (2 : ℂ) r)).finiteSupport
    (isCompact_closedBall (2 : ℂ) r)).toFinset

theorem productReflection_divisor_apply (q : ℕ) [NeZero q] {X U r : ℝ}
    (hX : 100000 ≤ X) (hqX : (q : ℝ) ≤ X) {s : ℂ} (hs : s ∈ closedBall (2 : ℂ) r) :
    MeromorphicOn.divisor (productReflection q X U) (closedBall (2 : ℂ) r) s =
      (analyticOrderNatAt (productReflection q X U) s : ℤ) := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply
    (fun z _ => (productReflection_differentiable q X U).analyticAt z) hs,
    ← Nat.cast_analyticOrderNatAt (productReflection_order_finite q hX hqX U s)]
  simp

theorem mem_productReflectedZeros (q : ℕ) [NeZero q] {X U r : ℝ}
    (hX : 100000 ≤ X) (hqX : (q : ℝ) ≤ X) {s : ℂ}
    (hs : s ∈ closedBall (2 : ℂ) r) (hz : productReflection q X U s = 0) :
    s ∈ productReflectedZeros q X U r := by
  have ho := ((productReflection_differentiable q X U).analyticAt s).analyticOrderAt_eq_zero
  rw [← Nat.cast_analyticOrderNatAt (productReflection_order_finite q hX hqX U s)] at ho
  simp only [Nat.cast_eq_zero] at ho
  have hn : analyticOrderNatAt (productReflection q X U) s ≠ 0 := fun h => (ho.mp h) hz
  apply ((MeromorphicOn.divisor (productReflection q X U) (closedBall (2 : ℂ) r)).finiteSupport
    (isCompact_closedBall (2 : ℂ) r)).mem_toFinset.mpr
  rw [Function.mem_support, productReflection_divisor_apply q hX hqX hs]
  exact_mod_cast hn

theorem product_reflected_card_le_divisor (q : ℕ) [NeZero q] {X : ℝ}
    (hX : 100000 ≤ X) (hqX : (q : ℝ) ≤ X) (U r : ℝ) :
    ((productReflectedZeros q X U r).card : ℝ) ≤
      ((∑ᶠ s, MeromorphicOn.divisor (productReflection q X U)
        (closedBall (2 : ℂ) r) s : ℤ) : ℝ) := by
  classical
  let D := MeromorphicOn.divisor (productReflection q X U) (closedBall (2 : ℂ) r)
  have hsum : (∑ᶠ s, D s) = ∑ s ∈ productReflectedZeros q X U r, D s :=
    finsum_eq_sum_of_support_subset _ (fun s hs =>
      (D.finiteSupport (isCompact_closedBall (2 : ℂ) r)).mem_toFinset.mpr hs)
  have hcard : ((productReflectedZeros q X U r).card : ℤ) ≤ ∑ᶠ s, D s := by
    rw [hsum]
    calc
      ((productReflectedZeros q X U r).card : ℤ) = ∑ _s ∈ productReflectedZeros q X U r, (1 : ℤ) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro s hs
        have hsm := (D.finiteSupport (isCompact_closedBall (2 : ℂ) r)).mem_toFinset.mp hs
        have he := productReflection_divisor_apply q hX hqX (U := U) (D.supportWithinDomain hsm)
        have hn : D s ≠ 0 := hsm
        change D s = _ at he
        rw [he] at hn ⊢
        have hp : (0 : ℤ) ≤ (analyticOrderNatAt (productReflection q X U) s : ℤ) := Int.natCast_nonneg _
        omega
  exact_mod_cast hcard

end LiuWang.Proof.SourceRoute.Density.Restart
