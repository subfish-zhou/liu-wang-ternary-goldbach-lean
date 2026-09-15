import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation.ArgumentVariation

/-! The source's `(n + 1) pi` bound for an argument anchored in the right half-plane. -/

set_option autoImplicit false

noncomputable section

open Complex Set

namespace LiuWang.Proof.SourceRoute.Density.Restart

theorem argument_start_le {A : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hA : ContinuousOn A (Icc a b)) (S : Finset ℂ)
    (hS : ∀ t ∈ Icc a b, Real.cos (A t) = 0 → (t : ℂ) ∈ S)
    (hb : A b ≤ Real.pi / 2) :
    A a ≤ (S.card + 1 : ℝ) * Real.pi := by
  classical
  by_contra hbound
  have hlarge : (S.card + 1 : ℝ) * Real.pi < A a := lt_of_not_ge hbound
  let v (k : Fin (S.card + 1)) : ℝ := Real.pi / 2 + (k.val : ℝ) * Real.pi
  have hv (k : Fin (S.card + 1)) : v k ∈ Icc (A b) (A a) := by
    have hk : (k.val : ℝ) ≤ S.card := by exact_mod_cast Nat.le_of_lt_succ k.isLt
    have hk0 : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
    dsimp [v]
    constructor <;> nlinarith [Real.pi_pos]
  have hex (k : Fin (S.card + 1)) : ∃ t ∈ Icc a b, A t = v k :=
    intermediate_value_Icc' hab hA (hv k)
  choose g hg hgA using hex
  have hgS (k : Fin (S.card + 1)) : (g k : ℂ) ∈ S := by
    apply hS (g k) (hg k)
    rw [hgA]
    dsimp [v]
    rw [Real.cos_add_nat_mul_pi, Real.cos_pi_div_two, mul_zero]
  let G : Fin (S.card + 1) → {z : ℂ // z ∈ S} := fun k => ⟨g k, hgS k⟩
  have hG : Function.Injective G := by
    intro j k hjk
    have he : g j = g k := Complex.ofReal_injective (congrArg Subtype.val hjk)
    have hvjk : v j = v k := by rw [← hgA j, ← hgA k, he]
    have hcast : (j.val : ℝ) = k.val := by
      dsimp [v] at hvjk
      nlinarith [Real.pi_pos]
    exact Fin.ext (by exact_mod_cast hcast)
  have hcard := Fintype.card_le_of_injective G hG
  simp only [Fintype.card_fin, Fintype.card_coe] at hcard
  omega

theorem anchored_argument_bound {A : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hA : ContinuousOn A (Icc a b)) (S : Finset ℂ)
    (hS : ∀ t ∈ Icc a b, Real.cos (A t) = 0 → (t : ℂ) ∈ S)
    (hb : |A b| ≤ Real.pi / 2) :
    |A a| ≤ (S.card + 1 : ℝ) * Real.pi := by
  have hp := argument_start_le hab hA S hS (abs_le.mp hb).2
  have hm := argument_start_le hab hA.neg S
    (fun t ht hz => hS t ht (by simpa only [Pi.neg_apply, Real.cos_neg] using hz))
    (by dsimp; linarith [(abs_le.mp hb).1])
  simp only [Pi.neg_apply] at hm
  exact abs_le.mpr ⟨by linarith, hp⟩

theorem argument_stays_right {A : ℝ → ℝ} {a b : ℝ}
    (hA : ContinuousOn A (Icc a b))
    (hcos : ∀ t ∈ Icc a b, Real.cos (A t) ≠ 0)
    (hb : |A b| < Real.pi / 2) {x : ℝ} (hx : x ∈ Icc a b) :
    |A x| < Real.pi / 2 := by
  by_contra hx'
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc' hx.2
    (hA.abs.mono (Icc_subset_Icc hx.1 le_rfl)) ⟨hb.le, le_of_not_gt hx'⟩
  dsimp at he
  apply hcos t (Icc_subset_Icc hx.1 le_rfl ht)
  rw [← Real.cos_abs, he, Real.cos_pi_div_two]

end LiuWang.Proof.SourceRoute.Density.Restart
