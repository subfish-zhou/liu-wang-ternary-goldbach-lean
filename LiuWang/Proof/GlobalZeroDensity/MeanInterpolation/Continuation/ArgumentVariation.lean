import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation.ReflectedJensen

set_option autoImplicit false

noncomputable section

open Complex Set

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation

theorem argument_increase_le {A : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hA : ContinuousOn A (Icc a b)) (S : Finset ℂ)
    (hS : ∀ t ∈ Icc a b, Real.cos (A t) = 0 → (t : ℂ) ∈ S) :
    A b - A a ≤ (S.card + 1 : ℝ) * Real.pi := by
  classical
  by_contra hbound
  have hlarge : (S.card + 1 : ℝ) * Real.pi < A b - A a := lt_of_not_ge hbound
  let q : ℝ := (A a - Real.pi / 2) / Real.pi
  let m : ℤ := ⌊q⌋ + 1
  have hlow : A a < Real.pi / 2 + (m : ℝ) * Real.pi := by
    have h := (div_lt_iff₀ Real.pi_pos).mp (Int.lt_floor_add_one q)
    dsimp [q] at h
    dsimp [m]
    push_cast
    linarith
  have hupp : Real.pi / 2 + (m : ℝ) * Real.pi ≤ A a + Real.pi := by
    have h := (le_div_iff₀ Real.pi_pos).mp (Int.floor_le q)
    dsimp [q] at h
    dsimp [m]
    push_cast
    linarith
  let v (k : Fin (S.card + 1)) : ℝ :=
    Real.pi / 2 + ((m + (k.val : ℤ) : ℤ) : ℝ) * Real.pi
  have hv (k : Fin (S.card + 1)) : v k ∈ Icc (A a) (A b) := by
    have hk : (k.val : ℝ) ≤ S.card := by exact_mod_cast Nat.le_of_lt_succ k.isLt
    have hk0 : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
    dsimp [v]
    push_cast
    constructor <;> nlinarith [Real.pi_pos]
  have hex (k : Fin (S.card + 1)) : ∃ t ∈ Icc a b, A t = v k :=
    intermediate_value_Icc hab hA (hv k)
  choose g hg hgA using hex
  have hgS (k : Fin (S.card + 1)) : (g k : ℂ) ∈ S := by
    apply hS (g k) (hg k)
    rw [hgA]
    dsimp [v]
    rw [Real.cos_add_int_mul_pi, Real.cos_pi_div_two, mul_zero]
  let G : Fin (S.card + 1) → {z : ℂ // z ∈ S} := fun k => ⟨g k, hgS k⟩
  have hG : Function.Injective G := by
    intro j k hjk
    have he : g j = g k := Complex.ofReal_injective (congrArg Subtype.val hjk)
    have hvjk : v j = v k := by rw [← hgA j, ← hgA k, he]
    have hcast : (j.val : ℝ) = k.val := by
      dsimp [v] at hvjk
      push_cast at hvjk
      nlinarith [Real.pi_pos]
    exact Fin.ext (by exact_mod_cast hcast)
  have hcard := Fintype.card_le_of_injective G hG
  simp only [Fintype.card_fin, Fintype.card_coe] at hcard
  omega

theorem argument_variation_le {A : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hA : ContinuousOn A (Icc a b)) (S : Finset ℂ)
    (hS : ∀ t ∈ Icc a b, Real.cos (A t) = 0 → (t : ℂ) ∈ S) :
    |A b - A a| ≤ (S.card + 1 : ℝ) * Real.pi := by
  have hp := argument_increase_le hab hA S hS
  have hm := argument_increase_le hab hA.neg S
    (fun t ht hz => hS t ht (by simpa using hz))
  simp only [Pi.neg_apply] at hm
  exact abs_le.mpr ⟨by linarith, hp⟩

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation
