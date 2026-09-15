import LiuWang.Proof.DirichletZeroCount.Applications.RightLimit
import PrimeNumberTheoremAnd.RectangleArgumentPrinciple

/-! # Entire-function rectangle integrals with actual analytic multiplicities -/

set_option autoImplicit false
noncomputable section

open Complex Complex.Hadamard
open scoped BigOperators
open Classical

namespace LiuWang.Proof.DirichletZeroCount.Argument

def lowerCorner (b H : ℝ) : ℂ := (1 - b : ℝ) - (H : ℂ) * I
def upperCorner (b H : ℝ) : ℂ := (b : ℂ) + (H : ℂ) * I

theorem mem_rectangle {b H : ℝ} (hb : 1 < b) (hH : 0 ≤ H) (s : ℂ) :
    s ∈ Rectangle (lowerCorner b H) (upperCorner b H) ↔
      1 - b ≤ s.re ∧ s.re ≤ b ∧ -H ≤ s.im ∧ s.im ≤ H := by
  rw [mem_Rect (by simp [lowerCorner, upperCorner]; linarith)
    (by simp [lowerCorner, upperCorner]; linarith)]
  simp [lowerCorner, upperCorner]

theorem mem_border {b H : ℝ} (hb : 1 < b) (hH : 0 ≤ H) (s : ℂ) :
    s ∈ RectangleBorder (lowerCorner b H) (upperCorner b H) ↔
      (((1 - b ≤ s.re ∧ s.re ≤ b) ∧ s.im = -H) ∨
        (s.re = 1 - b ∧ (-H ≤ s.im ∧ s.im ≤ H))) ∨
      ((1 - b ≤ s.re ∧ s.re ≤ b) ∧ s.im = H) ∨
        (s.re = b ∧ (-H ≤ s.im ∧ s.im ≤ H)) := by
  simp only [RectangleBorder, lowerCorner, upperCorner]
  simp only [sub_re, sub_im, add_re, add_im, ofReal_re, ofReal_im, mul_re, mul_im,
    I_re, I_im, mul_zero, mul_one, sub_zero, zero_sub, add_zero, zero_add]
  rw [Set.uIcc_of_le (by linarith : 1 - b ≤ b), Set.uIcc_of_le (by linarith : -H ≤ H)]
  change (((_ ∧ _) ∨ (_ ∧ _)) ∨ (_ ∧ _)) ∨ (_ ∧ _) ↔ _
  simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_singleton_iff]
  tauto

theorem entire_order_finite {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hn : ∃ s, f s ≠ 0) (s : ℂ) : meromorphicOrderAt f s ≠ ⊤ := by
  have h := analyticOrderAt_ne_top_of_exists_ne_zero hf hn s
  rw [(hf.analyticAt s).meromorphicOrderAt_eq,
    ← Nat.cast_analyticOrderNatAt h]
  simp

theorem entire_divisor_eq_order {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {U : Set ℂ} {s : ℂ} (hs : s ∈ U) :
    MeromorphicOn.divisor f U s = (analyticOrderNatAt f s : ℤ) := by
  have hm : MeromorphicOn f U := fun z _ => (hf.analyticAt z).meromorphicAt
  have hu : MeromorphicOn f Set.univ := fun z _ => (hf.analyticAt z).meromorphicAt
  rw [MeromorphicOn.divisor_apply hm hs,
    ← MeromorphicOn.divisor_apply hu (Set.mem_univ s)]
  exact divisor_univ_eq_analyticOrderNatAt_int hf s

theorem entire_rectangle_count {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hn : ∃ s, f s ≠ 0) {z w : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (V : Finset ℂ) (hV : ∀ s, s ∈ V ↔ s ∈ Rectangle z w ∧ f s = 0)
    (hborder : ∀ s ∈ RectangleBorder z w, f s ≠ 0) :
    RectangleIntegral' (logDeriv f) z w =
      ∑ s ∈ V, (analyticOrderNatAt f s : ℂ) := by
  have hm : MeromorphicOn f (Rectangle z w) :=
    fun s _ => (hf.analyticAt s).meromorphicAt
  have hl : MeromorphicOn (logDeriv f) (Rectangle z w) :=
    fun s _ => (hf.analyticAt s).deriv.meromorphicAt.div (hf.analyticAt s).meromorphicAt
  have hsupp : (divisor_support_rectangle_finite f z w).toFinset = V := by
    ext s
    rw [Set.Finite.mem_toFinset, hV]
    constructor
    · intro hs
      have hsR := (MeromorphicOn.divisor f (Rectangle z w)).supportWithinDomain hs
      refine ⟨hsR, ?_⟩
      apply apply_eq_zero_of_analyticOrderNatAt_ne_zero
      intro hzero
      have hne : MeromorphicOn.divisor f (Rectangle z w) s ≠ 0 := hs
      rw [entire_divisor_eq_order hf hsR, hzero, Nat.cast_zero] at hne
      exact hne rfl
    · rintro ⟨hsR, hz⟩
      change MeromorphicOn.divisor f (Rectangle z w) s ≠ 0
      rw [entire_divisor_eq_order hf hsR]
      have hfinite := analyticOrderAt_ne_top_of_exists_ne_zero hf hn s
      have hpos : analyticOrderAt f s ≠ 0 :=
        (hf.analyticAt s).analyticOrderAt_ne_zero.mpr hz
      have hnzero : analyticOrderNatAt f s ≠ 0 := by
        intro heq
        rw [← Nat.cast_analyticOrderNatAt hfinite, heq] at hpos
        simp at hpos
      exact_mod_cast hnzero
  have hdisj : Disjoint (RectangleBorder z w)
      (MeromorphicOn.divisor f (Rectangle z w)).support := by
    rw [Set.disjoint_left]
    intro s hs hz
    have hv : s ∈ V := by
      rw [← hsupp]
      exact (divisor_support_rectangle_finite f z w).mem_toFinset.mpr hz
    exact hborder s hs ((hV s).mp hv).2
  rw [rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt hre him hm hl
    (fun s _ => entire_order_finite hf hn s) hdisj, hsupp]
  apply Finset.sum_congr rfl
  intro s hs
  rw [entire_divisor_eq_order hf ((hV s).mp hs).1]
  simp

end LiuWang.Proof.DirichletZeroCount.Argument
