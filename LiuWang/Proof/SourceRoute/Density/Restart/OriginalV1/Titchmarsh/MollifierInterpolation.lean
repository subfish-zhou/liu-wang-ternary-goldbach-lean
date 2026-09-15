import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.AuxiliaryDomain

/-!
LWD p.285, (3.40): the original three-lines step for the actual strict-cutoff
Möbius polynomial. Only the two printed Chen boundary estimates remain inputs.
-/

set_option autoImplicit false
noncomputable section

open Complex Set
open Complex.HadamardThreeLines
open LiuWang.Proof.GlobalZeroDensity

namespace LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.Titchmarsh

theorem Q_diffContOnCl (y : ℝ) :
    DiffContOnCl ℂ (Q y) (verticalStrip (1 / 2) 1) :=
  ⟨(differentiable_Q y).differentiableOn, (differentiable_Q y).continuous.continuousOn⟩

theorem Q_bounded_on_strip (y : ℝ) :
    BddAbove ((norm ∘ Q y) '' verticalClosedStrip (1 / 2) 1) := by
  refine ⟨(⌈y⌉₊ : ℝ), ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  exact Strip.norm_Q_strip_le (by
    change 1 / 2 ≤ s.re ∧ s.re ≤ 1 at hs
    linarith [hs.1]) y

theorem equation_3_40 {y sigma t : ℝ} (hs : sigma ∈ Icc (1 / 2) 1)
    (hchen11 : ∀ u : ℝ, ‖Q y ((1 / 2 : ℂ) + u * I)‖ ≤ 1.3071 * Real.sqrt y)
    (hchen12 : ∀ u : ℝ, ‖Q y ((1 : ℂ) + u * I)‖ ≤ 1.19 * Real.log y) :
    ‖Q y ((sigma : ℂ) + t * I)‖ ≤
      (1.3071 * Real.sqrt y) ^ (2 * (1 - sigma)) *
        (1.19 * Real.log y) ^ (2 * sigma - 1) := by
  have h := norm_le_interp_of_mem_verticalClosedStrip'
    (f := Q y) (z := (sigma : ℂ) + t * I) (by norm_num : (1 / 2 : ℝ) < 1)
    (by simpa [verticalClosedStrip] using hs) (Q_diffContOnCl y) (Q_bounded_on_strip y)
    (a := 1.3071 * Real.sqrt y) (b := 1.19 * Real.log y)
    (fun s hs => by
      have hs' : s.re = 1 / 2 := hs
      have he : s = (1 / 2 : ℂ) + s.im * I := by
        apply Complex.ext <;> simp [hs']
      rw [he]
      exact hchen11 s.im)
    (fun s hs => by
      have hs' : s.re = 1 := hs
      have he : s = (1 : ℂ) + s.im * I := by
        apply Complex.ext <;> simp [hs']
      rw [he]
      exact hchen12 s.im)
  have he1 : (1 : ℝ) - (2 * sigma - 1) = 2 * (1 - sigma) := by ring
  have he2 : (sigma - 1 / 2) / (1 - 1 / 2) = 2 * sigma - 1 := by ring
  simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, zero_mul, sub_self, add_zero, he2, he1] using h

end LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.Titchmarsh
