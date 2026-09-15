import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation.LineParts

/-! Compatible logarithms on three sides, with the harmless cut at the left-bottom corner. -/

set_option autoImplicit false

noncomputable section

open Complex Set MeasureTheory
open scoped Interval

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation

def rightLog (f : ℂ → ℂ) (b d t : ℝ) : ℂ :=
  lineLog f b I d (Complex.log (f ((b : ℂ) + d * I))) t

def horizontalLog (f : ℂ → ℂ) (b d h x : ℝ) : ℂ :=
  lineLog f (h * I) 1 b (rightLog f b d h) x

def leftLog (f : ℂ → ℂ) (a b d t : ℝ) : ℂ :=
  lineLog f a I d (horizontalLog f b d d a) t

theorem rectangle_nonzero_lines {f : ℂ → ℂ} {a b c d : ℝ}
    (hn : ∀ s ∈ RectangleBorder ((a : ℂ) + c * I) ((b : ℂ) + d * I), f s ≠ 0) :
    (∀ x ∈ [[a, b]], f ((x : ℂ) + c * I) ≠ 0) ∧
    (∀ x ∈ [[a, b]], f ((x : ℂ) + d * I) ≠ 0) ∧
    (∀ t ∈ [[c, d]], f ((a : ℂ) + t * I) ≠ 0) ∧
    (∀ t ∈ [[c, d]], f ((b : ℂ) + t * I) ≠ 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    apply hn
    simp [RectangleBorder, mem_reProdIm, hx]
  · intro x hx
    apply hn
    simp [RectangleBorder, mem_reProdIm, hx]
  · intro t ht
    apply hn
    simp [RectangleBorder, mem_reProdIm, ht]
  · intro t ht
    apply hn
    simp [RectangleBorder, mem_reProdIm, ht]

theorem rectangle_complex_log_formula {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {a b c d : ℝ}
    (hn : ∀ s ∈ RectangleBorder ((a : ℂ) + c * I) ((b : ℂ) + d * I), f s ≠ 0) :
    RectangleIntegral (fun s => (s - ((a : ℂ) + c * I)) * logDeriv f s)
      ((a : ℂ) + c * I) ((b : ℂ) + d * I) =
      -(∫ x in a..b, horizontalLog f b d c x) +
        (∫ x in a..b, horizontalLog f b d d x) -
          I * (∫ t in c..d, rightLog f b d t) +
            I * (∫ t in c..d, leftLog f a b d t) := by
  obtain ⟨hc, hd, ha, hb⟩ := rectangle_nonzero_lines hn
  have hc' : ∀ x ∈ [[a, b]], lineValue f (c * I) 1 x ≠ 0 := by
    simpa [lineValue, add_comm] using hc
  have hd' : ∀ x ∈ [[a, b]], lineValue f (d * I) 1 x ≠ 0 := by
    simpa [lineValue, add_comm] using hd
  have hbot := line_integral_parts hf (c := (a : ℂ) + c * I)
    (l := rightLog f b d c) hc'
  have htop := line_integral_parts hf (c := (a : ℂ) + c * I)
    (l := rightLog f b d d) hd'
  have hright := line_integral_parts hf (p := b) (v := I) (a := c) (b := d)
    (c := (a : ℂ) + c * I) (l := Complex.log (f ((b : ℂ) + d * I))) hb
  have hleft := line_integral_parts hf (p := a) (v := I) (a := c) (b := d)
    (c := (a : ℂ) + c * I) (l := horizontalLog f b d d a) ha
  simp only [lineSlope, mul_one, one_mul] at hbot htop
  simp_rw [add_comm ((c : ℂ) * I), add_comm ((d : ℂ) * I)] at hbot htop
  change (∫ x in a..b, ((x : ℂ) + c * I - ((a : ℂ) + c * I)) * logDeriv f ((x : ℂ) + c * I)) =
    _ at hbot
  change (∫ x in a..b, ((x : ℂ) + d * I - ((a : ℂ) + c * I)) * logDeriv f ((x : ℂ) + d * I)) =
    _ at htop
  have hright_int :
      (∫ t in c..d, ((b : ℂ) + t * I - ((a : ℂ) + c * I)) * lineSlope f b I t) =
        I * ∫ t in c..d, ((b : ℂ) + t * I - ((a : ℂ) + c * I)) * logDeriv f ((b : ℂ) + t * I) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    unfold lineSlope
    ring
  have hleft_int :
      (∫ t in c..d, ((a : ℂ) + t * I - ((a : ℂ) + c * I)) * lineSlope f a I t) =
        I * ∫ t in c..d, ((a : ℂ) + t * I - ((a : ℂ) + c * I)) * logDeriv f ((a : ℂ) + t * I) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    unfold lineSlope
    ring
  rw [hright_int] at hright
  rw [hleft_int] at hleft
  simp only [RectangleIntegral, HIntegral, VIntegral, add_re, ofReal_re, mul_I_re,
    ofReal_im, neg_zero, add_zero, add_im, mul_I_im, zero_add, smul_eq_mul]
  rw [hbot, htop, hright, hleft]
  change _ = -(∫ x in a..b, lineLog f (c * I) 1 b (rightLog f b d c) x) +
    (∫ x in a..b, lineLog f (d * I) 1 b (rightLog f b d d) x) -
      I * (∫ t in c..d, lineLog f b I d (Complex.log (f ((b : ℂ) + d * I))) t) +
        I * (∫ t in c..d, lineLog f a I d (horizontalLog f b d d a) t)
  simp only [horizontalLog, rightLog, lineLog_anchor]
  ring

theorem rightLog_exp {f : ℂ → ℂ} (hf : Differentiable ℂ f) {b c d t : ℝ}
    (hn : ∀ u ∈ [[c, d]], f ((b : ℂ) + u * I) ≠ 0) (ht : t ∈ [[c, d]]) :
    Complex.exp (rightLog f b d t) = f ((b : ℂ) + t * I) :=
  exp_lineLog hf ht hn (Complex.exp_log (hn d right_mem_uIcc))

theorem horizontalLog_exp {f : ℂ → ℂ} (hf : Differentiable ℂ f) {a b c d h x : ℝ}
    (hv : ∀ u ∈ [[c, d]], f ((b : ℂ) + u * I) ≠ 0) (hh : h ∈ [[c, d]])
    (hn : ∀ u ∈ [[a, b]], f ((u : ℂ) + h * I) ≠ 0) (hx : x ∈ [[a, b]]) :
    Complex.exp (horizontalLog f b d h x) = f ((x : ℂ) + h * I) := by
  have hpath : ∀ u ∈ [[a, b]], lineValue f (h * I) 1 u ≠ 0 := by
    simpa [lineValue, add_comm] using hn
  have hl : Complex.exp (rightLog f b d h) = lineValue f (h * I) 1 b := by
    simpa [lineValue, add_comm] using rightLog_exp hf hv hh
  simpa [horizontalLog, lineValue, add_comm] using exp_lineLog hf hx hpath hl

theorem leftLog_exp {f : ℂ → ℂ} (hf : Differentiable ℂ f) {a b c d t : ℝ}
    (hn : ∀ s ∈ RectangleBorder ((a : ℂ) + c * I) ((b : ℂ) + d * I), f s ≠ 0)
    (ht : t ∈ [[c, d]]) :
    Complex.exp (leftLog f a b d t) = f ((a : ℂ) + t * I) := by
  obtain ⟨_, hd, ha, hb⟩ := rectangle_nonzero_lines hn
  exact exp_lineLog hf ht ha (horizontalLog_exp hf hb right_mem_uIcc hd left_mem_uIcc)

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation
