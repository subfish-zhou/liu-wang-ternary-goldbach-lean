import LiuWang.Proof.SourceRoute.Density.FamilyBoundary
import Mathlib.Analysis.Complex.JensenFormula

/-! Conjugate reflection for complex characters, without a real-character assumption. -/

set_option autoImplicit false

noncomputable section

open Complex Set Metric
open scoped ComplexConjugate
open LiuWang.Proof.Interfaces (Character)
open LiuWang.Proof.NonprincipalDensityAdvance

namespace LiuWang.Proof.SourceRoute.Density

def reflectedDetector {q : ℕ} [NeZero q] (chi : Character q) (X h : ℝ) (s : ℂ) : ℂ :=
  H chi X (s + h * I) + conj (H chi X (conj s + h * I))

theorem reflectedDetector_real {q : ℕ} [NeZero q] (chi : Character q) (X h x : ℝ) :
    reflectedDetector chi X h x = (2 * (H chi X ((x : ℂ) + h * I)).re : ℝ) := by
  simp only [reflectedDetector, conj_ofReal]
  exact Complex.add_conj _

theorem reflectedDetector_real_zero_iff {q : ℕ} [NeZero q]
    (chi : Character q) (X h x : ℝ) :
    reflectedDetector chi X h x = 0 ↔ (H chi X ((x : ℂ) + h * I)).re = 0 := by
  rw [reflectedDetector_real, ofReal_eq_zero]
  simp

theorem differentiable_reflectedDetector {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (X h : ℝ) : Differentiable ℂ (reflectedDetector chi X h) := by
  have hf : Differentiable ℂ (fun s : ℂ => H chi X (s + h * I)) :=
    (differentiable_H hchi X).comp (differentiable_id.add_const _)
  exact hf.add (fun s => by simpa only [Function.comp_def, conj_conj] using
    (hf (conj s)).conj_conj)

theorem H_re_two_lower {q : ℕ} [NeZero q] (chi : Character q) {X : ℝ}
    (hX : 1 < X) (t : ℝ) :
    1 - 4 / (X - 1) ^ 2 ≤ (H chi X ((2 : ℂ) + t * I)).re := by
  have hn := norm_f_two_le chi (by simp : (((2 : ℂ) + t * I)).re = 2) hX
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hr := Complex.re_le_norm (f chi X ((2 : ℂ) + t * I) ^ 2)
  rw [norm_pow] at hr
  have he : (2 / (X - 1)) ^ 2 = 4 / (X - 1) ^ 2 := by rw [div_pow]; norm_num
  rw [he] at hs
  simp only [H, sub_re, one_re]
  linarith

theorem reflectedDetector_two_lower {q : ℕ} [NeZero q] (chi : Character q)
    {X : ℝ} (hX : 1 < X) (h : ℝ) :
    2 - 8 / (X - 1) ^ 2 ≤ (reflectedDetector chi X h 2).re := by
  have hb := H_re_two_lower chi hX h
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, reflectedDetector_real]
  simp only [ofReal_re, ofReal_ofNat]
  rw [show 2 - 8 / (X - 1) ^ 2 = 2 * (1 - 4 / (X - 1) ^ 2) by ring]
  exact mul_le_mul_of_nonneg_left hb (by norm_num)

theorem reflectedDetector_two_ne_zero {q : ℕ} [NeZero q] (chi : Character q)
    {X : ℝ} (hX : 5 ≤ X) (h : ℝ) : reflectedDetector chi X h 2 ≠ 0 := by
  have hb := reflectedDetector_two_lower chi (by linarith : 1 < X) h
  have hq : 8 / (X - 1) ^ 2 ≤ 1 / 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < X - 1))).mpr
    nlinarith
  intro hz
  rw [hz, zero_re] at hb
  linarith

theorem reflectedDetector_order_finite {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {X : ℝ} (hX : 5 ≤ X) (h : ℝ) (s : ℂ) :
    analyticOrderAt (reflectedDetector chi X h) s ≠ ⊤ :=
  Complex.Hadamard.analyticOrderAt_ne_top_of_exists_ne_zero
    (differentiable_reflectedDetector hchi X h) ⟨2, reflectedDetector_two_ne_zero chi hX h⟩ s

def reflectedZeros {q : ℕ} [NeZero q] (chi : Character q) (X h r : ℝ) : Finset ℂ :=
  ((MeromorphicOn.divisor (reflectedDetector chi X h) (closedBall (2 : ℂ) r)).finiteSupport
    (isCompact_closedBall (2 : ℂ) r)).toFinset

theorem mem_reflectedZeros_of_zero {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {X h r : ℝ} (hX : 5 ≤ X)
    {s : ℂ} (hs : s ∈ closedBall (2 : ℂ) r) (hz : reflectedDetector chi X h s = 0) :
    s ∈ reflectedZeros chi X h r := by
  have hf := differentiable_reflectedDetector hchi X h
  have ho := (hf.analyticAt s).analyticOrderAt_eq_zero
  rw [← Nat.cast_analyticOrderNatAt (reflectedDetector_order_finite hchi hX h s)] at ho
  simp only [Nat.cast_eq_zero] at ho
  have hn : analyticOrderNatAt (reflectedDetector chi X h) s ≠ 0 := fun h => (ho.mp h) hz
  apply ((MeromorphicOn.divisor (reflectedDetector chi X h) (closedBall (2 : ℂ) r)).finiteSupport
    (isCompact_closedBall (2 : ℂ) r)).mem_toFinset.mpr
  rw [Function.mem_support, MeromorphicOn.AnalyticOnNhd.divisor_apply
    (fun z _ => hf.analyticAt z) hs,
    ← Nat.cast_analyticOrderNatAt (reflectedDetector_order_finite hchi hX h s)]
  simpa using hn

end LiuWang.Proof.SourceRoute.Density
