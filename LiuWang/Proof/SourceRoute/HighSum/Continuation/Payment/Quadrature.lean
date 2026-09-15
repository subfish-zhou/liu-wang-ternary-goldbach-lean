import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.UniformReduction
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! # Directed finite quadrature of the original exponential terms

Concavity of `-s-A/s` supplies a tangent upper bound and a chord lower
bound. The latter is used for the negative endpoint of the signed profile.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment

def phase (A s : ℝ) : ℝ := -s - A / s

def chord (u v a b s : ℝ) : ℝ := (v - s) / (v - u) * a + (s - u) / (v - u) * b

def tangent (A m s : ℝ) : ℝ := phase A m + (A / m ^ (2 : ℕ) - 1) * (s - m)

theorem chord_integrable (u v a b : ℝ) :
    IntervalIntegrable (chord u v a b) volume u v := by
  apply Continuous.intervalIntegrable
  unfold chord
  fun_prop

theorem integral_chord {u v : ℝ} (huv : u < v) (a b : ℝ) :
    (∫ s in u..v, chord u v a b s) = (v - u) * (a + b) / 2 := by
  have hn : v - u ≠ 0 := (sub_pos.mpr huv).ne'
  have he (s : ℝ) : chord u v a b s =
      ((b - a) / (v - u)) * s + (v * a - u * b) / (v - u) := by
    unfold chord
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_add
    ((show Continuous (fun s : ℝ => ((b - a) / (v - u)) * s) by fun_prop).intervalIntegrable _ _)
    intervalIntegrable_const,
    intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  field_simp
  ring

theorem phase_le_tangent {A m s : ℝ} (hA : 0 ≤ A) (hm : 0 < m) (hs : 0 < s) :
    phase A s ≤ tangent A m s := by
  have he : tangent A m s - phase A s = A * (s - m) ^ (2 : ℕ) / (m ^ (2 : ℕ) * s) := by
    unfold tangent phase
    field_simp
    ring
  have hn : 0 ≤ A * (s - m) ^ (2 : ℕ) / (m ^ (2 : ℕ) * s) := by positivity
  linarith

theorem chord_le_phase {A u v s : ℝ} (hA : 0 ≤ A) (hu : 0 < u)
    (huv : u < v) (hs : s ∈ Set.Icc u v) :
    chord u v (phase A u) (phase A v) s ≤ phase A s := by
  have hv := hu.trans huv
  have hs0 := hu.trans_le hs.1
  have hn : v - u ≠ 0 := (sub_pos.mpr huv).ne'
  have he : phase A s - chord u v (phase A u) (phase A v) s =
      A * (s - u) * (v - s) / (u * v * s) := by
    unfold phase chord
    field_simp
    ring
  have hh : 0 ≤ A * (s - u) * (v - s) / (u * v * s) := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg hA (sub_nonneg.mpr hs.1)) (sub_nonneg.mpr hs.2))
      (by positivity)
  linarith

theorem exp_phase_integrable (A : ℝ) {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    IntervalIntegrable (fun s => Real.exp (phase A s)) volume u v := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le huv]
  have hn (s : ℝ) (hs : s ∈ Set.Icc u v) : s ≠ 0 := (hu.trans_le hs.1).ne'
  unfold phase
  fun_prop

theorem cell_exp_upper {A u v : ℝ} (hA : 0 ≤ A) (hu : 0 < u) (huv : u < v) :
    (∫ s in u..v, Real.exp (phase A s)) ≤
      (v - u) / 2 * (Real.exp (tangent A ((u + v) / 2) u) +
        Real.exp (tangent A ((u + v) / 2) v)) := by
  let m := (u + v) / 2
  have hm : 0 < m := by dsimp [m]; linarith
  have hd : 0 < v - u := sub_pos.mpr huv
  have hp (s : ℝ) (hs : s ∈ Set.Icc u v) :
      Real.exp (phase A s) ≤ chord u v
        (Real.exp (tangent A m u)) (Real.exp (tangent A m v)) s := by
    have hw : (v - s) / (v - u) + (s - u) / (v - u) = 1 := by field_simp; ring
    have hh := convexOn_exp.2 (Set.mem_univ (tangent A m u))
      (Set.mem_univ (tangent A m v))
      (div_nonneg (sub_nonneg.mpr hs.2) hd.le)
      (div_nonneg (sub_nonneg.mpr hs.1) hd.le) hw
    have he : (v - s) / (v - u) * tangent A m u +
        (s - u) / (v - u) * tangent A m v = tangent A m s := by
      unfold tangent
      field_simp
      ring
    simp only [smul_eq_mul, he] at hh
    exact (Real.exp_le_exp.mpr (phase_le_tangent hA hm (hu.trans_le hs.1))).trans hh
  have hi := intervalIntegral.integral_mono_on huv.le (exp_phase_integrable A hu huv.le)
    (chord_integrable u v _ _) hp
  rw [integral_chord huv] at hi
  exact hi.trans_eq (by ring)

theorem cell_exp_lower {A u v : ℝ} (hA : 0 ≤ A) (hu : 0 < u) (huv : u < v) :
    (v - u) * Real.exp ((phase A u + phase A v) / 2) ≤
      ∫ s in u..v, Real.exp (phase A s) := by
  let c := (phase A u + phase A v) / 2
  let a := Real.exp c * (1 + phase A u - c)
  let b := Real.exp c * (1 + phase A v - c)
  have hp (s : ℝ) (hs : s ∈ Set.Icc u v) :
      chord u v a b s ≤ Real.exp (phase A s) := by
    have hn : v - u ≠ 0 := (sub_pos.mpr huv).ne'
    have hh := mul_le_mul_of_nonneg_left
      (Real.add_one_le_exp (chord u v (phase A u) (phase A v) s - c)) (Real.exp_pos c).le
    rw [← Real.exp_add, add_sub_cancel] at hh
    have he : chord u v a b s =
        Real.exp c * (chord u v (phase A u) (phase A v) s - c + 1) := by
      dsimp [a, b, chord]
      field_simp
      ring
    rw [he]
    exact hh.trans (Real.exp_le_exp.mpr (chord_le_phase hA hu huv hs))
  have hi := intervalIntegral.integral_mono_on huv.le (chord_integrable u v a b)
    (exp_phase_integrable A hu huv.le) hp
  rw [integral_chord huv] at hi
  exact (show (v - u) * Real.exp c = (v - u) * (a + b) / 2 by dsimp [a, b, c]; ring).trans_le hi

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment
