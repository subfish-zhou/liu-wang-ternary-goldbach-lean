import Mathlib.NumberTheory.Chebyshev
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Group.ForwardDiff

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open MeasureTheory Set

namespace LiuWang.Proof.Campaign20260915.Totient

def rsPsiBox (h : ℝ) : ℕ → ℝ → ℝ
  | 0 => Chebyshev.psi
  | m + 1 => fun x => ∫ t in (0 : ℝ)..h, rsPsiBox h m (x + t)

theorem rsPsiBox_monotone {h : ℝ} (hh : 0 ≤ h) (m : ℕ) :
    Monotone (rsPsiBox h m) := by
  induction m with
  | zero => exact Chebyshev.psi_mono
  | succ m ih =>
    intro x y hxy
    apply intervalIntegral.integral_mono hh
      (ih.comp (monotone_id.const_add x)).intervalIntegrable
      (ih.comp (monotone_id.const_add y)).intervalIntegrable
    intro t
    exact ih (by linarith)

theorem rsPsiBox_bounds {h : ℝ} (hh : 0 ≤ h) (m : ℕ) (x : ℝ) :
    h ^ m * Chebyshev.psi x ≤ rsPsiBox h m x ∧
      rsPsiBox h m x ≤ h ^ m * Chebyshev.psi (x + (m : ℝ) * h) := by
  induction m generalizing x with
  | zero => simp [rsPsiBox]
  | succ m ih =>
    have hi : IntervalIntegrable (fun t => rsPsiBox h m (x + t)) volume 0 h :=
      ((rsPsiBox_monotone hh m).comp (monotone_id.const_add x)).intervalIntegrable
    have hlo := intervalIntegral.integral_mono_on hh intervalIntegrable_const hi
      (fun t ht => (mul_le_mul_of_nonneg_left
        (Chebyshev.psi_mono (by linarith [ht.1] : x ≤ x + t))
        (pow_nonneg hh m)).trans (ih (x + t)).1)
    have hup := intervalIntegral.integral_mono_on hh hi intervalIntegrable_const
      (fun t ht => (ih (x + t)).2.trans (mul_le_mul_of_nonneg_left
        (Chebyshev.psi_mono (show x + t + (m : ℝ) * h ≤
          x + ((m : ℝ) + 1) * h by linarith [ht.2]))
        (pow_nonneg hh m)))
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hlo hup
    constructor
    · simpa only [rsPsiBox, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hlo
    · simpa only [rsPsiBox, Nat.cast_add, Nat.cast_one, pow_succ,
        mul_assoc, mul_left_comm, mul_comm] using hup

theorem rsPsiBox_desmoothing {h : ℝ} (hh : 0 < h) (m : ℕ) (x : ℝ) :
    rsPsiBox h m (x - (m : ℝ) * h) / h ^ m ≤ Chebyshev.psi x ∧
      Chebyshev.psi x ≤ rsPsiBox h m x / h ^ m := by
  have hlo := (rsPsiBox_bounds hh.le m (x - (m : ℝ) * h)).2
  have hup := (rsPsiBox_bounds hh.le m x).1
  simp only [sub_add_cancel] at hlo
  constructor
  · exact (div_le_iff₀ (pow_pos hh m)).mpr (by simpa only [mul_comm] using hlo)
  · exact (le_div_iff₀ (pow_pos hh m)).mpr (by simpa only [mul_comm] using hup)

theorem rsPsiBox_original_domain {m : ℕ} {δ a x : ℝ}
    (hδ : 0 < δ) (ha : 0 < a) (hcut : 1 + (m : ℝ) * δ * a < a)
    (hax : a ≤ x) :
    0 < δ * x ∧ 1 < x - (m : ℝ) * (δ * x) := by
  have hc : 0 < 1 - (m : ℝ) * δ := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hax hc.le
  constructor
  · exact mul_pos hδ (ha.trans_le hax)
  · nlinarith

theorem rsPsiBox_original_desmoothing {m : ℕ} {δ a x : ℝ}
    (hδ : 0 < δ) (ha : 0 < a) (hcut : 1 + (m : ℝ) * δ * a < a)
    (hax : a ≤ x) :
    1 < x - (m : ℝ) * (δ * x) ∧
      rsPsiBox (δ * x) m (x - (m : ℝ) * (δ * x)) / (δ * x) ^ m ≤
        Chebyshev.psi x ∧
      Chebyshev.psi x ≤ rsPsiBox (δ * x) m x / (δ * x) ^ m := by
  have hd := rsPsiBox_original_domain hδ ha hcut hax
  exact ⟨hd.2, rsPsiBox_desmoothing hd.1 m x⟩

#print axioms rsPsiBox_monotone
#print axioms rsPsiBox_bounds
#print axioms rsPsiBox_desmoothing
#print axioms rsPsiBox_original_domain
#print axioms rsPsiBox_original_desmoothing

end LiuWang.Proof.Campaign20260915.Totient
