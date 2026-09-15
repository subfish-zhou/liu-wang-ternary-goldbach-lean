import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic.Counting
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
noncomputable section

open Finset MeasureTheory Set
open scoped ArithmeticFunction.Moebius

namespace LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic

def weightedSum (y : ℝ) (w : ℝ → ℝ) : ℝ :=
  ∑ n ∈ positiveBelow y, w n * |(μ n : ℝ)|

def countMajorant (x : ℝ) : ℝ := 6 / Real.pi ^ 2 * x + 2 * Real.sqrt x + 1

private def truncatedCoeff (y : ℝ) (n : ℕ) : ℝ :=
  if (n : ℝ) < y then |(μ n : ℝ)| else 0

private theorem truncated_sum (y : ℝ) (w : ℝ → ℝ) :
    (∑ n ∈ Icc 0 ⌊y⌋₊, w n * truncatedCoeff y n) = weightedSum y w := by
  classical
  have hsub : positiveBelow y ⊆ Icc 0 ⌊y⌋₊ := by
    intro n hn
    exact mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor (mem_positiveBelow.mp hn).2.le⟩
  rw [weightedSum, ← sum_subset hsub]
  · apply sum_congr rfl
    intro n hn
    rw [truncatedCoeff, if_pos (mem_positiveBelow.mp hn).2]
  · intro n _ hn
    by_cases hn0 : n = 0
    · subst n; simp [truncatedCoeff]
    · have hny : ¬(n : ℝ) < y := by
        intro h; exact hn (mem_positiveBelow.mpr ⟨Nat.pos_of_ne_zero hn0, h⟩)
      simp [truncatedCoeff, hny]

private theorem truncated_prefix {y t : ℝ} (ht : 0 ≤ t) (hty : t ≤ y)
    (hnt : t ∉ Set.range (fun n : ℕ => (n : ℝ))) :
    (∑ n ∈ Icc 0 ⌊t⌋₊, truncatedCoeff y n) = squarefreeCount t := by
  have hlt (n : ℕ) (hn : n ∈ Finset.Icc 0 ⌊t⌋₊) : (n : ℝ) < t := by
    have hn' : (n : ℝ) ≤ t := (Nat.le_floor_iff ht).mp (Finset.mem_Icc.mp hn).2
    exact hn'.lt_of_ne (by intro h; exact hnt ⟨n, h⟩)
  have he : (∑ n ∈ Icc 0 ⌊t⌋₊, truncatedCoeff y n) =
      ∑ n ∈ Icc 0 ⌊t⌋₊, (1 : ℝ) * truncatedCoeff t n := by
    apply sum_congr rfl
    intro n hn
    simp only [truncatedCoeff, if_pos (hlt n hn), if_pos ((hlt n hn).trans_le hty), one_mul]
  rw [he, truncated_sum t (fun _ => 1)]
  simp [weightedSum, squarefreeCount]

theorem abel_upper {y : ℝ} (hy : 1 ≤ y) (w dw H : ℝ → ℝ)
    (hw : ∀ x ∈ Icc 1 y, HasDerivAt w (dw x) x)
    (hdw : ContinuousOn dw (Icc 1 y))
    (hw0 : 0 ≤ w y) (hdw0 : ∀ x ∈ Icc 1 y, dw x ≤ 0)
    (hH : ∀ x ∈ Icc 1 y, HasDerivAt H (-dw x * countMajorant x) x) :
    weightedSum y w ≤ w y * countMajorant y + H y - H 1 := by
  classical
  let c := truncatedCoeff y
  have hd : Set.EqOn (deriv w) dw (Icc 1 y) := fun x hx => (hw x hx).deriv
  have hdi : IntegrableOn (deriv w) (Icc 1 y) :=
    hdw.integrableOn_Icc.congr_fun (fun x hx => (hd hx).symm) measurableSet_Icc
  have hraw := sum_mul_eq_sub_integral_mul₀ c (by simp [c, truncatedCoeff]) y
    (fun x hx => (hw x hx).differentiableAt) hdi
  have hec : (∑ n ∈ Icc 0 ⌊y⌋₊, c n) = squarefreeCount y := by
    simpa [weightedSum, squarefreeCount, c] using
      truncated_sum y (fun _ => 1)
  rw [truncated_sum y, hec] at hraw
  have hci : IntegrableOn
      (fun t => deriv w t * ∑ n ∈ Icc 0 ⌊t⌋₊, c n) (Ioc 1 y) :=
    (integrableOn_mul_sum_Icc c (by norm_num : (0 : ℝ) ≤ 1) hdi).mono_set
      Ioc_subset_Icc_self
  have hbi : IntegrableOn (fun t => -dw t * countMajorant t) (Icc 1 y) := by
    apply ContinuousOn.integrableOn_Icc
    exact hdw.neg.mul (by unfold countMajorant; fun_prop)
  have hcmp :
      (∫ t in Ioc 1 y, -(deriv w t * ∑ n ∈ Icc 0 ⌊t⌋₊, c n)) ≤
        ∫ t in Ioc 1 y, -dw t * countMajorant t := by
    apply integral_mono_ae hci.neg (hbi.mono_set Ioc_subset_Icc_self)
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae ((Set.countable_range (fun n : ℕ => (n : ℝ))).ae_notMem volume)]
      with t ht hnt
    have ht' : t ∈ Icc 1 y := ⟨ht.1.le, ht.2⟩
    change -(deriv w t * ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, truncatedCoeff y n) ≤ _
    rw [hd ht', truncated_prefix (by linarith [ht.1]) ht.2 hnt]
    simpa only [neg_mul, countMajorant] using
      mul_le_mul_of_nonneg_left (squarefreeCount_upper ht'.1)
      (neg_nonneg.mpr (hdw0 t ht'))
  have hint : (∫ t in Ioc 1 y, -dw t * countMajorant t) = H y - H 1 := by
    rw [← intervalIntegral.integral_of_le hy]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (by simpa only [uIcc_of_le hy] using hH)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hy).mpr hbi)
  rw [integral_neg, hint] at hcmp
  have he := mul_le_mul_of_nonneg_left (squarefreeCount_upper hy) hw0
  unfold countMajorant at *
  linarith

end LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic
