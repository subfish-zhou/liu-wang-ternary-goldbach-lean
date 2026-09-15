import LiuWang.Proof.SingularSeries.Uniform.Abel

/-! The strict real tail q>P, uniformly in N, from finite nonnegative sums. -/

set_option autoImplicit false
noncomputable section
open Finset

namespace LiuWang.Proof.SingularSeries.Uniform

theorem strict_tail_index_iff {P : ℝ} (hP : 0 ≤ P) (q : ℕ) :
    P < (q : ℝ) ↔ ⌊P⌋₊ + 1 ≤ q := by
  rw [← Nat.floor_lt hP, Nat.succ_le_iff]

theorem inverse_totient_strict_tail_finite {P : ℝ} (hP : 1 ≤ P)
    (s : Finset {q : ℕ // P < (q : ℝ)}) :
    (∑ q ∈ s, 1 / ((q : ℕ).totient : ℝ) ^ 2) ≤ 44 / P := by
  classical
  let m : ℕ := ⌊P⌋₊ + 1
  let B : ℕ := s.sup (fun q => (q : ℕ))
  have hsub : s.image (fun q : {q : ℕ // P < (q : ℝ)} => (q : ℕ)) ⊆ Icc m B := by
    intro q hq
    rcases mem_image.mp hq with ⟨a, ha, rfl⟩
    exact mem_Icc.mpr ⟨(strict_tail_index_iff (by linarith : 0 ≤ P) a).mp a.property, le_sup ha⟩
  calc
    _ = ∑ q ∈ s.image (fun q : {q : ℕ // P < (q : ℝ)} => (q : ℕ)), 1 / (q.totient : ℝ) ^ 2 :=
      (sum_image (fun _ _ _ _ h => Subtype.ext h)).symm
    _ ≤ ∑ q ∈ Icc m B, 1 / (q.totient : ℝ) ^ 2 :=
      sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ ≤ 44 / (m : ℝ) := inverse_totient_tail_finite (by dsimp [m]; omega)
    _ ≤ 44 / P := by
      have hm : P < (m : ℝ) := by
        simpa only [m, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one P
      exact div_le_div_of_nonneg_left (by norm_num) (by linarith) hm.le

theorem inverse_totient_strict_tail_summable {P : ℝ} (hP : 1 ≤ P) :
    Summable (fun q : {q : ℕ // P < (q : ℝ)} =>
      1 / ((q : ℕ).totient : ℝ) ^ 2) :=
  summable_of_sum_le (fun _ => by positivity) (inverse_totient_strict_tail_finite hP)

theorem inverse_totient_strict_tail_le {P : ℝ} (hP : 1 ≤ P) :
    (∑' q : {q : ℕ // P < (q : ℝ)}, 1 / ((q : ℕ).totient : ℝ) ^ 2) ≤ 44 / P :=
  (inverse_totient_strict_tail_summable hP).tsum_le_of_sum_le
    (inverse_totient_strict_tail_finite hP)

theorem absoluteTail_summable (N : ℕ) {P : ℝ} (hP : 1 ≤ P) :
    Summable (fun q : {q : ℕ // P < (q : ℝ)} => ‖coefficient N q‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => norm_coefficient_le N q)
    (inverse_totient_strict_tail_summable hP)

theorem absoluteTail_le (N : ℕ) {P : ℝ} (hP : 1 ≤ P) :
    absoluteTail N P ≤ 44 / P := by
  exact ((absoluteTail_summable N hP).tsum_le_tsum
    (fun q : {q : ℕ // P < (q : ℝ)} => norm_coefficient_le N q)
      (inverse_totient_strict_tail_summable hP)).trans
      (inverse_totient_strict_tail_le hP)

theorem coefficientTail_le (N : ℕ) {P : ℝ} (hP : 1 ≤ P) :
    ‖coefficientTail N P‖ ≤ 44 / P :=
  (norm_tsum_le_tsum_norm (absoluteTail_summable N hP)).trans (absoluteTail_le N hP)

end LiuWang.Proof.SingularSeries.Uniform
