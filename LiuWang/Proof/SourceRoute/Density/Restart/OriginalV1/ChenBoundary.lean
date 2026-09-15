import LiuWang.Proof.NonprincipalDensityAdvance.Family
import LiuWang.Proof.DirichletZeroCount.Applications.LowAlpha

/-!
Chen, Chinese original p.687: strict left edge, closed height, all nonprincipal
characters. This file proves the change of left edge, not Chen's density theorem.
The supplied transcription does not settle every hypothesis of that theorem.
-/

set_option autoImplicit false
noncomputable section

open Finset Set
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.NonprincipalDensityAdvance

namespace LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1

def strictNonprincipalCount (q : ℕ) [NeZero q] (alpha y : ℝ) : ℕ :=
  ∑ chi ∈ nonprincipalCharacters q,
    ∑ rho ∈ (zeroValues chi 0 y).filter (fun rho => alpha < rho.re),
      analyticOrderNatAt chi.LFunction rho

theorem mem_strict_values {q : ℕ} [NeZero q] (chi : Character q)
    {alpha y : ℝ} {rho : ℂ} :
    rho ∈ (zeroValues chi 0 y).filter (fun rho => alpha < rho.re) ↔
      chi.LFunction rho = 0 ∧ 0 < rho.re ∧ rho.re < 1 ∧
        |rho.im| ≤ y ∧ alpha < rho.re := by
  simp only [mem_filter, mem_zeroValues]
  constructor
  · rintro ⟨⟨hz, ⟨h0, h1, ht⟩, _⟩, ha⟩
    exact ⟨hz, h0, h1, ht, ha⟩
  · rintro ⟨hz, h0, h1, ht, ha⟩
    exact ⟨⟨hz, ⟨h0, h1, ht⟩, h0.le⟩, ha⟩

theorem closed_nonprincipal_le_strict (q : ℕ) [NeZero q]
    {beta alpha y : ℝ} (hba : beta < alpha) :
    nonprincipalCount q alpha y ≤ strictNonprincipalCount q beta y := by
  unfold nonprincipalCount strictNonprincipalCount count
  apply sum_le_sum
  intro chi _
  apply sum_le_sum_of_subset_of_nonneg
  · intro rho hrho
    obtain ⟨hz, ⟨h0, h1, ht⟩, ha⟩ := mem_zeroValues.mp hrho
    exact (mem_strict_values chi).mpr ⟨hz, h0, h1, ht, hba.trans_le ha⟩
  · intros
    exact Nat.zero_le _

@[simp] theorem strictNonprincipalCount_one (alpha y : ℝ) :
    strictNonprincipalCount 1 alpha y = 0 := by
  simp [strictNonprincipalCount]

@[simp] theorem strictNonprincipalCount_two (alpha y : ℝ) :
    strictNonprincipalCount 2 alpha y = 0 := by
  simp [strictNonprincipalCount]

def chenBound (q : ℕ) (alpha y : ℝ) : ℝ :=
  (250359 / Real.log ((q : ℝ) * y) + 5700) *
    ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)) ^ (1 - alpha) *
    (Real.log ((q : ℝ) * y)) ^ (6 * alpha)

theorem continuous_chenBound (q : ℕ) [NeZero q] {y : ℝ} (hy : 1 < y) :
    Continuous (fun alpha => chenBound q alpha y) := by
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hbase : 0 < (q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ) := by positivity
  have hlog : 0 < Real.log ((q : ℝ) * y) :=
    Real.log_pos (by nlinarith)
  unfold chenBound
  fun_prop (disch := positivity)

theorem closed_nonprincipal_of_strict_bounds (q : ℕ) [NeZero q]
    {alpha y : ℝ} {B : ℝ → ℝ} (ha : 1 / 2 < alpha) (ha1 : alpha < 1)
    (hB : ContinuousAt B alpha)
    (hstrict : ∀ beta ∈ Set.Ico (1 / 2) 1,
      (strictNonprincipalCount q beta y : ℝ) ≤ B beta) :
    (nonprincipalCount q alpha y : ℝ) ≤ B alpha := by
  apply le_of_forall_pos_le_add
  intro e he
  obtain ⟨d, hd, hnear⟩ := Metric.continuousAt_iff.mp hB e he
  let r := min d (alpha - 1 / 2)
  have hr : 0 < r := lt_min hd (by linarith)
  have hrd : r ≤ d := min_le_left _ _
  have hra : r ≤ alpha - 1 / 2 := min_le_right _ _
  let beta := alpha - r / 2
  have hba : beta < alpha := by dsimp [beta]; linarith
  have hb : beta ∈ Set.Ico (1 / 2) 1 := by
    constructor <;> dsimp [beta] <;> linarith
  have hdist : dist beta alpha < d := by
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hba)]
    dsimp [beta]
    linarith
  have hval := (abs_lt.mp (show |B beta - B alpha| < e from hnear hdist)).2
  exact (Nat.cast_le.mpr (closed_nonprincipal_le_strict q hba)).trans
    ((hstrict beta hb).trans (by linarith))

theorem closed_nonprincipal_of_chen (q : ℕ) [NeZero q]
    {alpha y : ℝ} (hy : 1 < y) (ha : 1 / 2 < alpha) (ha1 : alpha < 1)
    (hchen : ∀ beta ∈ Set.Ico (1 / 2) 1,
      (strictNonprincipalCount q beta y : ℝ) ≤ chenBound q beta y) :
    (nonprincipalCount q alpha y : ℝ) ≤ chenBound q alpha y :=
  closed_nonprincipal_of_strict_bounds q ha ha1
    (continuous_chenBound q hy).continuousAt hchen

end LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1
