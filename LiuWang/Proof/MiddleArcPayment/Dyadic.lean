import LiuWang.Proof.MiddleArcPayment.CountPayment

/-!
# Finite geometric height mesh

The tail is not bounded by N(T)/u once: every dyadic cell consumes its own
actual count at its upper height and its own inverse-height oscillation.
Only geometric height coverage is assumed, never a bound on S or a zero sum.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion

namespace LiuWang.Proof.MiddleArcPayment

def cellLower (U : ℝ) (j : ℕ) : ℝ := if j = 0 then 0 else 2 ^ (j - 1) * U

def cellUpper (U : ℝ) (j : ℕ) : ℝ := 2 ^ j * U

theorem dyadic_cover (U : ℝ) (k : ℕ) {y : ℝ} (hy0 : 0 ≤ y)
    (hy : y ≤ 2 ^ k * U) :
    ∃ j ∈ Finset.range (k + 1), cellLower U j ≤ y ∧ y ≤ cellUpper U j := by
  induction k with
  | zero =>
    exact ⟨0, by simp, by simpa [cellLower, cellUpper] using And.intro hy0 hy⟩
  | succ k ih =>
    by_cases h : y ≤ 2 ^ k * U
    · obtain ⟨j, hj, hjy⟩ := ih h
      exact ⟨j, Finset.mem_range.mpr (by have := Finset.mem_range.mp hj; omega), hjy⟩
    · exact ⟨k + 1, by simp, by
        simpa [cellLower, cellUpper] using And.intro (lt_of_not_ge h).le hy⟩

def sourceDyadicHeight (N : ℕ) : ℕ :=
  ⌈Real.log (sourceT N) / Real.log 2⌉₊

theorem sourceDyadicHeight_covers {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    sourceT N ≤ (2 : ℝ) ^ sourceDyadicHeight N := by
  have hlog : Real.log (sourceT N) ≤ (sourceDyadicHeight N : ℝ) * Real.log 2 :=
    (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp (Nat.le_ceil _)
  calc
    _ = Real.exp (Real.log (sourceT N)) := (Real.exp_log (sourceT_pos hN)).symm
    _ ≤ Real.exp ((sourceDyadicHeight N : ℝ) * Real.log 2) := Real.exp_le_exp.mpr hlog
    _ = _ := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

def dyadicCountBound {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ)
    (eta b U padding : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1),
    cellBound chi N eta b (cellLower U j) (cellUpper U j) padding

theorem lowerRealMass_le_dyadic {q N : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (chi : Character q) (eta b : ℝ)
    {U padding : ℝ} {k : ℕ} (hU : 0 ≤ U) (hp : 0 < padding)
    (hT : sourceT N ≤ 2 ^ k * U) :
    lowerRealMass chi N eta b ≤ dyadicCountBound chi N eta b U padding k := by
  let s := (CompleteExpansion.zeroValues chi (sourceT N)).filter (fun rho => rho.re ≤ b)
  let f := fun rho => (analyticOrderNatAt chi.LFunction rho : ℝ) * ‖Jrho N rho eta‖
  let C := fun j => cellValues chi b (cellLower U j) (cellUpper U j)
  have hf (rho : ℂ) : 0 ≤ f rho := by dsimp [f]; positivity
  have cover (rho : ℂ) (hrho : rho ∈ s) : ∃ j ∈ Finset.range (k + 1), rho ∈ C j := by
    obtain ⟨hz, hb⟩ := Finset.mem_filter.mp hrho
    have hr := CompleteExpansion.mem_zeroValues.mp hz
    obtain ⟨j, hj, hjlo, hjhi⟩ := dyadic_cover U k (abs_nonneg rho.im) (hr.2.2.2.1.trans hT)
    exact ⟨j, hj, Finset.mem_filter.mpr ⟨DirichletZeroCount.mem_zeroValues.mpr
      ⟨hr.1, ⟨hr.2.1, hr.2.2.1, hjhi⟩, hr.2.2.2.2⟩, hb, hjlo⟩⟩
  calc
    _ ≤ ∑ rho ∈ s, ∑ j ∈ Finset.range (k + 1), if rho ∈ C j then f rho else 0 := by
      apply Finset.sum_le_sum
      intro rho hrho
      obtain ⟨j, hj, hc⟩ := cover rho hrho
      have h := Finset.single_le_sum
        (s := Finset.range (k + 1))
        (f := fun j => if rho ∈ C j then f rho else 0)
        (fun j _ => by split_ifs <;> positivity) hj
      simpa only [if_pos hc] using h
    _ = ∑ j ∈ Finset.range (k + 1), ∑ rho ∈ s.filter (fun rho => rho ∈ C j), f rho := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter]
    _ ≤ ∑ j ∈ Finset.range (k + 1),
        cellMass chi N eta b (cellLower U j) (cellUpper U j) := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun rho hrho => (Finset.mem_filter.mp hrho).2) (fun rho _ _ => hf rho)
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      exact cellMass_le (nat_pos_of_exp_le hN) chi eta b (cellLower U j)
        (mul_nonneg (by positivity) hU) hp

end LiuWang.Proof.MiddleArcPayment
