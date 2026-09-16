import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.UnitShiftFiniteBudget

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

open LiuWang.Proof.Campaign20260915.ZetaWinding

def logGridUpper (a h : ℝ) (n : ℕ) : ℝ :=
  h * ∑ k ∈ Finset.range n, realLogZeta (a + k * h)

def logGridLower (a h : ℝ) (n : ℕ) : ℝ :=
  h * ∑ k ∈ Finset.range n, realLogZeta (a + (k + 1 : ℕ) * h)

theorem logGrid_integral_bounds {a h : ℝ} (ha : 1 < a) (hh : 0 ≤ h) (n : ℕ) :
    logGridLower a h n ≤ (∫ x in a..(a + n * h), realLogZeta x) ∧
      (∫ x in a..(a + n * h), realLogZeta x) ≤ logGridUpper a h n := by
  have hp (k : ℕ) : 1 < a + k * h :=
    lt_of_lt_of_le ha (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg k) hh))
  have he := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => a + k * h) (n := n)
    (fun k _ => realLogZeta_intervalIntegrable (hp k) (hp (k + 1)))
  simp only [Nat.cast_zero, zero_mul, add_zero] at he
  have hb (k : ℕ) :
      h * realLogZeta (a + (k + 1 : ℕ) * h) ≤
          (∫ x in (a + k * h)..(a + (k + 1 : ℕ) * h), realLogZeta x) ∧
        (∫ x in (a + k * h)..(a + (k + 1 : ℕ) * h), realLogZeta x) ≤
          h * realLogZeta (a + k * h) := by
    have hstep : a + k * h ≤ a + (k + 1 : ℕ) * h := by
      push_cast
      nlinarith
    have hd : a + (k + 1 : ℕ) * h - (a + k * h) = h := by push_cast; ring
    simpa only [hd] using realLogZeta_integral_bounds (hp k) hstep
  rw [← he]
  constructor
  · unfold logGridLower
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => (hb k).1
  · unfold logGridUpper
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => (hb k).2

theorem logGrid_gap (a h : ℝ) (n : ℕ) :
    logGridUpper a h n - logGridLower a h n =
      h * (realLogZeta a - realLogZeta (a + n * h)) := by
  have hs :
      ∑ k ∈ Finset.range n, (realLogZeta (a + k * h) -
        realLogZeta (a + (k + 1 : ℕ) * h)) =
      realLogZeta a - realLogZeta (a + n * h) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  unfold logGridUpper logGridLower
  rw [← mul_sub, ← Finset.sum_sub_distrib, hs]

theorem logGrid_integral_error {a h : ℝ} (ha : 1 < a) (hh : 0 ≤ h) (n : ℕ) :
    0 ≤ logGridUpper a h n - (∫ x in a..(a + n * h), realLogZeta x) ∧
      logGridUpper a h n - (∫ x in a..(a + n * h), realLogZeta x) ≤
        h * (realLogZeta a - realLogZeta (a + n * h)) := by
  have hb := logGrid_integral_bounds ha hh n
  have he := logGrid_gap a h n
  constructor <;> linarith

theorem unitShiftRealBudget_disjoint :
    unitShiftRealBudget =
      -2 * (∫ x in (3 / 2 : ℝ)..(5 / 2), realLogZeta x) -
        (∫ x in (5 / 2 : ℝ)..3, realLogZeta x) - realLogTail 5 / 2 := by
  have h1 := realLogTail_split (by norm_num : (1 : ℝ) < 3 / 2)
    (by norm_num : (1 : ℝ) < 5 / 2)
  have h2 := realLogTail_split (by norm_num : (1 : ℝ) < 5 / 2)
    (by norm_num : (1 : ℝ) < 3)
  have h3 := realLogTail_split (by norm_num : (1 : ℝ) < 3)
    (by norm_num : (1 : ℝ) < 5)
  unfold unitShiftRealBudget
  linarith

def unitShiftGridCost (m : ℕ) : ℝ :=
  2 * logGridUpper (3 / 2) (1 / (2 * m)) (2 * m) +
    logGridUpper (5 / 2) (1 / (2 * m)) m +
    logGridUpper 5 (1 / (2 * m)) (22 * m) / 2

theorem unitShiftRealBudget_grid_lower {m : ℕ} (hm : 0 < m) :
    -unitShiftGridCost m - 1 / 6000 ≤ unitShiftRealBudget := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hh : 0 ≤ (1 : ℝ) / (2 * m) := by positivity
  have h1 := (logGrid_integral_bounds (by norm_num : (1 : ℝ) < 3 / 2) hh (2 * m)).2
  have h2 := (logGrid_integral_bounds (by norm_num : (1 : ℝ) < 5 / 2) hh m).2
  have h3 := (logGrid_integral_bounds (by norm_num : (1 : ℝ) < 5) hh (22 * m)).2
  have e1 : (3 / 2 : ℝ) + (2 * m : ℕ) * (1 / (2 * m)) = 5 / 2 := by
    push_cast
    field_simp
    norm_num
  have e2 : (5 / 2 : ℝ) + m * (1 / (2 * m)) = 3 := by field_simp; ring
  have e3 : (5 : ℝ) + (22 * m : ℕ) * (1 / (2 * m)) = 16 := by
    push_cast
    field_simp
    ring
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  rw [unitShiftRealBudget_disjoint,
    realLogTail_split (by norm_num : (1 : ℝ) < 5) (by norm_num : (1 : ℝ) < 16)]
  unfold unitShiftGridCost
  linarith [realLogTail_sixteen_budget.2]

theorem horizontalLogMass_grid_lower {T : ℝ} (hT : T ≠ 0) {m : ℕ} (hm : 0 < m) :
    (∫ x in (1 / 2 : ℝ)..(3 / 2),
      Real.log ‖riemannZeta (horizontalAt T x) /
        riemannZeta (horizontalAt T (x + 1))‖) -
      unitShiftGridCost m - 1 / 6000 ≤ horizontalLogMass T := by
  linarith [horizontalLogMass_unitShift_lower hT, unitShiftRealBudget_grid_lower hm]

theorem horizontalLogMass_grid_upper {T : ℝ} (hT : T ≠ 0) {m : ℕ} (hm : 0 < m) :
    horizontalLogMass T ≤
      (∫ x in (1 / 2 : ℝ)..(5 / 4), Real.log ‖riemannZeta (horizontalAt T x)‖) +
        logGridUpper (5 / 4) (1 / (4 * m)) (59 * m) + 1 / 3000 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have h := (logGrid_integral_bounds (by norm_num : (1 : ℝ) < 5 / 4)
    (by positivity : 0 ≤ (1 : ℝ) / (4 * m)) (59 * m)).2
  have he : (5 / 4 : ℝ) + (59 * m : ℕ) * (1 / (4 * m)) = 16 := by
    push_cast
    field_simp
    ring
  rw [he] at h
  linarith [horizontalLogMass_finite_tail_upper hT (by norm_num : (1 : ℝ) < 5 / 4)]

#print axioms logGrid_integral_error
#print axioms unitShiftRealBudget_disjoint
#print axioms horizontalLogMass_grid_lower
#print axioms horizontalLogMass_grid_upper

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
