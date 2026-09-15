import LiuWang.Proof.VaughanRecovery.Energy

/-! 恢复后的 kappa 消费实际行与几何和；保留二进个数和逆根尾。 -/

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.VaughanRecovery

open Interfaces Parameters VaughanTypeII VaughanTypeIIBudget Finset

def geometricRows (N q : ℕ) : ℝ :=
  (dyadicCount N : ℝ) * ((7 / 4 : ℝ) * Real.sqrt (N : ℝ) / Real.sqrt q) +
    (7 / 4 : ℝ) * ((2 + Real.sqrt 2) * Real.sqrt ((N : ℝ) / sourceVaughanU N)) +
    (Real.sqrt (N : ℝ) * Real.sqrt (sourceL N)) *
      ((2 + Real.sqrt 2) / Real.sqrt (sourceVaughanV N) -
        (2 + Real.sqrt 2) / Real.sqrt (dyadicScale N (dyadicCount N))) +
    (dyadicCount N : ℝ) * (Real.sqrt q * Real.sqrt (sourceL N))

def recoveredDyadicBudget (N q : ℕ) : ℝ :=
  recoveredKappa * Real.sqrt (N : ℝ) * Real.log ((N : ℝ) / sourceVaughanV N) *
    ∑ j ∈ range (dyadicCount N), Real.sqrt (scalarRowBudget N (dyadicScale N j) q)

theorem dyadicCount_le_three_tenths {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (dyadicCount N : ℝ) ≤ (3 / 10) * sourceL N := by
  have hn := exp_2000_le_of_exp_3100_le hN
  have hL := sourceL_ge_3100 hN
  have hlog := ArithmeticBounds.PrimeMoment.log_le_hundredth hL
  have htwo : (69 / 100 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hnum : 0 ≤ sourceL N + 3 * Real.log (sourceL N) := by
    positivity [sourceL_pos hn, Real.log_nonneg (one_le_sourceL hn)]
  have hdiv :
      (sourceL N + 3 * Real.log (sourceL N)) / (5 * Real.log 2) ≤
        (sourceL N + 3 * Real.log (sourceL N)) / (345 / 100) :=
    div_le_div_of_nonneg_left hnum (by norm_num) (by linarith)
  have hcount := dyadicCount_lt_sourceL_bound hn
  linarith

theorem sum_sqrt_rows_le_geometric {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) (hqU : (q : ℝ) ≤ sourceQ N) :
    (∑ j ∈ range (dyadicCount N), Real.sqrt (scalarRowBudget N (dyadicScale N j) q)) ≤
      geometricRows N q := by
  have hn := exp_2000_le_of_exp_3100_le hN
  have htail := sum_inv_sqrt_dyadic_add_tail hn (dyadicCount N)
  have hinv : (∑ j ∈ range (dyadicCount N), 1 / Real.sqrt (dyadicScale N j)) =
      (2 + Real.sqrt 2) / Real.sqrt (sourceVaughanV N) -
        (2 + Real.sqrt 2) / Real.sqrt (dyadicScale N (dyadicCount N)) := by linarith
  calc
    _ ≤ ∑ j ∈ range (dyadicCount N),
        ((7 / 4 : ℝ) * Real.sqrt (N : ℝ) / Real.sqrt q +
        (7 / 4 : ℝ) * Real.sqrt (dyadicScale N j) +
        (Real.sqrt (N : ℝ) * Real.sqrt (sourceL N)) * (1 / Real.sqrt (dyadicScale N j)) +
        Real.sqrt q * Real.sqrt (sourceL N)) :=
      sum_le_sum fun j _ => sqrt_scalarRowBudget_le hN hqL hqU (dyadicScale_pos hn j).le
    _ = (dyadicCount N : ℝ) * ((7 / 4 : ℝ) * Real.sqrt (N : ℝ) / Real.sqrt q) +
        (7 / 4 : ℝ) * (∑ j ∈ range (dyadicCount N), Real.sqrt (dyadicScale N j)) +
        (Real.sqrt (N : ℝ) * Real.sqrt (sourceL N)) *
          (∑ j ∈ range (dyadicCount N), 1 / Real.sqrt (dyadicScale N j)) +
        (dyadicCount N : ℝ) * (Real.sqrt q * Real.sqrt (sourceL N)) := by
      simp only [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, mul_sum]
    _ ≤ _ := by
      rw [hinv]
      unfold geometricRows
      gcongr
      exact sum_sqrt_dyadic_le hn

theorem geometricRows_le {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    geometricRows N q ≤
      ((3 / 10) * sourceL N) * ((7 / 4 : ℝ) * Real.sqrt (N : ℝ) / Real.sqrt q) +
      (7 / 4 : ℝ) * ((7 / 2 : ℝ) * Real.sqrt ((N : ℝ) / sourceVaughanU N)) +
      (Real.sqrt (N : ℝ) * Real.sqrt (sourceL N)) *
        ((7 / 2 : ℝ) / Real.sqrt (sourceVaughanV N)) +
      ((3 / 10) * sourceL N) * (Real.sqrt q * Real.sqrt (sourceL N)) := by
  have hinv :
      (2 + Real.sqrt 2) / Real.sqrt (sourceVaughanV N) -
        (2 + Real.sqrt 2) / Real.sqrt (dyadicScale N (dyadicCount N)) ≤
          (7 / 2 : ℝ) / Real.sqrt (sourceVaughanV N) := by
    apply (sub_le_self _ (by positivity)).trans
    gcongr
    exact geometric_constant_le
  unfold geometricRows
  gcongr
  · exact dyadicCount_le_three_tenths hN
  · exact geometric_constant_le
  · exact dyadicCount_le_three_tenths hN

theorem sourceS4_le_recoveredDyadicBudget {N a q : ℕ} {α θ : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hqL : sourceP1 N ≤ (q : ℝ))
    (hi : sourceIndex a q) (hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2) :
    ‖VaughanTypeI.sourceS4 N α‖ ≤ recoveredDyadicBudget N q := by
  apply (sourceS4_le_recoveredKappa hN α).trans
  unfold recoveredDyadicBudget
  have hlog := (log_Y_bounds hN).1
  apply mul_le_mul_of_nonneg_left _ (by unfold recoveredKappa; positivity)
  exact sum_le_sum fun j hj => Real.sqrt_le_sqrt
    (VaughanEstimate.dyadic_rowMax_le_scalarRowBudget hN hqL hi hθ hα j (mem_range.mp hj))

theorem recoveredDyadicBudget_le_geometric {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) (hqU : (q : ℝ) ≤ sourceQ N) :
    recoveredDyadicBudget N q ≤
      recoveredKappa * Real.sqrt (N : ℝ) * Real.log ((N : ℝ) / sourceVaughanV N) *
        geometricRows N q := by
  have hlog := (log_Y_bounds hN).1
  exact mul_le_mul_of_nonneg_left (sum_sqrt_rows_le_geometric hN hqL hqU)
    (by unfold recoveredKappa; positivity)

theorem recoveredDyadicBudget_le_three_terms {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) (hqU : (q : ℝ) ≤ sourceQ N) :
    recoveredDyadicBudget N q ≤
      0.1328355 * termA N q + 2.4353175 * termB N + 0.075906 * termC N q := by
  have hn := exp_2000_le_of_exp_3100_le hN
  have hL := sourceL_pos hn
  have hlog := log_Y_bounds hN
  have hsum := (sum_sqrt_rows_le_geometric hN hqL hqU).trans (geometricRows_le hN)
  calc
    _ ≤ (0.4217 : ℝ) * Real.sqrt (N : ℝ) * ((3 / 5 : ℝ) * sourceL N) *
        (((3 / 10) * sourceL N) * ((7 / 4 : ℝ) * Real.sqrt (N : ℝ) / Real.sqrt q) +
        (7 / 4 : ℝ) * ((7 / 2 : ℝ) * Real.sqrt ((N : ℝ) / sourceVaughanU N)) +
        (Real.sqrt (N : ℝ) * Real.sqrt (sourceL N)) *
          ((7 / 2 : ℝ) / Real.sqrt (sourceVaughanV N)) +
        ((3 / 10) * sourceL N) * (Real.sqrt q * Real.sqrt (sourceL N))) := by
      unfold recoveredDyadicBudget
      apply mul_le_mul
      · exact mul_le_mul
          (mul_le_mul_of_nonneg_right recoveredKappa_le (Real.sqrt_nonneg _)) hlog.2
          hlog.1 (by positivity)
      · exact hsum
      · positivity
      · positivity
    _ = _ := by
      rw [termA_eq_sqrt, termC_eq_sqrt hN]
      have hs := Real.sq_sqrt (Nat.cast_nonneg N)
      calc
        _ = 0.1328355 * ((N : ℝ) / Real.sqrt q * sourceL N ^ (2 : ℕ)) +
            1.5497475 * (Real.sqrt (N : ℝ) * sourceL N *
              Real.sqrt ((N : ℝ) / sourceVaughanU N)) +
            0.88557 * ((N : ℝ) * sourceL N * Real.sqrt (sourceL N) /
              Real.sqrt (sourceVaughanV N)) +
            0.075906 * (Real.sqrt (N : ℝ) * Real.sqrt q * sourceL N ^ (2 : ℕ) *
              Real.sqrt (sourceL N)) := by
          ring_nf
          rw [hs]
          ring
        _ = _ := by rw [sqrt_upper_identity hN, inv_sqrt_V_identity hN]; ring

end LiuWang.Proof.VaughanRecovery
