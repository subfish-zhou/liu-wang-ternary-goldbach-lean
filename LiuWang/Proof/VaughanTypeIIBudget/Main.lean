import LiuWang.Proof.VaughanTypeIIBudget.Scales

/-! 真实有限二进和的无条件数值支付；没有实际核行界前提。 -/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.VaughanTypeIIBudget

open Interfaces Parameters VaughanTypeII Finset
open scoped BigOperators

theorem sqrt_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy,
    mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]

theorem sqrt_four_le {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    Real.sqrt (a + b + c + d) ≤
      Real.sqrt a + Real.sqrt b + Real.sqrt c + Real.sqrt d := by
  calc
    _ ≤ Real.sqrt (a + b + c) + Real.sqrt d := sqrt_add_le (by positivity) hd
    _ ≤ (Real.sqrt (a + b) + Real.sqrt c) + Real.sqrt d :=
      add_le_add (sqrt_add_le (by positivity) hc) le_rfl
    _ ≤ _ := add_le_add (add_le_add (sqrt_add_le ha hb) le_rfl) le_rfl

theorem sqrt_scalarRowBudget_le {N q : ℕ} {M : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) (hqU : (q : ℝ) ≤ sourceQ N)
    (hM : 0 ≤ M) :
    Real.sqrt (scalarRowBudget N M q) ≤
      (7 / 4 : ℝ) * Real.sqrt (N : ℝ) / Real.sqrt q +
      (7 / 4 : ℝ) * Real.sqrt M +
      (Real.sqrt (N : ℝ) * Real.sqrt (sourceL N)) * (1 / Real.sqrt M) +
      Real.sqrt q * Real.sqrt (sourceL N) := by
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  have hlog := VaughanTypeI.one_add_log_q_le_L hN hqL hqU
  calc
    _ ≤ Real.sqrt (3 * (N : ℝ) / q + 3 * M +
        ((N : ℝ) / M) * sourceL N + (q : ℝ) * sourceL N) := by
      apply Real.sqrt_le_sqrt
      unfold scalarRowBudget
      gcongr
    _ ≤ Real.sqrt (3 * (N : ℝ) / q) + Real.sqrt (3 * M) +
        Real.sqrt (((N : ℝ) / M) * sourceL N) +
        Real.sqrt ((q : ℝ) * sourceL N) :=
      sqrt_four_le (by positivity) (by positivity) (by positivity) (by positivity)
    _ = Real.sqrt 3 * Real.sqrt (N : ℝ) / Real.sqrt q +
        Real.sqrt 3 * Real.sqrt M +
        (Real.sqrt (N : ℝ) * Real.sqrt (sourceL N)) * (1 / Real.sqrt M) +
        Real.sqrt q * Real.sqrt (sourceL N) := by
      rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3),
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3),
        Real.sqrt_mul (by positivity), Real.sqrt_div (Nat.cast_nonneg N),
        Real.sqrt_mul (Nat.cast_nonneg q)]
      ring
    _ ≤ _ := by gcongr <;> exact sqrt_three_le

theorem sum_sqrt_scalarRowBudget_le {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) (hqU : (q : ℝ) ≤ sourceQ N) :
    (∑ j ∈ range (dyadicCount N), Real.sqrt (scalarRowBudget N (dyadicScale N j) q)) ≤
      (sourceL N / 3) * ((7 / 4 : ℝ) * Real.sqrt (N : ℝ) / Real.sqrt q) +
      (7 / 4 : ℝ) * ((7 / 2 : ℝ) * Real.sqrt ((N : ℝ) / sourceVaughanU N)) +
      (Real.sqrt (N : ℝ) * Real.sqrt (sourceL N)) *
        ((7 / 2 : ℝ) / Real.sqrt (sourceVaughanV N)) +
      (sourceL N / 3) * (Real.sqrt q * Real.sqrt (sourceL N)) := by
  have hn := exp_2000_le_of_exp_3100_le hN
  have hL := sourceL_pos hn
  have hgeom : (∑ j ∈ range (dyadicCount N), Real.sqrt (dyadicScale N j)) ≤
      (7 / 2 : ℝ) * Real.sqrt ((N : ℝ) / sourceVaughanU N) :=
    (sum_sqrt_dyadic_le hn).trans (by gcongr; exact geometric_constant_le)
  have hinv : (∑ j ∈ range (dyadicCount N), 1 / Real.sqrt (dyadicScale N j)) ≤
      (7 / 2 : ℝ) / Real.sqrt (sourceVaughanV N) :=
    (sum_inv_sqrt_dyadic_le hn).trans (by gcongr; exact geometric_constant_le)
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
    _ ≤ _ := by gcongr <;> exact dyadicCount_le_L_third hN

/-- 较强的完整有限和预算；仅有原 N、q 域假设。 -/
theorem scalarDyadicBudget_le_strong {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) (hqU : (q : ℝ) ≤ sourceQ N) :
    scalarDyadicBudget N q ≤
      0.1526 * termA N q + 2.5179 * termB N + 0.0872 * termC N q := by
  have hn := exp_2000_le_of_exp_3100_le hN
  have hL := sourceL_pos hn
  have hlog := log_Y_bounds hN
  have hk : 0 ≤ kappa := Real.sqrt_nonneg _
  have hsum := sum_sqrt_scalarRowBudget_le hN hqL hqU
  calc
    _ ≤ (0.436 : ℝ) * Real.sqrt (N : ℝ) * ((3 / 5 : ℝ) * sourceL N) *
        ((sourceL N / 3) * ((7 / 4 : ℝ) * Real.sqrt (N : ℝ) / Real.sqrt q) +
        (7 / 4 : ℝ) * ((7 / 2 : ℝ) * Real.sqrt ((N : ℝ) / sourceVaughanU N)) +
        (Real.sqrt (N : ℝ) * Real.sqrt (sourceL N)) *
          ((7 / 2 : ℝ) / Real.sqrt (sourceVaughanV N)) +
        (sourceL N / 3) * (Real.sqrt q * Real.sqrt (sourceL N))) := by
      unfold scalarDyadicBudget
      apply mul_le_mul
      · exact mul_le_mul
          (mul_le_mul_of_nonneg_right kappa_le (Real.sqrt_nonneg _)) hlog.2
          hlog.1 (by positivity)
      · exact hsum
      · positivity
      · positivity
    _ = 0.1526 * termA N q + 2.5179 * termB N + 0.0872 * termC N q := by
      rw [termA_eq_sqrt, termC_eq_sqrt hN]
      have hs := Real.sq_sqrt (Nat.cast_nonneg N)
      calc
        _ = 0.1526 * ((N : ℝ) / Real.sqrt q * sourceL N ^ (2 : ℕ)) +
            1.6023 * (Real.sqrt (N : ℝ) * sourceL N *
              Real.sqrt ((N : ℝ) / sourceVaughanU N)) +
            0.9156 * ((N : ℝ) * sourceL N * Real.sqrt (sourceL N) /
              Real.sqrt (sourceVaughanV N)) +
            0.0872 * (Real.sqrt (N : ℝ) * Real.sqrt q * sourceL N ^ (2 : ℕ) *
              Real.sqrt (sourceL N)) := by
          ring_nf
          rw [hs]
          ring
        _ = _ := by rw [sqrt_upper_identity hN, inv_sqrt_V_identity hN]; ring

/-- 请求的原预算由较强常数推出；不丢弃较强结论。 -/
theorem scalarDyadicBudget_le {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) (hqU : (q : ℝ) ≤ sourceQ N) :
    scalarDyadicBudget N q ≤
      0.2387 * termA N q + 3.1999 * termB N + 0.0889 * termC N q := by
  have ht := terms_nonneg hN q
  exact (scalarDyadicBudget_le_strong hN hqL hqU).trans (by
    apply add_le_add
    · exact add_le_add (mul_le_mul_of_nonneg_right (by norm_num) ht.1)
        (mul_le_mul_of_nonneg_right (by norm_num) ht.2.1)
    · exact mul_le_mul_of_nonneg_right (by norm_num) ht.2.2)

end LiuWang.Proof.VaughanTypeIIBudget
