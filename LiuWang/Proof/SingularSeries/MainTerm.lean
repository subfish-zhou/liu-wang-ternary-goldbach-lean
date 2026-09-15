import LiuWang.Proof.SingularSeries.Euler
import LiuWang.Proof.SingularSeries.JBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Finite source I11 and its explicitly unpaid arithmetic errors

The denominator cutoff is the real cutoff `q ≤ P`, and the omitted
coefficient tail is literally `q > P`. The integral radius is the original
`deltaRadius N q`. These theorems consume the accepted full-line J-cube
integral and prove the source weighted version of (4.4).

The final lower bound retains the actual coefficient tail and weighted
totient sum. It does not assert (4.8) or completion of the other major-arc
terms.
-/

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory
open scoped Interval
open AnalyticNumberTheory.LargeSieve LiuWang.Proof.Interfaces
open LiuWang.Proof.Parameters

namespace LiuWang.Proof.SingularSeries

def denominators (P : ℝ) : Finset ℕ := Icc 1 ⌊P⌋₊

theorem mem_denominators {P : ℝ} (hP : 0 ≤ P) (q : ℕ) :
    q ∈ denominators P ↔ 1 ≤ q ∧ (q : ℝ) ≤ P := by
  simp only [denominators, mem_Icc, Nat.le_floor_iff hP]

def partialSeries (N : ℕ) (P : ℝ) : ℝ :=
  ∑ q ∈ denominators P, realCoefficient N q

def coefficientTail (N : ℕ) (P : ℝ) : ℂ :=
  ∑' q : {q : ℕ // P < (q : ℝ)}, coefficient N q

def absoluteTail (N : ℕ) (P : ℝ) : ℝ :=
  ∑' q : {q : ℕ // P < (q : ℝ)}, ‖coefficient N q‖

theorem coefficientTail_norm_le {N : ℕ} (hN : 0 < N) (P : ℝ) :
    ‖coefficientTail N P‖ ≤ absoluteTail N P :=
  norm_tsum_le_tsum_norm ((coefficient_norm_summable hN).subtype _)

set_option backward.isDefEq.respectTransparency false in
theorem partialSeries_add_tail {N : ℕ} (hN : 0 < N) {P : ℝ} (hP : 0 ≤ P) :
    (partialSeries N P : ℂ) + coefficientTail N P = (series N : ℂ) := by
  classical
  have h := (coefficient_summable hN).sum_add_tsum_subtype_compl (range (⌊P⌋₊ + 1))
  have hs : (partialSeries N P : ℂ) =
      ∑ q ∈ range (⌊P⌋₊ + 1), coefficient N q := by
    have he : Icc 1 ⌊P⌋₊ = Ico 1 (⌊P⌋₊ + 1) := by ext q; simp
    simp only [partialSeries, denominators, he,
      sum_Ico_eq_sub _ (by omega : 1 ≤ ⌊P⌋₊ + 1), sum_range_one, realCoefficient_zero, sub_zero]
    push_cast
    simp only [ofReal_realCoefficient]
  have ht : (∑' q : {q : ℕ // q ∉ range (⌊P⌋₊ + 1)}, coefficient N q) =
      coefficientTail N P := by
    change (∑' q : {q : ℕ // q ∉ range (⌊P⌋₊ + 1)}, coefficient N q) =
      ∑' q : {q : ℕ // P < (q : ℝ)}, coefficient N q
    have he (q : ℕ) : q ∉ range (⌊P⌋₊ + 1) ↔ P < (q : ℝ) := by
      simp only [mem_range, not_lt, Nat.succ_le_iff, Nat.floor_lt hP]
    exact (Equiv.subtypeEquivRight he).tsum_eq (fun q => coefficient N q)
  rw [← hs, ht, ← ofReal_series] at h
  exact h

theorem partialSeries_error_le {N : ℕ} (hN : 0 < N) {P : ℝ} (hP : 0 ≤ P) :
    |series N - partialSeries N P| ≤ absoluteTail N P := by
  have he : ((series N - partialSeries N P : ℝ) : ℂ) = coefficientTail N P := by
    push_cast
    exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using (partialSeries_add_tail hN hP).symm)
  simpa only [← he, Complex.norm_real, Real.norm_eq_abs] using coefficientTail_norm_le hN P

def I11 (N : ℕ) : ℂ :=
  ∑ q ∈ denominators (sourceP N), coefficient N q *
    ∫ eta in -deltaRadius N q..deltaRadius N q, cubeIntegrand N eta

theorem I11_source {N : ℕ} :
    I11 N =
      ∑ q ∈ denominators (sourceP N),
        (ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) ^ 3 *
          (∑ a ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
            charReal (-(a : ℝ) * (N : ℝ) / (q : ℝ))) *
          ∫ eta in -deltaRadius N q..deltaRadius N q,
            J N eta ^ 3 * charReal (-(N : ℝ) * eta) := by
  apply sum_congr rfl
  intro q hq
  rw [coefficient_source (Nat.zero_lt_of_lt (mem_Icc.mp hq).1)]
  rfl

def fullMass (N : ℕ) : ℝ := (N : ℝ) ^ 2 * ((0.997 : ℝ) ^ 2 / 2)

theorem fullMass_nonneg (N : ℕ) : 0 ≤ fullMass N := by unfold fullMass; positivity

theorem integral_cube_eq_fullMass {N : ℕ} (hN : 0 < N) :
    (∫ eta : ℝ, cubeIntegrand N eta) = (fullMass N : ℂ) := by
  change (∫ eta : ℝ, J N eta ^ 3 * charReal (-(N : ℝ) * eta)) = _
  rw [LiuWang.Proof.SingularIntegral.integral_J_cube hN]
  simp [fullMass]

def arcError (N : ℕ) : ℂ :=
  ∑ q ∈ denominators (sourceP N), coefficient N q *
    ((∫ eta : ℝ, cubeIntegrand N eta) -
      ∫ eta in -deltaRadius N q..deltaRadius N q, cubeIntegrand N eta)

theorem I11_eq_partial_main_sub_arcError {N : ℕ} (hN : 0 < N) :
    I11 N = (fullMass N : ℂ) * (partialSeries N (sourceP N) : ℂ) - arcError N := by
  simp only [I11, arcError, integral_cube_eq_fullMass hN, partialSeries,
    Complex.ofReal_sum, ofReal_realCoefficient, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intros
  ring

theorem norm_coefficient_le_moebius (N q : ℕ) :
    ‖coefficient N q‖ ≤
      |(ArithmeticFunction.moebius q : ℝ)| / (q.totient : ℝ) ^ 2 := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  have hφ : 0 < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq)
  rw [coefficient, if_neg hq, norm_mul, norm_div, norm_pow, Complex.norm_natCast,
    Complex.norm_intCast]
  calc
    _ ≤ (|(ArithmeticFunction.moebius q : ℝ)| / (q.totient : ℝ) ^ 3) *
        (q.totient : ℝ) :=
      mul_le_mul_of_nonneg_left (norm_ramanujan_le_totient N q) (by positivity)
    _ = _ := by field_simp

def weightedTotientSum (P : ℝ) : ℝ :=
  ∑ q ∈ denominators P,
    |(ArithmeticFunction.moebius q : ℝ)| * (q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2

theorem weightedTotientSum_nonneg (P : ℝ) : 0 ≤ weightedTotientSum P := by
  apply sum_nonneg
  intros
  positivity

theorem delta_tail_identity {N q : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : 0 < q) :
    1 / (Real.pi ^ 3 * deltaRadius N q ^ 2) =
      (100 / (Real.pi * (3.36 : ℝ) ^ 2)) *
        ((N : ℝ) ^ 2 / sourceP N ^ 2) * (q : ℝ) ^ 2 := by
  have hP := sourceP_pos (exp_2000_le_of_exp_3100_le hN)
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (nat_pos_of_exp_le hN).ne'
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  unfold deltaRadius
  field_simp
  ring

theorem source_arc_constant_le : 100 / (Real.pi * (3.36 : ℝ) ^ 2) ≤ 2.82 := by
  rw [div_le_iff₀ (by positivity)]
  have h := Real.pi_gt_d20
  norm_num at h ⊢
  nlinarith

theorem arcError_bound {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    ‖arcError N‖ ≤
      2.82 * (N : ℝ) ^ 2 / sourceP N ^ 2 * weightedTotientSum (sourceP N) := by
  have hN0 := nat_pos_of_exp_le hN
  have hP := sourceP_pos (exp_2000_le_of_exp_3100_le hN)
  calc
    _ ≤ ∑ q ∈ denominators (sourceP N),
        ‖coefficient N q *
          ((∫ eta : ℝ, cubeIntegrand N eta) -
            ∫ eta in -deltaRadius N q..deltaRadius N q, cubeIntegrand N eta)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ q ∈ denominators (sourceP N),
        (|(ArithmeticFunction.moebius q : ℝ)| / (q.totient : ℝ) ^ 2) *
          (1 / (Real.pi ^ 3 * deltaRadius N q ^ 2)) := by
      apply sum_le_sum
      intro q hq
      have hq0 : 0 < q := (mem_Icc.mp hq).1
      rw [norm_mul]
      exact mul_le_mul (norm_coefficient_le_moebius N q)
        (cube_integral_tail_bound hN0
          (deltaRadius_pos (exp_2000_le_of_exp_3100_le hN) hq0))
        (norm_nonneg _) (by positivity)
    _ = (100 / (Real.pi * (3.36 : ℝ) ^ 2)) *
        ((N : ℝ) ^ 2 / sourceP N ^ 2) * weightedTotientSum (sourceP N) := by
      simp only [weightedTotientSum, mul_sum]
      apply sum_congr rfl
      intro q hq
      rw [delta_tail_identity hN (mem_Icc.mp hq).1]
      ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right source_arc_constant_le
        (mul_nonneg (by positivity : 0 ≤ (N : ℝ) ^ 2 / sourceP N ^ 2)
          (weightedTotientSum_nonneg (sourceP N)))
      calc
        _ = (100 / (Real.pi * (3.36 : ℝ) ^ 2)) *
            (((N : ℝ) ^ 2 / sourceP N ^ 2) * weightedTotientSum (sourceP N)) := by ring
        _ ≤ _ := h
        _ = _ := by ring

theorem I11_eq_series_main_sub_errors {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    I11 N = (fullMass N : ℂ) * (series N : ℂ) -
      (fullMass N : ℂ) * coefficientTail N (sourceP N) - arcError N := by
  have ht := partialSeries_add_tail (nat_pos_of_exp_le hN)
    (sourceP_pos (exp_2000_le_of_exp_3100_le hN)).le
  rw [I11_eq_partial_main_sub_arcError (nat_pos_of_exp_le hN), ← ht]
  ring

theorem re_I11_lower_bound {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    fullMass N * series N -
      fullMass N * absoluteTail N (sourceP N) -
      2.82 * (N : ℝ) ^ 2 / sourceP N ^ 2 * weightedTotientSum (sourceP N) ≤
        (I11 N).re := by
  rw [I11_eq_series_main_sub_errors hN]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  have ht := (Complex.re_le_norm (coefficientTail N (sourceP N))).trans
    (coefficientTail_norm_le (nat_pos_of_exp_le hN) (sourceP N))
  have he := (Complex.re_le_norm (arcError N)).trans (arcError_bound hN)
  have hm := mul_le_mul_of_nonneg_left ht (fullMass_nonneg N)
  linarith

end LiuWang.Proof.SingularSeries
