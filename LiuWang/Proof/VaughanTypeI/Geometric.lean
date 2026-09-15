import AnalyticNumberTheory.LargeSieve.WellSpaced

/-!
# 闭区间几何和与反向 Abel 界

共振时截断核取完整长度，不使用实数除零的值。
单调非负权重使用同一区间的末段和，只支付一次最高权重。
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.VaughanTypeI

open Finset AnalyticNumberTheory.LargeSieve

def truncatedKernel (Y x : ℝ) : ℝ :=
  if distToInt x = 0 then Y else min Y (1 / (2 * distToInt x))

theorem truncatedKernel_nonneg {Y : ℝ} (hY : 0 ≤ Y) (x : ℝ) :
    0 ≤ truncatedKernel Y x := by
  unfold truncatedKernel
  split_ifs
  · exact hY
  · exact le_min hY (div_nonneg (by norm_num)
      (mul_nonneg (by norm_num) (distToInt_nonneg x)))

theorem truncatedKernel_mono {Y Z : ℝ} (hYZ : Y ≤ Z) (x : ℝ) :
    truncatedKernel Y x ≤ truncatedKernel Z x := by
  unfold truncatedKernel
  split_ifs
  · exact hYZ
  · exact min_le_min_right _ hYZ

@[simp] theorem truncatedKernel_int (Y : ℝ) (k : ℤ) :
    truncatedKernel Y (k : ℝ) = Y := by
  have hk := (distToInt_eq_zero_iff (k : ℝ)).mpr ⟨k, rfl⟩
  simp [truncatedKernel, hk]

theorem norm_charReal_eq_one (x : ℝ) : ‖charReal x‖ = 1 := by
  unfold charReal
  simpa using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)

theorem sum_charReal_Icc_eq (a b : ℕ) (x : ℝ) :
    (∑ n ∈ Icc a b, charReal ((n : ℝ) * x)) =
      charRealSubIcc ((a : ℤ) - 1) (b + 1 - a) x := by
  unfold charRealSubIcc
  by_cases hab : a ≤ b
  · apply Finset.sum_bij (i := fun (n : ℕ) _ => (n : ℤ))
    · intro n hn
      simp only [mem_Icc] at hn ⊢
      omega
    · intro n _ m _ h
      exact_mod_cast h
    · intro z hz
      simp only [mem_Icc] at hz
      refine ⟨z.toNat, ?_, ?_⟩
      · simp only [mem_Icc]
        omega
      · omega
    · intro n _
      simp
  · have hba : b + 1 - a = 0 := by omega
    simp [Icc_eq_empty_of_lt (Nat.lt_of_not_ge hab), hba]

theorem norm_sum_charReal_Icc_le (a b : ℕ) (x : ℝ) :
    ‖∑ n ∈ Icc a b, charReal ((n : ℝ) * x)‖ ≤
      truncatedKernel (b + 1 - a : ℕ) x := by
  rw [sum_charReal_Icc_eq]
  unfold truncatedKernel
  split_ifs with hx
  · exact geomSum_exp_bound_Icc_trivial _ _ _
  · exact le_min (geomSum_exp_bound_Icc_trivial _ _ _)
      (geomSum_exp_bound_Icc_far _ _ (by
        rwa [← distToInt_eq_zero_iff]))

theorem sum_weighted_Icc_reverse (w : ℕ → ℝ) (f : ℕ → ℂ)
    {a b : ℕ} (hab : a ≤ b) :
    (∑ n ∈ Icc a b, (w n : ℂ) * f n) =
      (w a : ℂ) * (∑ n ∈ Icc a b, f n) +
        ∑ k ∈ Ico a b, ((w (k + 1) - w k : ℝ) : ℂ) *
          (∑ n ∈ Icc (k + 1) b, f n) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
      rw [sum_Icc_succ_top (Nat.le_succ_of_le hab), ih,
        sum_Icc_succ_top (Nat.le_succ_of_le hab),
        sum_Ico_succ_top hab]
      simp only [Icc_self, sum_singleton]
      have htail :
          (∑ k ∈ Ico a b, ((w (k + 1) - w k : ℝ) : ℂ) *
            (∑ n ∈ Icc (k + 1) (b + 1), f n)) =
          (∑ k ∈ Ico a b, ((w (k + 1) - w k : ℝ) : ℂ) *
            (∑ n ∈ Icc (k + 1) b, f n)) +
          ((w b - w a : ℝ) : ℂ) * f (b + 1) := by
        calc
          _ = ∑ k ∈ Ico a b,
              (((w (k + 1) - w k : ℝ) : ℂ) *
                (∑ n ∈ Icc (k + 1) b, f n) +
              ((w (k + 1) - w k : ℝ) : ℂ) * f (b + 1)) := by
            apply sum_congr rfl
            intro k hk
            rw [sum_Icc_succ_top (by have := (mem_Ico.mp hk).2; omega), mul_add]
          _ = _ := by
            rw [sum_add_distrib, ← sum_mul, ← Complex.ofReal_sum,
              sum_Ico_sub (f := w) hab]
      rw [htail]
      push_cast
      ring

theorem norm_sum_weighted_Icc_le (w : ℕ → ℝ) (f : ℕ → ℂ)
    {a b : ℕ} {B : ℝ} (hab : a ≤ b)
    (hwa : 0 ≤ w a) (hw : MonotoneOn w (Set.Icc a b))
    (hB : ∀ k ∈ Icc a b, ‖∑ n ∈ Icc k b, f n‖ ≤ B) :
    ‖∑ n ∈ Icc a b, (w n : ℂ) * f n‖ ≤ w b * B := by
  have hdiff (k : ℕ) (hk : k ∈ Ico a b) : 0 ≤ w (k + 1) - w k := by
    have hk' := mem_Ico.mp hk
    exact sub_nonneg.mpr (hw ⟨hk'.1, hk'.2.le⟩
      ⟨by omega, by omega⟩ (by omega))
  rw [sum_weighted_Icc_reverse w f hab]
  calc
    _ ≤ ‖(w a : ℂ) * (∑ n ∈ Icc a b, f n)‖ +
        ∑ k ∈ Ico a b, ‖((w (k + 1) - w k : ℝ) : ℂ) *
          (∑ n ∈ Icc (k + 1) b, f n)‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    _ ≤ w a * B + ∑ k ∈ Ico a b, (w (k + 1) - w k) * B := by
      apply add_le_add
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwa]
        exact mul_le_mul_of_nonneg_left (hB a (mem_Icc.mpr ⟨le_rfl, hab⟩)) hwa
      · apply sum_le_sum
        intro k hk
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hdiff k hk)]
        exact mul_le_mul_of_nonneg_left
          (hB (k + 1) (mem_Icc.mpr (by have := mem_Ico.mp hk; omega))) (hdiff k hk)
    _ = w b * B := by
      rw [← sum_mul, sum_Ico_sub (f := w) hab]
      ring

theorem norm_sum_log_charReal_Icc_le {a b : ℕ} (ha : 1 ≤ a) (x : ℝ) :
    ‖∑ n ∈ Icc a b, (Real.log n : ℂ) * charReal ((n : ℝ) * x)‖ ≤
      Real.log b * truncatedKernel (b : ℝ) x := by
  by_cases hab : a ≤ b
  · apply norm_sum_weighted_Icc_le (fun n => Real.log n) _ hab
    · exact Real.log_nonneg (by exact_mod_cast ha)
    · intro i hi j _ hij
      exact Real.log_le_log (by exact_mod_cast ha.trans hi.1) (by exact_mod_cast hij)
    · intro k hk
      exact (norm_sum_charReal_Icc_le k b x).trans
        (truncatedKernel_mono (by
          have hk1 : 1 ≤ k := ha.trans (mem_Icc.mp hk).1
          exact_mod_cast (show b + 1 - k ≤ b by omega)) x)
  · rw [Icc_eq_empty_of_lt (Nat.lt_of_not_ge hab), sum_empty, norm_zero]
    apply mul_nonneg
    · exact Real.log_natCast_nonneg b
    · exact truncatedKernel_nonneg (Nat.cast_nonneg b) x

end LiuWang.Proof.VaughanTypeI
