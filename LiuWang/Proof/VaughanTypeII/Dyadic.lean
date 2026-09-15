import LiuWang.Proof.VaughanTypeII.Energy

/-! 对数长度的有限二进分解；所有超过 N/U 的尾项逐项为零。 -/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.VaughanTypeII

open Finset Interfaces Parameters ArithmeticBounds
open AnalyticNumberTheory.LargeSieve
open scoped BigOperators

def dyadicCount (N : ℕ) : ℕ :=
  ⌈Real.log ((N : ℝ) / (sourceVaughanU N * sourceVaughanV N)) / Real.log 2⌉₊

def dyadicScale (N j : ℕ) : ℝ := (2 : ℝ) ^ j * sourceVaughanV N

def effectiveSupport (N : ℕ) : Finset ℕ :=
  Ioc ⌊sourceVaughanV N⌋₊ ⌊(N : ℝ) / sourceVaughanU N⌋₊

theorem dyadicScale_zero (N : ℕ) : dyadicScale N 0 = sourceVaughanV N := by
  simp [dyadicScale]

theorem dyadicScale_succ (N j : ℕ) : dyadicScale N (j + 1) = 2 * dyadicScale N j := by
  simp only [dyadicScale, pow_succ]
  ring

theorem dyadicScale_pos {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) (j : ℕ) :
    0 < dyadicScale N j := mul_pos (by positivity) (sourceVaughanV_pos hN)

theorem dyadicScale_mono {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    Monotone (dyadicScale N) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hij)
    (sourceVaughanV_pos hN).le

theorem V_le_dyadicScale {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) (j : ℕ) :
    sourceVaughanV N ≤ dyadicScale N j := by
  simpa only [dyadicScale_zero] using dyadicScale_mono hN (Nat.zero_le j)

theorem dyadic_ratio_gt_one {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    1 < (N : ℝ) / (sourceVaughanU N * sourceVaughanV N) := by
  exact (one_lt_div (mul_pos (sourceVaughanU_pos hN) (sourceVaughanV_pos hN))).mpr
    (sourceVaughanUV_lt_natCast hN)

theorem dyadicCount_pos {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    0 < dyadicCount N := by
  apply Nat.ceil_pos.mpr
  exact div_pos (Real.log_pos (dyadic_ratio_gt_one hN)) (Real.log_pos (by norm_num))

theorem dyadicCount_lt_log_bound {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    (dyadicCount N : ℝ) <
      1 + Real.log ((N : ℝ) / (sourceVaughanU N * sourceVaughanV N)) / Real.log 2 := by
  simpa only [dyadicCount, add_comm] using Nat.ceil_lt_add_one
    (div_nonneg (Real.log_nonneg (dyadic_ratio_gt_one hN).le)
      (Real.log_pos (by norm_num)).le)

theorem dyadicScale_lt_upper {N j : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hj : j < dyadicCount N) :
    dyadicScale N j < (N : ℝ) / sourceVaughanU N := by
  have hU := sourceVaughanU_pos hN
  have hV := sourceVaughanV_pos hN
  have hlog := (lt_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp
    (Nat.lt_ceil.mp hj)
  have hp : (2 : ℝ) ^ j < (N : ℝ) / (sourceVaughanU N * sourceVaughanV N) := by
    apply (Real.log_lt_log_iff (by positivity) ((zero_lt_one.trans (dyadic_ratio_gt_one hN)))).mp
    simpa only [Real.log_pow] using hlog
  have hm := mul_lt_mul_of_pos_right hp hV
  have he : (N : ℝ) / (sourceVaughanU N * sourceVaughanV N) * sourceVaughanV N =
      (N : ℝ) / sourceVaughanU N := by field_simp
  rwa [he] at hm

theorem upper_le_dyadicScale_count {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) :
    (N : ℝ) / sourceVaughanU N ≤ dyadicScale N (dyadicCount N) := by
  have hU := sourceVaughanU_pos hN
  have hV := sourceVaughanV_pos hN
  have hlog := (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp
    (Nat.le_ceil (Real.log ((N : ℝ) / (sourceVaughanU N * sourceVaughanV N)) / Real.log 2))
  have hp : (N : ℝ) / (sourceVaughanU N * sourceVaughanV N) ≤
      (2 : ℝ) ^ dyadicCount N := by
    apply (Real.log_le_log_iff (zero_lt_one.trans (dyadic_ratio_gt_one hN)) (by positivity)).mp
    simpa only [Real.log_pow, dyadicCount] using hlog
  have hm := mul_le_mul_of_nonneg_right hp hV.le
  have he : (N : ℝ) / (sourceVaughanU N * sourceVaughanV N) * sourceVaughanV N =
      (N : ℝ) / sourceVaughanU N := by field_simp
  rwa [he] at hm

theorem dyadic_blocks_disjoint {N i j : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hij : i < j) :
    Disjoint (blockSupport (dyadicScale N i)) (blockSupport (dyadicScale N j)) := by
  apply disjoint_left.mpr
  intro t hi hj
  have hti := ((mem_blockSupport (dyadicScale_pos hN i).le t).mp hi).2
  have htj := ((mem_blockSupport (dyadicScale_pos hN j).le t).mp hj).1
  have hm := dyadicScale_mono hN (show i + 1 ≤ j by omega)
  rw [dyadicScale_succ] at hm
  linarith

theorem exists_mem_dyadic_block {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (k t : ℕ)
    (htV : sourceVaughanV N < (t : ℝ)) (htk : (t : ℝ) ≤ dyadicScale N k) :
    ∃ j < k, t ∈ blockSupport (dyadicScale N j) := by
  induction k with
  | zero => simp only [dyadicScale_zero] at htk; linarith
  | succ k ih =>
    by_cases ht : (t : ℝ) ≤ dyadicScale N k
    · obtain ⟨j, hj, hmem⟩ := ih ht
      exact ⟨j, by omega, hmem⟩
    · refine ⟨k, Nat.lt_succ_self k, (mem_blockSupport (dyadicScale_pos hN k).le t).mpr ?_⟩
      exact ⟨lt_of_not_ge ht, by rwa [dyadicScale_succ] at htk⟩

theorem existsUnique_dyadic_block {N t : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ))
    (htV : sourceVaughanV N < (t : ℝ)) (htU : (t : ℝ) ≤ (N : ℝ) / sourceVaughanU N) :
    ∃! j, j < dyadicCount N ∧ t ∈ blockSupport (dyadicScale N j) := by
  obtain ⟨j, hj, htj⟩ := exists_mem_dyadic_block hN (dyadicCount N) t htV
    (htU.trans (upper_le_dyadicScale_count hN))
  refine ⟨j, ⟨hj, htj⟩, ?_⟩
  intro k hk
  rcases lt_trichotomy k j with h | h | h
  · exact False.elim ((disjoint_left.mp (dyadic_blocks_disjoint hN h)) hk.2 htj)
  · exact h
  · exact False.elim ((disjoint_left.mp (dyadic_blocks_disjoint hN h)) htj hk.2)

theorem sum_dyadic_blocks {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (k : ℕ) (f : ℕ → ℂ) :
    (∑ j ∈ range k, ∑ t ∈ blockSupport (dyadicScale N j), f t) =
      ∑ t ∈ Ioc ⌊sourceVaughanV N⌋₊ ⌊dyadicScale N k⌋₊, f t := by
  induction k with
  | zero => simp [dyadicScale_zero]
  | succ k ih =>
    rw [sum_range_succ, ih, blockSupport, ← dyadicScale_succ]
    exact sum_Ioc_consecutive f (Nat.floor_mono (V_le_dyadicScale hN k))
      (Nat.floor_mono (dyadicScale_mono hN (Nat.le_succ k)))

theorem sourceS4_eq_effectiveSum {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (α : ℝ) :
    VaughanTypeI.sourceS4 N α =
      ∑ t ∈ effectiveSupport N, (ArithmeticFunction.moebius t : ℝ) • innerSum N t α := by
  rw [sourceS4_eq_outerSum hN]
  have hU := sourceVaughanU_pos hN
  have hV := sourceVaughanV_pos hN
  have hX : 0 ≤ (N : ℝ) / sourceVaughanU N := by positivity
  have hsub : effectiveSupport N ⊆ outerSupport N := by
    intro t ht
    obtain ⟨htV, htU⟩ := mem_Ioc.mp ht
    have htV' := (Nat.floor_lt hV.le).mp htV
    have htU' := (Nat.le_floor_iff hX).mp htU
    have htN : (t : ℝ) ≤ N :=
      htU'.trans (div_le_self (Nat.cast_nonneg N) (one_lt_sourceVaughanU hN).le)
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by exact_mod_cast htN⟩, htV'⟩
  symm
  apply sum_subset hsub
  intro t ht hnot
  have htV := (Nat.floor_lt hV.le).mpr (mem_filter.mp ht).2
  have htU : (N : ℝ) / sourceVaughanU N < (t : ℝ) := by
    by_contra h
    exact hnot (mem_Ioc.mpr ⟨htV, (Nat.le_floor_iff hX).mpr (le_of_not_gt h)⟩)
  rw [innerSum_eq_zero_of_upper hN htU, smul_zero]

theorem sourceS4_eq_dyadic_blocks {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (α : ℝ) :
    VaughanTypeI.sourceS4 N α = ∑ j ∈ range (dyadicCount N), block N (dyadicScale N j) α := by
  rw [sourceS4_eq_effectiveSum hN]
  unfold block
  rw [sum_dyadic_blocks hN]
  have hX : 0 ≤ (N : ℝ) / sourceVaughanU N := by
    exact div_nonneg (Nat.cast_nonneg N) (sourceVaughanU_pos hN).le
  apply sum_subset
  · exact Ioc_subset_Ioc_right (Nat.floor_mono (upper_le_dyadicScale_count hN))
  · intro t ht hnot
    have htU : (N : ℝ) / sourceVaughanU N < (t : ℝ) := by
      by_contra h
      exact hnot (mem_Ioc.mpr ⟨(mem_Ioc.mp ht).1,
        (Nat.le_floor_iff hX).mpr (le_of_not_gt h)⟩)
    rw [innerSum_eq_zero_of_upper hN htU, smul_zero]

theorem sourceS4_le_sqrt_sum {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (α : ℝ) :
    ‖VaughanTypeI.sourceS4 N α‖ ≤
      ∑ j ∈ range (dyadicCount N),
        Real.sqrt (((6111 / 10000) * (31 / 100)) * (N : ℝ) *
          Real.log ((N : ℝ) / sourceVaughanV N) ^ 2 * rowMax N (dyadicScale N j) α) := by
  have hn := exp_2000_le_of_exp_3100_le hN
  rw [sourceS4_eq_dyadic_blocks hn]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro j hj
  exact Real.le_sqrt_of_sq_le
    (block_sq_le_paid_moment_rowMax hN (V_le_dyadicScale hn j)
      (dyadicScale_lt_upper hn (mem_range.mp hj)).le α)

end LiuWang.Proof.VaughanTypeII
