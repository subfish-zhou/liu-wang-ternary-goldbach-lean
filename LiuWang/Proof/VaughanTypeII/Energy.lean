import LiuWang.Proof.VaughanTypeII.Kernel

/-! 同一 α 上的实际闭窗口能量与两个已付款输入的消费。 -/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.VaughanTypeII

open Finset Interfaces Parameters ArithmeticBounds
open AnalyticNumberTheory.LargeSieve
open scoped BigOperators

def windowCharacter (N t m : ℕ) (α : ℝ) : ℂ :=
  if m * t ∈ windowFinset N then charReal (α * (m : ℝ) * (t : ℝ)) else 0

def commonSum (N : ℕ) (M α : ℝ) (m m' : ℕ) : ℂ :=
  ∑ t ∈ commonSupport N M m m', charReal ((t : ℝ) * (α * ((m : ℝ) - (m' : ℝ))))

theorem coefficientSupport_geometry {N m : ℕ} {M : ℝ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hM : sourceVaughanV N ≤ M)
    (hm : m ∈ coefficientSupport N M) :
    m ∈ Icc 1 N ∧ sourceVaughanU N < (m : ℝ) := by
  have hM0 := (sourceVaughanV_pos hN).trans_le hM
  obtain ⟨hu, hx⟩ := mem_Ioc.mp hm
  have hU := (Nat.floor_lt (sourceVaughanU_pos hN).le).mp hu
  have hxR := (Nat.le_floor_iff (div_nonneg (Nat.cast_nonneg N) hM0.le)).mp hx
  have hM1 := (one_lt_sourceVaughanU hN).le.trans ((sourceVaughanU_le_V hN).trans hM)
  have hmN : (m : ℝ) ≤ N := hxR.trans (div_le_self (Nat.cast_nonneg N) hM1)
  exact ⟨mem_Icc.mpr ⟨by omega, by exact_mod_cast hmN⟩, hU⟩

theorem innerSum_eq_coefficientSum {N t : ℕ} {M : ℝ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hM : sourceVaughanV N ≤ M)
    (ht : M ≤ (t : ℝ)) (α : ℝ) :
    innerSum N t α =
      ∑ m ∈ coefficientSupport N M,
        (sourceLargeDivisorWeight N m : ℂ) * windowCharacter N t m α := by
  have hM0 := (sourceVaughanV_pos hN).trans_le hM
  have he : closedSupport N t =
      (coefficientSupport N M).filter fun m => m * t ∈ windowFinset N := by
    ext m
    constructor
    · intro hm
      exact mem_filter.mpr ⟨closedSupport_subset_coefficientSupport hN hM0 ht hm,
        (mem_filter.mp hm).2.2⟩
    · intro hm
      obtain ⟨hmJ, hw⟩ := mem_filter.mp hm
      obtain ⟨hmI, hU⟩ := coefficientSupport_geometry hN hM hmJ
      exact mem_filter.mpr ⟨hmI, hU, hw⟩
  simp only [innerSum, he, sum_filter, windowCharacter, mul_ite, mul_zero]

theorem windowCharacter_cross (N t m m' : ℕ) (α : ℝ) :
    windowCharacter N t m α * star (windowCharacter N t m' α) =
      if m * t ∈ windowFinset N ∧ m' * t ∈ windowFinset N then
        charReal ((t : ℝ) * (α * ((m : ℝ) - (m' : ℝ)))) else 0 := by
  classical
  by_cases hm : m * t ∈ windowFinset N
  · by_cases hm' : m' * t ∈ windowFinset N
    · simp only [windowCharacter, hm, hm', ite_true, and_self]
      rw [← charReal_sub]
      congr 1
      ring
    · simp [windowCharacter, hm, hm']
  · simp [windowCharacter, hm]

theorem energy_expansion {N : ℕ} {M : ℝ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hM : sourceVaughanV N ≤ M) (α : ℝ) :
    ((∑ t ∈ blockSupport M, ‖innerSum N t α‖ ^ 2 : ℝ) : ℂ) =
      ∑ m ∈ coefficientSupport N M, ∑ m' ∈ coefficientSupport N M,
        (sourceLargeDivisorWeight N m : ℂ) * (sourceLargeDivisorWeight N m' : ℂ) *
          commonSum N M α m m' := by
  have hM0 := (sourceVaughanV_pos hN).trans_le hM
  have he := dualExpansion (blockSupport M) (coefficientSupport N M)
    (fun t m => star (windowCharacter N t m α))
    (fun m => (sourceLargeDivisorWeight N m : ℂ))
  simp only [Complex.star_def, Complex.conj_conj, Complex.conj_ofReal] at he
  calc
    _ = ((∑ t ∈ blockSupport M,
        ‖∑ m ∈ coefficientSupport N M,
          windowCharacter N t m α * (sourceLargeDivisorWeight N m : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
      congr 1
      apply sum_congr rfl
      intro t ht
      rw [innerSum_eq_coefficientSum hN hM ((mem_blockSupport hM0.le t).mp ht).1.le α]
      simp only [mul_comm]
    _ = _ := by
      rw [he]
      apply sum_congr rfl
      intro m hm
      apply sum_congr rfl
      intro m' hm'
      congr 1
      simp only [← Complex.star_def, windowCharacter_cross, commonSum,
        commonSupport, sum_filter]

theorem weighted_kernel_le_rowMax {N : ℕ} {M : ℝ}
    (hM : 0 ≤ M) (α : ℝ) :
    (∑ m ∈ coefficientSupport N M, ∑ m' ∈ coefficientSupport N M,
      sourceLargeDivisorWeight N m * sourceLargeDivisorWeight N m' *
        kernel M (α * ((m : ℝ) - (m' : ℝ)))) ≤
      (∑ m ∈ coefficientSupport N M, sourceLargeDivisorWeight N m ^ 2) * rowMax N M α := by
  let J := coefficientSupport N M
  let a := sourceLargeDivisorWeight N
  let K := fun m m' : ℕ => kernel M (α * ((m : ℝ) - (m' : ℝ)))
  have hs : (∑ m ∈ J, ∑ m' ∈ J, (a m ^ 2 + a m' ^ 2) * K m m') =
      2 * ∑ m ∈ J, a m ^ 2 * rowSum N M α m := by
    simp only [add_mul, sum_add_distrib]
    have hswap : (∑ m ∈ J, ∑ m' ∈ J, a m' ^ 2 * K m m') =
        ∑ m ∈ J, ∑ m' ∈ J, a m ^ 2 * K m m' := by
      rw [sum_comm]
      apply sum_congr rfl
      intro m hm
      apply sum_congr rfl
      intro m' hm'
      rw [show K m' m = K m m' from kernel_symm M α m' m]
    rw [hswap]
    simp only [← mul_sum]
    change _ + _ = 2 * (∑ m ∈ J, a m ^ 2 * ∑ m' ∈ J, K m m')
    ring
  have hyoung : 2 * (∑ m ∈ J, ∑ m' ∈ J, a m * a m' * K m m') ≤
      ∑ m ∈ J, ∑ m' ∈ J, (a m ^ 2 + a m' ^ 2) * K m m' := by
    simp only [mul_sum]
    apply sum_le_sum
    intro m hm
    apply sum_le_sum
    intro m' hm'
    have hy : 2 * (a m * a m') ≤ a m ^ 2 + a m' ^ 2 := by nlinarith [sq_nonneg (a m - a m')]
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right hy (kernel_nonneg hM _)
  have hr : (∑ m ∈ J, a m ^ 2 * rowSum N M α m) ≤
      (∑ m ∈ J, a m ^ 2) * rowMax N M α := by
    rw [sum_mul]
    exact sum_le_sum fun m hm =>
      mul_le_mul_of_nonneg_left (rowSum_le_rowMax hm) (sq_nonneg _)
  rw [hs] at hyoung
  change (∑ m ∈ J, ∑ m' ∈ J, a m * a m' * K m m') ≤ _
  linarith

theorem energy_le_moment_mul_rowMax {N : ℕ} {M : ℝ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hM : sourceVaughanV N ≤ M) (α : ℝ) :
    (∑ t ∈ blockSupport M, ‖innerSum N t α‖ ^ 2) ≤
      (∑ m ∈ coefficientSupport N M, sourceLargeDivisorWeight N m ^ 2) * rowMax N M α := by
  have hM0 := (sourceVaughanV_pos hN).trans_le hM
  calc
    _ = ‖((∑ t ∈ blockSupport M, ‖innerSum N t α‖ ^ 2 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sum_nonneg fun _ _ => sq_nonneg _)]
    _ = ‖∑ m ∈ coefficientSupport N M, ∑ m' ∈ coefficientSupport N M,
        (sourceLargeDivisorWeight N m : ℂ) * (sourceLargeDivisorWeight N m' : ℂ) *
          commonSum N M α m m'‖ := by rw [energy_expansion hN hM]
    _ ≤ ∑ m ∈ coefficientSupport N M, ∑ m' ∈ coefficientSupport N M,
        sourceLargeDivisorWeight N m * sourceLargeDivisorWeight N m' *
          kernel M (α * ((m : ℝ) - (m' : ℝ))) := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro m hm
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro m' hm'
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (weight_nonneg N m), abs_of_nonneg (weight_nonneg N m')]
      apply mul_le_mul_of_nonneg_left
      · exact common_char_le_kernel hM0.le
          (mem_Icc.mp (coefficientSupport_geometry hN hM hm).1).1
          (mem_Icc.mp (coefficientSupport_geometry hN hM hm').1).1 _
      · exact mul_nonneg (weight_nonneg N m) (weight_nonneg N m')
    _ ≤ _ := weighted_kernel_le_rowMax hM0.le α

theorem block_sq_le_paid_moment_rowMax {N : ℕ} {M : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hM : sourceVaughanV N ≤ M) (hM' : M ≤ (N : ℝ) / sourceVaughanU N) (α : ℝ) :
    ‖block N M α‖ ^ 2 ≤
      ((6111 / 10000) * (31 / 100)) * (N : ℝ) *
        Real.log ((N : ℝ) / sourceVaughanV N) ^ 2 * rowMax N M α := by
  have hn := exp_2000_le_of_exp_3100_le hN
  have hM0 := (sourceVaughanV_pos hn).trans_le hM
  have h400 : (400000 : ℝ) ≤ M :=
    fourHundredThousand_le_exp_13066.trans ((sourceVaughanV_ge_exp_13066 hn).trans hM)
  calc
    _ ≤ (6111 / 10000) * M * (∑ t ∈ blockSupport M, ‖innerSum N t α‖ ^ 2) :=
      moebius_dyadic_cauchy_6111 h400 (fun t => innerSum N t α)
    _ ≤ (6111 / 10000) * M *
        ((∑ m ∈ coefficientSupport N M, sourceLargeDivisorWeight N m ^ 2) * rowMax N M α) :=
      mul_le_mul_of_nonneg_left (energy_le_moment_mul_rowMax hn hM α) (by positivity)
    _ ≤ (6111 / 10000) * M *
        ((31 / 100) * ((N : ℝ) / M) * Real.log ((N : ℝ) / sourceVaughanV N) ^ 2 *
          rowMax N M α) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (PrimeMoment.source_actual_moment_31 hN hM hM')
          (rowMax_nonneg N M α)) (by positivity)
    _ = _ := by field_simp

end LiuWang.Proof.VaughanTypeII
