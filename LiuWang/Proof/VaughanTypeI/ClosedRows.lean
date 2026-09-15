import LiuWang.Proof.VaughanTypeI.Decomposition
import LiuWang.Proof.VaughanTypeI.Geometric

/-! # 保留闭下端的乘法重指标与实际 S2 核界。 -/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.VaughanTypeI

open Finset Interfaces Parameters AnalyticNumberTheory.LargeSieve

def closedRow (N d : ℕ) : Finset ℕ :=
  Icc (max 1 ⌈sourceWindowLower N / (d : ℝ)⌉₊) (N / d)

theorem mem_closedRow {N d m : ℕ} (hd : 0 < d) :
    m ∈ closedRow N d ↔ 1 ≤ m ∧ d * m ∈ windowFinset N := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hl : ⌈sourceWindowLower N / (d : ℝ)⌉₊ ≤ m ↔ N ≤ 1000 * (d * m) := by
    rw [Nat.ceil_le, div_le_iff₀ hdr, sourceWindowLower,
      div_le_iff₀ (by norm_num : (0 : ℝ) < 1000)]
    norm_cast
    simp only [mul_comm, mul_assoc]
  simp only [closedRow, mem_Icc, max_le_iff, hl, mem_windowFinset_iff,
    mem_windowSet_iff, Nat.le_div_iff_mul_le hd, mul_comm m d]
  omega

theorem sum_window_divisors_reindex {R : Type*} [AddCommMonoid R]
    (N D : ℕ) (F : ℕ → ℕ → R) :
    (∑ n ∈ windowFinset N, ∑ d ∈ n.divisors.filter (fun d => d ≤ D), F d (n / d)) =
      ∑ d ∈ Icc 1 D, ∑ m ∈ closedRow N d, F d m := by
  classical
  rw [← sum_sigma (s := windowFinset N)
    (t := fun n => n.divisors.filter (fun d => d ≤ D))
    (f := fun x => F x.2 (x.1 / x.2)),
    ← sum_sigma (s := Icc 1 D) (t := closedRow N) (f := fun x => F x.1 x.2)]
  apply sum_bij (i := fun (x : (n : ℕ) × ℕ) _ => ⟨x.2, x.1 / x.2⟩)
  · intro x hx
    rcases mem_sigma.mp hx with ⟨hn, hd⟩
    rcases mem_filter.mp hd with ⟨hd, hD⟩
    rcases Nat.mem_divisors.mp hd with ⟨hdn, hn0⟩
    have hdp := Nat.pos_of_dvd_of_pos hdn (Nat.pos_of_ne_zero hn0)
    rw [mem_sigma, mem_Icc, mem_closedRow hdp]
    exact ⟨⟨hdp, hD⟩, Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdn) hdp,
      by simpa only [Nat.mul_div_cancel' hdn] using hn⟩
  · intro x hx y hy h
    have hxD := (mem_filter.mp (mem_sigma.mp hx).2).1
    have hyD := (mem_filter.mp (mem_sigma.mp hy).2).1
    have hd : x.2 = y.2 := congrArg Sigma.fst h
    have hm : x.1 / x.2 = y.1 / y.2 := congrArg Sigma.snd h
    have hn : x.1 = y.1 := by
      calc
        x.1 = x.2 * (x.1 / x.2) := (Nat.mul_div_cancel' (Nat.mem_divisors.mp hxD).1).symm
        _ = y.2 * (y.1 / y.2) := by rw [hm, hd]
        _ = y.1 := Nat.mul_div_cancel' (Nat.mem_divisors.mp hyD).1
    exact Sigma.ext hn (heq_of_eq hd)
  · intro y hy
    rcases mem_sigma.mp hy with ⟨hd, hm⟩
    have hdp := (mem_Icc.mp hd).1
    rcases (mem_closedRow hdp).mp hm with ⟨hmp, hn⟩
    refine ⟨⟨y.1 * y.2, y.1⟩, ?_, ?_⟩
    · rw [mem_sigma, mem_filter, Nat.mem_divisors]
      exact ⟨hn, ⟨dvd_mul_right _ _, (Nat.mul_pos hdp hmp).ne'⟩, (mem_Icc.mp hd).2⟩
    · simp only [Nat.mul_div_cancel_left _ hdp]
  · intro x _
    rfl

theorem norm_closedRow_charReal_le (N : ℕ) {d : ℕ} (hd : 0 < d) (α : ℝ) :
    ‖∑ m ∈ closedRow N d, charReal ((m : ℝ) * ((d : ℝ) * α))‖ ≤
      truncatedKernel ((N : ℝ) / d) ((d : ℝ) * α) := by
  have hfloor : (N / d : ℕ) ≤ (N : ℝ) / d := by
    rw [le_div_iff₀ (by exact_mod_cast hd)]
    exact_mod_cast Nat.div_mul_le_self N d
  have hlen : (N / d + 1 - max 1 ⌈sourceWindowLower N / (d : ℝ)⌉₊ : ℕ) ≤
      (N / d : ℕ) := by
    exact Nat.sub_le_iff_le_add.mpr (Nat.add_le_add_left (le_max_left _ _) _)
  exact (norm_sum_charReal_Icc_le _ _ _).trans (truncatedKernel_mono
    ((Nat.cast_le.mpr hlen).trans hfloor) _)

theorem norm_closedRow_log_charReal_le (N : ℕ) {d : ℕ} (hd : 0 < d) (α : ℝ) :
    ‖∑ m ∈ closedRow N d, (Real.log m : ℂ) *
      charReal ((m : ℝ) * ((d : ℝ) * α))‖ ≤
      sourceL N * truncatedKernel ((N : ℝ) / d) ((d : ℝ) * α) := by
  have hfloor : (N / d : ℕ) ≤ (N : ℝ) / d := by
    rw [le_div_iff₀ (by exact_mod_cast hd)]
    exact_mod_cast Nat.div_mul_le_self N d
  have hlog : Real.log (N / d : ℕ) ≤ sourceL N := by
    by_cases hp : 0 < (N / d : ℕ)
    · exact Real.log_le_log (by exact_mod_cast hp) (by exact_mod_cast Nat.div_le_self N d)
    · have hz : (N / d : ℕ) = 0 := Nat.eq_zero_of_not_pos hp
      simpa [hz, sourceL] using Real.log_natCast_nonneg N
  exact (norm_sum_log_charReal_Icc_le (le_max_left _ _) _).trans
    (mul_le_mul hlog (truncatedKernel_mono hfloor _)
      (truncatedKernel_nonneg (Nat.cast_nonneg _) _) (Real.log_natCast_nonneg N))

theorem sourceS2_eq_closedRows {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (α : ℝ) :
    sourceS2 N α =
      ∑ t ∈ Icc 1 ⌊sourceVaughanV N⌋₊,
        ((ArithmeticFunction.moebius t : ℝ) : ℂ) *
          ∑ m ∈ closedRow N t, (Real.log m : ℂ) *
            charReal ((m : ℝ) * ((t : ℝ) * α)) := by
  unfold sourceS2 windowSum
  simp_rw [sourceLambda2_eq_first hN, AnalyticNumberTheory.Sieve.vaughanFirst]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, sum_mul]
  calc
    _ = ∑ n ∈ windowFinset N,
        ∑ t ∈ n.divisors.filter (fun t => t ≤ ⌊sourceVaughanV N⌋₊),
          ((ArithmeticFunction.moebius t : ℝ) : ℂ) *
            (Real.log (n / t : ℕ) : ℂ) * charReal (((t * (n / t) : ℕ) : ℝ) * α) := by
      apply sum_congr rfl
      intro n _
      apply sum_congr rfl
      intro t ht
      rw [Nat.mul_div_cancel' (Nat.mem_divisors.mp (mem_filter.mp ht).1).1]
    _ = _ := by
      rw [sum_window_divisors_reindex N ⌊sourceVaughanV N⌋₊
        (fun t m => ((ArithmeticFunction.moebius t : ℝ) : ℂ) *
          (Real.log m : ℂ) * charReal (((t * m : ℕ) : ℝ) * α))]
      simp_rw [mul_sum]
      apply sum_congr rfl
      intro t _
      apply sum_congr rfl
      intro m _
      simp only [Nat.cast_mul]
      rw [show (t : ℝ) * m * α = (m : ℝ) * ((t : ℝ) * α) by ring]
      ring

theorem norm_sourceS2_le_kernel {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (α : ℝ) :
    ‖sourceS2 N α‖ ≤
      sourceL N * ∑ t ∈ Icc 1 ⌊sourceVaughanV N⌋₊,
        truncatedKernel ((N : ℝ) / t) ((t : ℝ) * α) := by
  rw [sourceS2_eq_closedRows hN, mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro t ht
  have ht0 := (mem_Icc.mp ht).1
  have hμ : ‖((ArithmeticFunction.moebius t : ℝ) : ℂ)‖ ≤ 1 := by
    rcases ArithmeticFunction.moebius_eq_or t with h | h | h <;> simp [h]
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right hμ (norm_nonneg _)).trans
    (by simpa only [one_mul] using norm_closedRow_log_charReal_le N ht0 α)

end LiuWang.Proof.VaughanTypeI
