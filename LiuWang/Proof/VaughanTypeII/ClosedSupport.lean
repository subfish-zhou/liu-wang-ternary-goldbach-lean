import LiuWang.Proof.VaughanTypeI.Decomposition
import LiuWang.Proof.ArithmeticBounds.PrimeMoment.Consumer

/-! 实际闭窗口的第二类和。这里不使用旧的左开内层支持。 -/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.VaughanTypeII

open Finset Interfaces Parameters ArithmeticBounds
open AnalyticNumberTheory.LargeSieve
open scoped BigOperators

def closedSupport (N t : ℕ) : Finset ℕ :=
  (Icc 1 N).filter fun m => sourceVaughanU N < (m : ℝ) ∧ m * t ∈ windowFinset N

def innerSum (N t : ℕ) (α : ℝ) : ℂ :=
  ∑ m ∈ closedSupport N t,
    (sourceLargeDivisorWeight N m : ℂ) * charReal (α * (m : ℝ) * (t : ℝ))

def outerSupport (N : ℕ) : Finset ℕ :=
  (Icc 1 N).filter fun t => sourceVaughanV N < (t : ℝ)

def blockSupport (M : ℝ) : Finset ℕ := Ioc ⌊M⌋₊ ⌊2 * M⌋₊

def block (N : ℕ) (M α : ℝ) : ℂ :=
  ∑ t ∈ blockSupport M, (ArithmeticFunction.moebius t : ℝ) • innerSum N t α

def coefficientSupport (N : ℕ) (M : ℝ) : Finset ℕ :=
  Ioc ⌊sourceVaughanU N⌋₊ ⌊(N : ℝ) / M⌋₊

theorem weight_nonneg (N m : ℕ) : 0 ≤ sourceLargeDivisorWeight N m :=
  sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg

theorem weight_eq_zero_of_le {N m : ℕ} (hm : (m : ℝ) ≤ sourceVaughanU N) :
    sourceLargeDivisorWeight N m = 0 := by
  apply sum_eq_zero
  intro r hr
  obtain ⟨hr, hU⟩ := mem_filter.mp hr
  have hle : (r : ℝ) ≤ m := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hr).2)
      (Nat.mem_divisors.mp hr).1
  exact False.elim (not_lt_of_ge (hle.trans hm) hU)

theorem window_pos {N n : ℕ} (hN : 0 < N) (hn : n ∈ windowFinset N) :
    0 < n := by
  have := (mem_windowFinset_iff N n).mp hn
  simp only [mem_windowSet_iff] at this
  omega

theorem sum_window_divisors {N : ℕ} (hN : 0 < N) (f : ℕ → ℕ → ℂ) :
    (∑ n ∈ windowFinset N, ∑ t ∈ n.divisors, f t (n / t)) =
      ∑ t ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).filter (fun m => m * t ∈ windowFinset N),
        f t m := by
  classical
  rw [← sum_sigma (s := windowFinset N) (t := fun n => n.divisors)
      (f := fun p => f p.2 (p.1 / p.2)),
    ← sum_sigma (s := Icc 1 N)
      (t := fun t => (Icc 1 N).filter fun m => m * t ∈ windowFinset N)
      (f := fun p => f p.1 p.2)]
  apply sum_bij (fun p _ => ⟨p.2, p.1 / p.2⟩)
  · intro p hp
    obtain ⟨hn, ht⟩ := mem_sigma.mp hp
    have hn0 := window_pos hN hn
    have hd := (Nat.mem_divisors.mp ht).1
    have ht0 := Nat.pos_of_mem_divisors ht
    have htn := Nat.le_of_dvd hn0 hd
    have hnN := ((mem_windowFinset_iff N p.1).mp hn).1
    have hm0 : 0 < p.1 / p.2 := Nat.div_pos htn ht0
    have hmN : p.1 / p.2 ≤ N := (Nat.div_le_self _ _).trans hnN
    exact mem_sigma.mpr ⟨mem_Icc.mpr ⟨ht0, htn.trans hnN⟩,
      mem_filter.mpr ⟨mem_Icc.mpr ⟨hm0, hmN⟩, by rwa [Nat.div_mul_cancel hd]⟩⟩
  · intro p hp q hq he
    obtain ⟨hpw, hpd⟩ := mem_sigma.mp hp
    obtain ⟨hqw, hqd⟩ := mem_sigma.mp hq
    have ht : p.2 = q.2 := congrArg Sigma.fst he
    have hm : p.1 / p.2 = q.1 / q.2 := by simpa using congrArg Sigma.snd he
    have hn : p.1 = q.1 := by
      calc
        p.1 = p.1 / p.2 * p.2 := (Nat.div_mul_cancel (Nat.mem_divisors.mp hpd).1).symm
        _ = q.1 / q.2 * q.2 := by rw [hm, ht]
        _ = q.1 := Nat.div_mul_cancel (Nat.mem_divisors.mp hqd).1
    exact Sigma.ext hn (by simpa using ht)
  · intro p hp
    obtain ⟨ht, hm⟩ := mem_sigma.mp hp
    obtain ⟨hm, hw⟩ := mem_filter.mp hm
    have ht0 := (mem_Icc.mp ht).1
    refine ⟨⟨p.2 * p.1, p.1⟩, mem_sigma.mpr ⟨hw, ?_⟩, ?_⟩
    · exact Nat.mem_divisors.mpr ⟨dvd_mul_left _ _, (window_pos hN hw).ne'⟩
    · simp [Nat.mul_div_cancel _ ht0]
  · intro p hp
    rfl

theorem sourceS4_eq_outerSum {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (α : ℝ) :
    VaughanTypeI.sourceS4 N α =
      ∑ t ∈ outerSupport N, (ArithmeticFunction.moebius t : ℝ) • innerSum N t α := by
  classical
  have hn0 : 0 < N := by exact_mod_cast natCast_pos_of_exp_le hN
  unfold VaughanTypeI.sourceS4 VaughanTypeI.windowSum VaughanTypeI.sourceLambda4
  simp only [sum_filter, Complex.ofReal_sum, sum_mul]
  have he := sum_window_divisors hn0 (fun t m =>
    if sourceVaughanV N < (t : ℝ) then
      ((ArithmeticFunction.moebius t : ℝ) : ℂ) *
        (sourceLargeDivisorWeight N m : ℂ) * charReal ((m * t : ℕ) * α)
    else 0)
  calc
    _ = ∑ n ∈ windowFinset N, ∑ t ∈ n.divisors,
        if sourceVaughanV N < (t : ℝ) then
          ((ArithmeticFunction.moebius t : ℝ) : ℂ) *
            (sourceLargeDivisorWeight N (n / t) : ℂ) *
              charReal (((n / t) * t : ℕ) * α) else 0 := by
      apply sum_congr rfl
      intro n hn
      apply sum_congr rfl
      intro t ht
      rw [Nat.div_mul_cancel (Nat.mem_divisors.mp ht).1]
      split_ifs <;> simp
    _ = _ := by
      rw [he]
      unfold outerSupport innerSum closedSupport
      rw [sum_filter]
      apply sum_congr rfl
      intro t ht
      by_cases hV : sourceVaughanV N < (t : ℝ)
      · simp only [hV, ite_true, sum_filter, smul_sum, RCLike.real_smul_eq_coe_mul]
        apply sum_congr rfl
        intro m hm
        by_cases hw : m * t ∈ windowFinset N
        · by_cases hU : sourceVaughanU N < (m : ℝ)
          · simp [hU, Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm]
          · simp [hw, hU, weight_eq_zero_of_le (le_of_not_gt hU)]
        · simp [hw]
      · simp [hV]

theorem closedSupport_subset_coefficientSupport {N t : ℕ} {M : ℝ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hM : 0 < M) (ht : M ≤ (t : ℝ)) :
    closedSupport N t ⊆ coefficientSupport N M := by
  intro m hm
  obtain ⟨hmI, hU, hw⟩ := mem_filter.mp hm
  have hp : (m : ℝ) * (t : ℝ) ≤ N := by
    exact_mod_cast ((mem_windowFinset_iff N (m * t)).mp hw).1
  have hmM : (m : ℝ) ≤ (N : ℝ) / M := by
    apply (le_div_iff₀ hM).mpr
    exact (mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg m)).trans hp
  exact mem_Ioc.mpr ⟨(Nat.floor_lt (sourceVaughanU_pos hN).le).mpr hU,
    (Nat.le_floor_iff (div_nonneg (Nat.cast_nonneg N) hM.le)).mpr hmM⟩

theorem innerSum_eq_zero_of_upper {N t : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ))
    (ht : (N : ℝ) / sourceVaughanU N < (t : ℝ)) (α : ℝ) :
    innerSum N t α = 0 := by
  have hU := sourceVaughanU_pos hN
  have ht0 : 0 < (t : ℝ) :=
    (div_nonneg (Nat.cast_nonneg N) hU.le).trans_lt ht
  have hempty : closedSupport N t = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro m hm
    obtain ⟨_, hmU, hw⟩ := mem_filter.mp hm
    have hp : (m : ℝ) * (t : ℝ) ≤ N := by
      exact_mod_cast ((mem_windowFinset_iff N (m * t)).mp hw).1
    have hNt := (div_lt_iff₀ hU).mp ht
    nlinarith [mul_lt_mul_of_pos_right hmU ht0]
  simp [innerSum, hempty]

theorem closedSupport_moment_31 {N t : ℕ} {M : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hM : sourceVaughanV N ≤ M) (hM' : M ≤ (N : ℝ) / sourceVaughanU N)
    (ht : M ≤ (t : ℝ)) :
    (∑ m ∈ closedSupport N t, sourceLargeDivisorWeight N m ^ 2) ≤
      (31 / 100) * ((N : ℝ) / M) * Real.log ((N : ℝ) / sourceVaughanV N) ^ 2 := by
  have hn := exp_2000_le_of_exp_3100_le hN
  exact (sum_le_sum_of_subset_of_nonneg
    (closedSupport_subset_coefficientSupport hn ((sourceVaughanV_pos hn).trans_le hM) ht)
    (fun _ _ _ => sq_nonneg _)).trans (PrimeMoment.source_actual_moment_31 hN hM hM')

end LiuWang.Proof.VaughanTypeII
