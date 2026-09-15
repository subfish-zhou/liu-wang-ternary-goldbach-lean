import LiuWang.Proof.VaughanTypeII.ClosedSupport
import AnalyticNumberTheory.LargeSieve.WellSpaced

/-! 闭共同支持、整数块的半单位取整余量及保留共振的有限核。 -/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.VaughanTypeII

open Finset Interfaces Parameters ArithmeticBounds
open AnalyticNumberTheory.LargeSieve
open scoped BigOperators

def kernel (M z : ℝ) : ℝ :=
  if distToInt z = 0 then M + 1 / 2
  else min (M + 1 / 2) (1 / (2 * distToInt z))

def commonSupport (N : ℕ) (M : ℝ) (m m' : ℕ) : Finset ℕ :=
  (blockSupport M).filter fun t => m * t ∈ windowFinset N ∧ m' * t ∈ windowFinset N

def rowSum (N : ℕ) (M α : ℝ) (m : ℕ) : ℝ :=
  ∑ m' ∈ coefficientSupport N M, kernel M (α * ((m : ℝ) - (m' : ℝ)))

def rowMax (N : ℕ) (M α : ℝ) : ℝ :=
  (insert 0 ((coefficientSupport N M).image (rowSum N M α))).max'
    (by simp)

theorem rowMax_nonneg (N : ℕ) (M α : ℝ) : 0 ≤ rowMax N M α := by
  classical
  exact le_max' _ _ (mem_insert_self _ _)

theorem rowSum_le_rowMax {N m : ℕ} {M α : ℝ}
    (hm : m ∈ coefficientSupport N M) : rowSum N M α m ≤ rowMax N M α := by
  classical
  exact le_max' _ _ (mem_insert_of_mem (mem_image_of_mem _ hm))

theorem rowMax_eq_zero_of_empty {N : ℕ} {M α : ℝ}
    (h : coefficientSupport N M = ∅) : rowMax N M α = 0 := by
  simp [rowMax, h]

theorem kernel_nonneg {M : ℝ} (hM : 0 ≤ M) (z : ℝ) : 0 ≤ kernel M z := by
  unfold kernel
  split_ifs
  · positivity
  · exact le_min (by positivity)
      (one_div_nonneg.mpr (mul_nonneg (by norm_num) (distToInt_nonneg z)))

theorem kernel_neg (M z : ℝ) : kernel M (-z) = kernel M z := by
  simp only [kernel, distToInt_neg]

theorem kernel_symm (M α : ℝ) (m m' : ℕ) :
    kernel M (α * ((m : ℝ) - (m' : ℝ))) =
      kernel M (α * ((m' : ℝ) - (m : ℝ))) := by
  rw [show α * ((m : ℝ) - (m' : ℝ)) = -(α * ((m' : ℝ) - (m : ℝ))) by ring,
    kernel_neg]

theorem mem_blockSupport {M : ℝ} (hM : 0 ≤ M) (t : ℕ) :
    t ∈ blockSupport M ↔ M < (t : ℝ) ∧ (t : ℝ) ≤ 2 * M := by
  simp only [blockSupport, mem_Ioc, Nat.floor_lt hM,
    Nat.le_floor_iff (show 0 ≤ 2 * M by positivity)]

theorem blockSupport_card_le {M : ℝ} (hM : 0 ≤ M) :
    ((blockSupport M).card : ℝ) ≤ M + 1 / 2 := by
  have hfloor : ⌊M⌋₊ ≤ ⌊2 * M⌋₊ := Nat.floor_mono (by linarith)
  have htwo : ⌊2 * M⌋₊ < 2 * ⌊M⌋₊ + 2 := by
    apply (Nat.floor_lt (by positivity : 0 ≤ 2 * M)).mpr
    have := Nat.lt_floor_add_one M
    push_cast
    linarith
  have htwoR : (⌊2 * M⌋₊ : ℝ) ≤ 2 * (⌊M⌋₊ : ℝ) + 1 := by
    exact_mod_cast (show ⌊2 * M⌋₊ ≤ 2 * ⌊M⌋₊ + 1 by omega)
  have hf := Nat.floor_le (show 0 ≤ 2 * M by positivity)
  simp only [blockSupport, Nat.card_Ioc, Nat.cast_sub hfloor]
  linarith

theorem mem_product_window {N m t : ℕ} (hm : 0 < m) :
    m * t ∈ windowFinset N ↔
      ⌈(N : ℝ) / (1000 * (m : ℝ))⌉₊ ≤ t ∧ t ≤ ⌊(N : ℝ) / (m : ℝ)⌋₊ := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  rw [Nat.ceil_le, Nat.le_floor_iff (by positivity),
    div_le_iff₀ (by positivity : 0 < 1000 * (m : ℝ)), le_div_iff₀ hmR]
  simp only [mem_windowFinset_iff, mem_windowSet_iff]
  constructor
  · rintro ⟨ha, hb⟩
    constructor
    · have : (N : ℝ) ≤ 1000 * ((m : ℝ) * (t : ℝ)) := by exact_mod_cast hb
      nlinarith
    · have : (m : ℝ) * (t : ℝ) ≤ N := by exact_mod_cast ha
      nlinarith
  · rintro ⟨ha, hb⟩
    constructor
    · exact_mod_cast (show (m : ℝ) * (t : ℝ) ≤ N by nlinarith)
    · exact_mod_cast (show (N : ℝ) ≤ 1000 * ((m : ℝ) * (t : ℝ)) by nlinarith)

theorem commonSupport_eq_Icc (N : ℕ) (M : ℝ) {m m' : ℕ}
    (hm : 0 < m) (hm' : 0 < m') :
    commonSupport N M m m' =
      Icc (max (⌊M⌋₊ + 1)
        (max ⌈(N : ℝ) / (1000 * (m : ℝ))⌉₊ ⌈(N : ℝ) / (1000 * (m' : ℝ))⌉₊))
        (min ⌊2 * M⌋₊ (min ⌊(N : ℝ) / (m : ℝ)⌋₊ ⌊(N : ℝ) / (m' : ℝ)⌋₊)) := by
  ext t
  simp only [commonSupport, blockSupport, mem_filter, mem_Ioc, mem_Icc,
    mem_product_window hm, mem_product_window hm', max_le_iff, le_min_iff]
  omega

theorem norm_char (x : ℝ) : ‖charReal x‖ = 1 := by
  simpa [charReal] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)

theorem natInterval_char_norm (a b : ℕ) (z : ℝ) :
    ‖∑ t ∈ Icc a b, charReal ((t : ℝ) * z)‖ =
      ‖∑ t ∈ range (b + 1 - a), charReal ((t : ℝ) * z)‖ := by
  have he : Icc a b = Ico a (b + 1) := by ext t; simp
  rw [he, sum_Ico_eq_sum_range]
  have hs : (∑ t ∈ range (b + 1 - a), charReal (((a + t : ℕ) : ℝ) * z)) =
      charReal ((a : ℝ) * z) * ∑ t ∈ range (b + 1 - a), charReal ((t : ℝ) * z) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro t ht
    rw [Nat.cast_add, add_mul, charReal_add]
  rw [hs, norm_mul, norm_char, one_mul]

theorem natInterval_char_le_kernel {M : ℝ} (a b : ℕ) (z : ℝ)
    (hc : ((Icc a b).card : ℝ) ≤ M + 1 / 2) :
    ‖∑ t ∈ Icc a b, charReal ((t : ℝ) * z)‖ ≤ kernel M z := by
  rw [natInterval_char_norm]
  have hc' : ((b + 1 - a : ℕ) : ℝ) ≤ M + 1 / 2 := by simpa using hc
  have htriv := (geomSum_exp_bound_trivial (b + 1 - a) z).trans hc'
  unfold kernel
  split_ifs with hz
  · exact htriv
  · apply le_min htriv
    apply geomSum_exp_bound_far
    rintro ⟨k, rfl⟩
    exact hz (by simp [distToInt])

theorem common_char_le_kernel {N m m' : ℕ} {M : ℝ}
    (hM : 0 ≤ M) (hm : 0 < m) (hm' : 0 < m') (z : ℝ) :
    ‖∑ t ∈ commonSupport N M m m', charReal ((t : ℝ) * z)‖ ≤ kernel M z := by
  have hc : ((commonSupport N M m m').card : ℝ) ≤ M + 1 / 2 :=
    (Nat.cast_le.mpr (card_le_card (filter_subset _ _))).trans (blockSupport_card_le hM)
  rw [commonSupport_eq_Icc N M hm hm'] at hc ⊢
  exact natInterval_char_le_kernel _ _ z hc

end LiuWang.Proof.VaughanTypeII
