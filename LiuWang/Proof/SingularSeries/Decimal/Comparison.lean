import LiuWang.Proof.SingularSeries.Decimal.Zeta

/-! Analytic comparison of the original odd-prime product with zeta(2). -/

set_option autoImplicit false
noncomputable section
open Finset
open scoped Topology
open MathlibNt.SieveTheory.SingularSeries

namespace LiuWang.Proof.SingularSeries.Decimal

def oddPrimes (B : ℕ) : Finset ℕ :=
  (range (B + 1)).filter (fun p => p.Prime ∧ 2 < p)

theorem mem_oddPrimes {p B : ℕ} :
    p ∈ oddPrimes B ↔ p ≤ B ∧ p.Prime ∧ 2 < p := by
  simp [oddPrimes]

theorem universalTruncated_eq (B : ℕ) :
    universalTruncated B = ∏ p ∈ oddPrimes B, a p := by
  rw [universalTruncated_source]
  simp [oddPrimes, a, prod_ite]

theorem prime_filter_split {B : ℕ} (hB : 2 ≤ B) :
    (range (B + 1)).filter Nat.Prime = insert 2 (oddPrimes B) := by
  ext p
  simp only [mem_filter, mem_range, Nat.lt_succ_iff, mem_insert, mem_oddPrimes]
  constructor
  · rintro ⟨hpB, hp⟩
    have := hp.two_le
    by_cases h : p = 2
    · exact Or.inl h
    · exact Or.inr ⟨hpB, hp, by omega⟩
  · rintro (rfl | ⟨hpB, hp, _⟩)
    · exact ⟨hB, Nat.prime_two⟩
    · exact ⟨hpB, hp⟩

theorem odd_zeta_product_lower {B : ℕ} (hB : 2 ≤ B) :
    8 / Real.pi ^ 2 ≤ ∏ p ∈ oddPrimes B, b p := by
  have h := finite_zeta_product_lower (range (B + 1))
  rw [prime_filter_split hB, prod_insert (by simp [mem_oddPrimes])] at h
  rw [show b ((2 : ℕ) : ℝ) = 3 / 4 by norm_num [b]] at h
  have hp := sq_pos_of_pos Real.pi_pos
  apply (div_le_iff₀ hp).mpr
  have h' := (div_le_iff₀ hp).mp h
  nlinarith

def smallRatio : ℝ := ∏ p ∈ oddPrimes 100, a p / b p

theorem odd_b_product_pos (B : ℕ) : 0 < ∏ p ∈ oddPrimes B, b p := by
  apply prod_pos
  intro p hp
  apply b_pos
  exact_mod_cast (mem_oddPrimes.mp hp).2.1.one_lt

theorem odd_a_product_pos (B : ℕ) : 0 < ∏ p ∈ oddPrimes B, a p := by
  apply prod_pos
  intro p hp
  apply a_pos
  exact_mod_cast (mem_oddPrimes.mp hp).2.2

theorem smallRatio_pos : 0 < smallRatio := by
  rw [smallRatio, prod_div_distrib]
  exact div_pos (odd_a_product_pos 100) (odd_b_product_pos 100)

theorem odd_product_split (f : ℕ → ℝ) {B : ℕ} (hB : 100 ≤ B) :
    (∏ p ∈ oddPrimes B, f p) =
      (∏ p ∈ oddPrimes 100, f p) *
        ∏ p ∈ (oddPrimes B).filter (fun p => 100 < p), f p := by
  have he : (oddPrimes B).filter (fun p => p ≤ 100) = oddPrimes 100 := by
    ext p
    simp only [mem_filter, mem_oddPrimes]
    constructor
    · rintro ⟨⟨_, hp, h2⟩, h100⟩
      exact ⟨h100, hp, h2⟩
    · rintro ⟨h100, hp, h2⟩
      exact ⟨⟨h100.trans hB, hp, h2⟩, h100⟩
  have h := prod_filter_mul_prod_filter_not (oddPrimes B) (fun p => p ≤ 100) f
  simpa only [he, Nat.not_le] using h.symm

theorem smallRatio_mul_odd_b {B : ℕ} (hB : 100 ≤ B) :
    smallRatio * (∏ p ∈ oddPrimes B, b p) =
      (∏ p ∈ oddPrimes 100, a p) *
        ∏ p ∈ (oddPrimes B).filter (fun p => 100 < p), b p := by
  rw [odd_product_split (fun p => b p) hB, smallRatio, prod_div_distrib,
    ← mul_assoc, div_mul_cancel₀ _ (odd_b_product_pos 100).ne']

theorem cubic_correction_nonneg {t : ℝ} (ht : 5 ≤ t) :
    0 ≤ 1 - 3 / t ^ 3 := by
  have ht0 : 0 < t := by linarith
  have ht3 : 3 ≤ t ^ 3 := by nlinarith [sq_nonneg t]
  exact sub_nonneg.mpr ((div_le_one (pow_pos ht0 3)).mpr ht3)

theorem truncated_comparison {B : ℕ} (hB : 100 ≤ B) :
    smallRatio * (∏ p ∈ oddPrimes B, b p) * (1 - (3 / 40000 : ℝ)) ≤
      universalTruncated B := by
  let s := (oddPrimes B).filter (fun p => 100 < p)
  have hs : ∀ p ∈ s, p.Prime ∧ 100 < p := by
    intro p hp
    obtain ⟨hp, h100⟩ := mem_filter.mp hp
    exact ⟨(mem_oddPrimes.mp hp).2.1, h100⟩
  have ht :
      (∏ p ∈ s, b p) * (∏ p ∈ s, (1 - 3 / (p : ℝ) ^ 3)) ≤ ∏ p ∈ s, a p := by
    rw [← prod_mul_distrib]
    apply prod_le_prod
    · intro p hp
      have hp5 : (5 : ℝ) ≤ p := by exact_mod_cast (show 5 ≤ p by have := (hs p hp).2; omega)
      exact mul_nonneg (b_pos (by linarith)).le (cubic_correction_nonneg hp5)
    · intro p hp
      apply local_comparison
      exact_mod_cast (show 5 ≤ p by have := (hs p hp).2; omega)
  calc
    _ ≤ smallRatio * (∏ p ∈ oddPrimes B, b p) *
        (∏ p ∈ s, (1 - 3 / (p : ℝ) ^ 3)) :=
      mul_le_mul_of_nonneg_left (prime_correction_lower s hs)
        (mul_nonneg smallRatio_pos.le (odd_b_product_pos B).le)
    _ = (∏ p ∈ oddPrimes 100, a p) *
        ((∏ p ∈ s, b p) * (∏ p ∈ s, (1 - 3 / (p : ℝ) ^ 3))) := by
      rw [smallRatio_mul_odd_b hB]
      exact mul_assoc _ _ _
    _ ≤ (∏ p ∈ oddPrimes 100, a p) * ∏ p ∈ s, a p :=
      mul_le_mul_of_nonneg_left ht (odd_a_product_pos 100).le
    _ = _ := by rw [universalTruncated_eq, odd_product_split (fun p => a p) hB]

theorem universalProduct_analytic_lower_bound :
    (8 / Real.pi ^ 2) * smallRatio * (1 - (3 / 40000 : ℝ)) ≤ universalProduct := by
  apply ge_of_tendsto tendsto_liuUniversalProductTruncated
  filter_upwards [Filter.eventually_ge_atTop 100] with B hB
  apply le_trans _ (truncated_comparison hB)
  apply mul_le_mul_of_nonneg_right _ (by norm_num)
  rw [mul_comm (8 / Real.pi ^ 2)]
  exact mul_le_mul_of_nonneg_left (odd_zeta_product_lower (by omega)) smallRatio_pos.le

end LiuWang.Proof.SingularSeries.Decimal
