import LiuWang.Proof.NonprincipalDensityMeans.TruncationMean

/-! # Collect the actual finite L times Mobius Q before taking the mean -/

set_option autoImplicit false
noncomputable section

open Finset
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.NonprincipalDensityAdvance

namespace LiuWang.Proof.NonprincipalDensityMeans.Continuation

def productFiber (M N n : ℕ) : Finset (ℕ × ℕ) :=
  (((range M).erase 0).product ((range N).erase 0)).filter (fun ab => ab.1 * ab.2 = n)

def productCoefficient (M N n : ℕ) : ℂ :=
  ∑ ab ∈ productFiber M N n, (ArithmeticFunction.moebius ab.2 : ℂ)

def detectorCoefficient (M N n : ℕ) : ℂ :=
  productCoefficient M N n - if n = 1 then 1 else 0

theorem product_mem_support {M N : ℕ} {ab : ℕ × ℕ}
    (hab : ab ∈ ((range M).erase 0).product ((range N).erase 0)) :
    ab.1 * ab.2 ∈ (range (M * N + 1)).erase 0 := by
  obtain ⟨ha, hb⟩ := mem_product.mp hab
  have ha' := mem_erase.mp ha
  have hb' := mem_erase.mp hb
  apply mem_erase.mpr
  refine ⟨mul_ne_zero ha'.1 hb'.1, mem_range.mpr ?_⟩
  exact Nat.lt_succ_of_le (Nat.mul_le_mul (mem_range.mp ha'.2).le (mem_range.mp hb'.2).le)

theorem productFiber_card_le (M N n : ℕ) :
    (productFiber M N n).card ≤ n.divisors.card := by
  apply card_le_card_of_injOn Prod.fst
  · intro ab hab
    obtain ⟨hab, he⟩ := mem_filter.mp hab
    have hp := mem_erase.mp (product_mem_support hab)
    exact Nat.mem_divisors.mpr ⟨he ▸ dvd_mul_right ab.1 ab.2, he ▸ hp.1⟩
  · intro ab hab cd hcd he
    have ha := (mem_erase.mp (mem_product.mp (mem_filter.mp hab).1).1).1
    have hp := (mem_filter.mp hab).2.trans (mem_filter.mp hcd).2.symm
    change ab.1 = cd.1 at he
    have hb : ab.2 = cd.2 := by
      rw [← he] at hp
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero ha) hp
    exact Prod.ext he hb

theorem productCoefficient_norm_le (M N n : ℕ) :
    ‖productCoefficient M N n‖ ≤ n.divisors.card := by
  calc
    _ ≤ ∑ ab ∈ productFiber M N n, ‖(ArithmeticFunction.moebius ab.2 : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _ab ∈ productFiber M N n, (1 : ℝ) := by
      apply sum_le_sum
      intro ab _
      rcases ArithmeticFunction.moebius_eq_or ab.2 with h | h | h <;> simp [h]
    _ = ((productFiber M N n).card : ℝ) := by simp
    _ ≤ _ := Nat.cast_le.mpr (productFiber_card_le M N n)

theorem productCoefficient_one {M N : ℕ} (hM : 2 ≤ M) (hN : 2 ≤ N) :
    productCoefficient M N 1 = 1 := by
  have he : productFiber M N 1 = {(1, 1)} := by
    ext ab
    constructor
    · intro hab
      obtain ⟨hab, he⟩ := mem_filter.mp hab
      have ha : 0 < ab.1 := Nat.pos_of_ne_zero (mem_erase.mp (mem_product.mp hab).1).1
      have hb : 0 < ab.2 := Nat.pos_of_ne_zero (mem_erase.mp (mem_product.mp hab).2).1
      have ha1 : ab.1 ≤ 1 := he ▸ Nat.le_mul_of_pos_right _ hb
      have hb1 : ab.2 ≤ 1 := he ▸ Nat.le_mul_of_pos_left _ ha
      exact mem_singleton.mpr (Prod.ext (by omega) (by omega))
    · intro hab
      have he := mem_singleton.mp hab
      rw [he]
      simp only [productFiber, mem_filter]
      norm_num
      omega
  simp [productCoefficient, he]

theorem detectorCoefficient_norm_le {M N : ℕ} (hM : 2 ≤ M) (hN : 2 ≤ N) (n : ℕ) :
    ‖detectorCoefficient M N n‖ ≤ n.divisors.card := by
  by_cases hn : n = 1
  · subst n
    simp [detectorCoefficient, productCoefficient_one hM hN]
  · simpa only [detectorCoefficient, if_neg hn, sub_zero] using productCoefficient_norm_le M N n

theorem partialL_mul_Q_eq_collected {q : ℕ} (chi : Character q) (M : ℕ) (X : ℝ) (s : ℂ) :
    partialL chi M s * NonprincipalDensityAdvance.Q chi X s =
      dirichletPolynomial chi ((range (M * ⌈X⌉₊ + 1)).erase 0)
        (productCoefficient M ⌈X⌉₊) s := by
  rw [Q_eq_dirichletPolynomial]
  unfold partialL dirichletPolynomial
  rw [sum_mul_sum, ← sum_product']
  have he :
      (∑ n ∈ (range (M * ⌈X⌉₊ + 1)).erase 0,
        (∑ ab ∈ productFiber M ⌈X⌉₊ n, (ArithmeticFunction.moebius ab.2 : ℂ)) *
          chi n / (n : ℂ) ^ s) =
      ∑ ab ∈ ((range M).erase 0).product ((range ⌈X⌉₊).erase 0),
        (ArithmeticFunction.moebius ab.2 : ℂ) * chi (ab.1 * ab.2) /
          ((ab.1 * ab.2 : ℕ) : ℂ) ^ s := by
    simp only [sum_mul, sum_div]
    have ht (n : ℕ) :
        (∑ ab ∈ productFiber M ⌈X⌉₊ n,
          (ArithmeticFunction.moebius ab.2 : ℂ) * chi n / (n : ℂ) ^ s) =
        ∑ ab ∈ productFiber M ⌈X⌉₊ n,
          (ArithmeticFunction.moebius ab.2 : ℂ) * chi (ab.1 * ab.2) /
            ((ab.1 * ab.2 : ℕ) : ℂ) ^ s := by
      apply sum_congr rfl
      intro ab hab
      rw [← Nat.cast_mul (α := ZMod q), (mem_filter.mp hab).2]
    simp_rw [ht]
    exact sum_fiberwise_of_maps_to (fun _ hab => product_mem_support hab) _
  rw [show productCoefficient M ⌈X⌉₊ = fun n =>
    ∑ ab ∈ productFiber M ⌈X⌉₊ n, (ArithmeticFunction.moebius ab.2 : ℂ) from rfl, he]
  apply sum_congr rfl
  intro ab _
  rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  have hc : chi (ab.1 * ab.2) = chi ab.1 * chi ab.2 := by
    simp only [map_mul]
  rw [hc]
  ring

theorem finiteDetector_eq_collected {q : ℕ} (chi : Character q) (X : ℝ)
    {M : ℕ} (hM : 2 ≤ M) (hX : 1 < X) (s : ℂ) :
    finiteDetector chi X M s =
      dirichletPolynomial chi ((range (M * ⌈X⌉₊ + 1)).erase 0)
        (detectorCoefficient M ⌈X⌉₊) s := by
  have hN : 2 ≤ ⌈X⌉₊ := by
    have : 1 < ⌈X⌉₊ := Nat.lt_ceil.mpr (by simpa using hX)
    omega
  have h1 : 1 ∈ (range (M * ⌈X⌉₊ + 1)).erase 0 := by
    apply mem_erase.mpr
    refine ⟨by decide, mem_range.mpr ?_⟩
    have := Nat.mul_le_mul hM hN
    omega
  have he : (∑ n ∈ (range (M * ⌈X⌉₊ + 1)).erase 0,
      (if n = 1 then (1 : ℂ) else 0) * chi n / (n : ℂ) ^ s) = 1 := by
    rw [sum_eq_single_of_mem 1 h1]
    · simp
    · intro n _ hn
      simp [hn]
  unfold finiteDetector
  rw [partialL_mul_Q_eq_collected]
  unfold dirichletPolynomial detectorCoefficient
  simp only [sub_mul, sub_div, sum_sub_distrib]
  rw [he]

end LiuWang.Proof.NonprincipalDensityMeans.Continuation
