import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Start

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

private theorem lookup_mem (rs : List (ℕ × ℤ)) (p : ℕ)
    (h : p ∈ rs.map Prod.fst) : (p, unitsFrom rs p) ∈ rs := by
  induction rs with
  | nil => simp at h
  | cons r rs ih =>
    rcases r with ⟨q, u⟩
    simp only [List.map_cons, List.mem_cons] at h
    by_cases he : p = q
    · subst p
      simp [unitsFrom]
    · have ht := ih (h.resolve_left he)
      simp only [unitsFrom, if_neg he, List.mem_cons]
      exact Or.inr ht

private theorem lookup_nonneg (rs : List (ℕ × ℤ))
    (h : ∀ r ∈ rs, 0 ≤ r.2) (p : ℕ) : 0 ≤ unitsFrom rs p := by
  induction rs with
  | nil => simp [unitsFrom]
  | cons r rs ih =>
    rcases r with ⟨q, u⟩
    by_cases he : p = q
    · simpa [unitsFrom, he] using h (q, u) (by simp)
    · simpa [unitsFrom, he] using ih (fun r hr => h r (by simp [hr]))

theorem theta_upper_1420 :
    Chebyshev.theta 1420 ≤ (13455622351102 : ℝ) / 10000000000 := by
  have hsmall : ∀ p ∈ Finset.range 286, p.Prime →
      p ∈ thetaLogRows.map Prod.fst := by decide +kernel
  have hnonneg : ∀ r ∈ thetaLogRows, 0 ≤ r.2 := by decide +kernel
  have hpbound (p : ℕ) (hp : p.Prime) (hi : p ≤ 1420) :
      Real.log p ≤ (unitsFrom thetaLogRows p + 61 : ℝ) / 10000000000 := by
    by_cases hlo : 286 ≤ p
    · exact (log_units_bounds hp hlo hi).2
    have hm := lookup_mem thetaLogRows p
      (hsmall p (Finset.mem_range.mpr (by omega)) hp)
    have hu := (theta_log_rows_checked _ hm).2
    have h := (rational_log_bounds (x := (p : ℚ))
      (by exact_mod_cast hp.one_lt.le)).2
    unfold logHi logLo at h
    rw [← hu] at h
    push_cast at h
    have hs : logScale (p : ℚ) ≤ 10 := by
      have hb : Nat.log 2 1420 ≤ 10 := by decide +kernel
      simpa only [logScale, Nat.floor_natCast] using
        (Nat.log_mono_right (b := 2) hi).trans hb
    have hsR : (logScale (p : ℚ) : ℝ) ≤ 10 := by exact_mod_cast hs
    linarith
  have hsum : Chebyshev.theta 1420 ≤
      (thetaInteger 1420 : ℝ) / 10000000000 +
        (1421 : ℝ) * 61 / 10000000000 := by
    have ht := Chebyshev.theta_eq_sum_primesLE_log 1420
    norm_num only [Nat.cast_ofNat] at ht
    rw [ht]
    change (∑ p ∈ (Finset.range 1421).filter Nat.Prime, Real.log p) ≤ _
    rw [Finset.sum_filter]
    have hle : (∑ p ∈ Finset.range 1421, if p.Prime then Real.log p else 0) ≤
        ∑ p ∈ Finset.range 1421,
          (unitsFrom thetaLogRows p + 61 : ℝ) / 10000000000 := by
      apply Finset.sum_le_sum
      intro p hp
      split_ifs with hprime
      · exact hpbound p hprime (by have := Finset.mem_range.mp hp; omega)
      · have hn : (0 : ℝ) ≤ unitsFrom thetaLogRows p := by
          exact_mod_cast lookup_nonneg thetaLogRows hnonneg p
        positivity
    convert hle using 1
    simp only [add_div, Finset.sum_add_distrib, Finset.sum_div, thetaInteger,
      Int.cast_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have he : thetaInteger 1420 = 13455622264421 := by
    rw [thetaInteger_eq_prefixUnits]
    decide +kernel
  rw [he] at hsum
  norm_num at hsum ⊢
  linarith

def UpperReach (a : ℕ) (H : ℤ) : Prop :=
  Chebyshev.theta a ≤ (H : ℝ) / 10000000000 ∧
    ∀ x : ℝ, 1420 ≤ x → x ≤ a → Chebyshev.theta x < x

theorem upper_reach_1420 : UpperReach 1420 13455622351102 := by
  refine ⟨theta_upper_1420, ?_⟩
  intro x hx hi
  have he : x = 1420 := le_antisymm hi hx
  subst x
  exact theta_upper_1420.trans_lt (by norm_num)

theorem theta_between {a b : ℕ} {x : ℝ}
    (hg : PrimeGap a b) (hx : (a : ℝ) ≤ x) (hb : x < b) :
    Chebyshev.theta x = Chebyshev.theta a := by
  have hx0 : 0 ≤ x := (Nat.cast_nonneg a).trans hx
  have hn : a ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).mpr hx
  have hi : ⌊x⌋₊ < b := by exact_mod_cast (Nat.floor_le hx0).trans_lt hb
  rw [Chebyshev.theta_eq_sum_primesLE, primesLE_gap hg hn hi,
    Chebyshev.theta_eq_sum_primesLE_log]

theorem upper_reach_next {a p : ℕ} {H u : ℤ} (ha : 1420 ≤ a) (hap : a < p)
    (hp : p.Prime) (hg : PrimeGap a p)
    (hh : Real.log p ≤ (u + 76 : ℝ) / 10000000000)
    (hnum : H + u + 76 < (p : ℤ) * 10000000000)
    (h : UpperReach a H) : UpperReach p (H + u + 76) := by
  have he := primesLE_next hap hp hg
  have hnot : p ∉ Nat.primesLE a := by simp [Nat.mem_primesLE, hap.not_ge]
  have ht : Chebyshev.theta p = Chebyshev.theta a + Real.log p := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, he, Finset.sum_insert hnot,
      Chebyshev.theta_eq_sum_primesLE_log]
    ring
  have hs : Chebyshev.theta p ≤ ((H + u + 76 : ℤ) : ℝ) / 10000000000 := by
    rw [ht]
    push_cast
    linarith [h.1]
  have hb : Chebyshev.theta p < (p : ℝ) := by
    have hn : (H : ℝ) + u + 76 < (p : ℝ) * 10000000000 := by exact_mod_cast hnum
    exact hs.trans_lt (by push_cast; linarith)
  refine ⟨hs, ?_⟩
  intro x hx hi
  by_cases hxa : x ≤ a
  · exact h.2 x hx hxa
  by_cases hxp : x = p
  · subst x
    exact hb
  rw [theta_between hg (le_of_not_ge hxa) (lt_of_le_of_ne hi hxp)]
  exact (h.2 a (by exact_mod_cast ha) le_rfl).trans_le (le_of_not_ge hxa)

#print axioms theta_upper_1420
#print axioms upper_reach_next

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
