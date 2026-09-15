import LiuWang.Proof.Campaign20260915.Totient.ThetaLogData

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.Totient

def prefixUnits (rs : List (ℕ × ℤ)) (n : ℕ) : ℤ :=
  ((rs.filter (fun r => r.1 ≤ n)).map Prod.snd).sum

private theorem unitsFrom_zero {rs : List (ℕ × ℤ)} {p : ℕ}
    (hp : p ∉ rs.map Prod.fst) : unitsFrom rs p = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rcases r with ⟨q, u⟩
    simp only [List.map_cons, List.mem_cons, not_or] at hp
    simpa only [unitsFrom, if_neg hp.1] using ih hp.2

private theorem sum_unitsFrom (rs : List (ℕ × ℤ))
    (hnd : (rs.map Prod.fst).Nodup) (n : ℕ) :
    (∑ p ∈ Finset.range (n + 1), unitsFrom rs p) = prefixUnits rs n := by
  induction rs with
  | nil => simp [unitsFrom, prefixUnits]
  | cons r rs ih =>
    rcases r with ⟨q, u⟩
    simp only [List.map_cons, List.nodup_cons] at hnd
    have he (p : ℕ) :
        unitsFrom ((q, u) :: rs) p = (if p = q then u else 0) + unitsFrom rs p := by
      by_cases hp : p = q
      · subst p
        simp [unitsFrom, unitsFrom_zero hnd.1]
      · simp [unitsFrom, hp]
    simp only [he, Finset.sum_add_distrib, ih hnd.2]
    by_cases hq : q ≤ n <;> simp [prefixUnits, hq]

theorem thetaInteger_eq_prefixUnits (n : ℕ) :
    thetaInteger n = prefixUnits thetaLogRows n :=
  sum_unitsFrom thetaLogRows (by decide +kernel) n

def thetaWalk : ℕ → ℕ → ℤ → Prop
  | _, 0, _ => True
  | n, k + 1, a =>
      (((min (n + 1) 1420 : ℕ) * 10000000000 - a) ^ 2 <
        4 * (min (n + 1) 1420 : ℕ) * 10000000000 ^ 2) ∧
      thetaWalk (n + 1) k (a + unitsFrom thetaLogRows (n + 1))

instance (n k : ℕ) (a : ℤ) : Decidable (thetaWalk n k a) := by
  induction k generalizing n a with
  | zero => exact instDecidableTrue
  | succ k ih =>
    unfold thetaWalk
    exact instDecidableAnd

theorem thetaWalk_sound {k n : ℕ} (h : thetaWalk n k (thetaInteger n)) :
    ∀ m, n ≤ m → m < n + k →
      (((min (m + 1) 1420 : ℕ) : ℤ) * 10000000000 - thetaInteger m) ^ 2 <
        4 * (min (m + 1) 1420 : ℕ) * 10000000000 ^ 2 := by
  induction k generalizing n with
  | zero => intro m hm hlt; omega
  | succ k ih =>
    intro m hm hlt
    have hs : thetaInteger (n + 1) =
        thetaInteger n + unitsFrom thetaLogRows (n + 1) := by
      exact Finset.sum_range_succ _ _
    obtain ⟨hnow, hnext⟩ := h
    by_cases he : m = n
    · subst m
      exact hnow
    · rw [← hs] at hnext
      exact ih hnext m (by omega) (by omega)

theorem theta_walk_tail :
    thetaWalk 1300 121 (prefixUnits thetaLogRows 1300) := by
  decide +kernel

theorem theta_integer_tail {n : ℕ} (hn : 1300 ≤ n) (hi : n ≤ 1420) :
    (((min (n + 1) 1420 : ℕ) : ℤ) * 10000000000 - thetaInteger n) ^ 2 <
      4 * (min (n + 1) 1420 : ℕ) * 10000000000 ^ 2 := by
  exact thetaWalk_sound (by simpa only [thetaInteger_eq_prefixUnits] using theta_walk_tail : thetaWalk 1300 121
    (thetaInteger 1300)) n hn (by omega)

#print axioms thetaInteger_eq_prefixUnits
#print axioms theta_integer_tail

end LiuWang.Proof.Campaign20260915.Totient
