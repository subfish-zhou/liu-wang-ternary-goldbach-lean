import LiuWang.Proof.Campaign20260915.RSMediumRange.BatchPrimality

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.RSMediumRange

def packedCompositeRun : ℕ → ℕ → ℕ → Prop
  | _, 0, code => code = 0
  | n, len + 1, code =>
      2 ≤ code % 65536 ∧ code % 65536 < n ∧ n % (code % 65536) = 0 ∧
      packedCompositeRun (n + 1) len (code / 65536)

instance (n len code : ℕ) : Decidable (packedCompositeRun n len code) := by
  induction len generalizing n code with
  | zero => exact inferInstanceAs (Decidable (code = 0))
  | succ len ih =>
    unfold packedCompositeRun
    exact instDecidableAnd

theorem packedCompositeRun_sound {n len code : ℕ}
    (h : packedCompositeRun n len code) :
    ∀ p, n ≤ p → p < n + len → ¬p.Prime := by
  induction len generalizing n code with
  | zero => intro p hp hi; omega
  | succ len ih =>
    intro p hp hi
    obtain ⟨hd, hlt, hmod, ht⟩ := h
    by_cases he : p = n
    · subst p
      exact Nat.not_prime_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero hmod) hd hlt
    · exact ih ht p (by omega) (by omega)

def NoPrimeGap (a b : ℕ) : Prop := ∀ p, a < p → p < b → ¬p.Prime

theorem gap_of_packed {a b code : ℕ} (hab : a < b)
    (h : packedCompositeRun (a + 1) (b - a - 1) code) : NoPrimeGap a b := by
  intro p ha hb
  exact packedCompositeRun_sound h p (by omega) (by omega)

theorem primesLE_of_gap {a b n : ℕ} (hgap : NoPrimeGap a b)
    (han : a ≤ n) (hnb : n < b) : Nat.primesLE n = Nat.primesLE a := by
  ext p
  simp only [Nat.mem_primesLE]
  constructor
  · rintro ⟨hpn, hp⟩
    refine ⟨?_, hp⟩
    by_contra! hpa
    exact hgap p hpa (hpn.trans_lt hnb) hp
  · rintro ⟨hpa, hp⟩
    exact ⟨hpa.trans han, hp⟩

theorem primesLE_insert_of_gap {a p : ℕ} (ha : a < p) (hp : p.Prime)
    (hgap : NoPrimeGap a p) :
    Nat.primesLE p = insert p (Nat.primesLE a) := by
  have h := primesLE_of_gap hgap (n := p - 1) (by omega) (by omega)
  have he : p = (p - 1) + 1 := by omega
  conv_lhs => rw [he, Nat.primesLE_succ]
  rw [← he, if_pos hp, h]

#print axioms gap_of_packed

end LiuWang.Proof.Campaign20260915.RSMediumRange
