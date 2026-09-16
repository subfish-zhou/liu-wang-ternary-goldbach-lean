import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Core

set_option autoImplicit false
set_option Elab.async false

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension

def CompositeRun : ℕ → List ℕ → Prop
  | _, [] => True
  | n, d :: ds => 2 ≤ d ∧ d < n ∧ d ∣ n ∧ CompositeRun (n + 1) ds

instance (n : ℕ) (ds : List ℕ) : Decidable (CompositeRun n ds) := by
  induction ds generalizing n with
  | nil => exact instDecidableTrue
  | cons d ds ih =>
    unfold CompositeRun
    exact instDecidableAnd

theorem compositeRun_sound {n : ℕ} {ds : List ℕ} (h : CompositeRun n ds) :
    ∀ p, n ≤ p → p < n + ds.length → ¬ p.Prime := by
  induction ds generalizing n with
  | nil => intro p hp hi; simp only [List.length_nil] at hi; omega
  | cons d ds ih =>
    intro p hp hi
    obtain ⟨hd, hdn, hdvd, ht⟩ := h
    by_cases he : p = n
    · subst p
      exact Nat.not_prime_of_dvd_of_lt hdvd hd hdn
    · apply ih ht p (by omega)
      simp only [List.length_cons] at hi
      omega

theorem primeGap_of_factors {a b : ℕ} {ds : List ℕ}
    (hlen : a + 1 + ds.length = b) (h : CompositeRun (a + 1) ds) :
    PrimeGap a b := by
  intro p hp
  obtain ⟨ha, hb⟩ := Finset.mem_Ioo.mp hp
  exact compositeRun_sound h p (by omega) (by omega)

#print axioms primeGap_of_factors

end LiuWang.Proof.Campaign20260915.RSFiniteExtension
