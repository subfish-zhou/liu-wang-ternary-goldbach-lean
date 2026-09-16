import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Core

set_option autoImplicit false
set_option Elab.async false

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension

def PrimeSpan (a b : ℕ) (ps : List ℕ) : Prop :=
  ∀ p, p ∈ ps ↔ a < p ∧ p ≤ b ∧ p.Prime

theorem primeSpan_of_checked {a b : ℕ} {ps : List ℕ}
    (h : ∀ p ∈ Finset.Ioc a b, p.Prime ↔ p ∈ ps)
    (hr : ∀ p ∈ ps, a < p ∧ p ≤ b) : PrimeSpan a b ps := by
  intro p
  constructor
  · intro hp
    obtain ⟨ha, hb⟩ := hr p hp
    exact ⟨ha, hb, (h p (Finset.mem_Ioc.mpr ⟨ha, hb⟩)).mpr hp⟩
  · rintro ⟨ha, hb, hp⟩
    exact (h p (Finset.mem_Ioc.mpr ⟨ha, hb⟩)).mp hp

theorem primeSpan_append {a b c : ℕ} {ps qs : List ℕ}
    (ha : a ≤ b) (hc : b ≤ c) (h : PrimeSpan a b ps) (g : PrimeSpan b c qs) :
    PrimeSpan a c (ps ++ qs) := by
  intro p
  rw [List.mem_append, h p, g p]
  constructor
  · rintro (⟨hp, hb, hprime⟩ | ⟨hp, hb, hprime⟩)
    · exact ⟨hp, hb.trans hc, hprime⟩
    · exact ⟨ha.trans_lt hp, hb, hprime⟩
  · rintro ⟨hp, hb, hprime⟩
    by_cases hm : p ≤ b
    · exact Or.inl ⟨hp, hm, hprime⟩
    · exact Or.inr ⟨by omega, hb, hprime⟩

theorem primeSpan_nodup_append {a b c : ℕ} {ps qs : List ℕ}
    (h : PrimeSpan a b ps) (g : PrimeSpan b c qs)
    (hp : ps.Nodup) (hq : qs.Nodup) : (ps ++ qs).Nodup := by
  apply List.Nodup.append hp hq
  intro p hps hqs
  have hl := (h p).mp hps
  have hr := (g p).mp hqs
  omega

theorem primeSpan_primesLE {a b : ℕ} {ps : List ℕ}
    (ha : a ≤ b) (h : PrimeSpan a b ps) :
    Nat.primesLE b = Nat.primesLE a ∪ ps.toFinset := by
  ext p
  simp only [Nat.mem_primesLE, Finset.mem_union, List.mem_toFinset, h p]
  constructor
  · rintro ⟨hp, hprime⟩
    by_cases hm : p ≤ a
    · exact Or.inl ⟨hm, hprime⟩
    · exact Or.inr ⟨by omega, hp, hprime⟩
  · rintro (⟨hp, hprime⟩ | ⟨_, hp, hprime⟩)
    · exact ⟨hp.trans ha, hprime⟩
    · exact ⟨hp, hprime⟩

end LiuWang.Proof.Campaign20260915.RSFiniteExtension
