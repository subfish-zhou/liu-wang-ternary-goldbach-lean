import LiuWang.Proof.Campaign20260915.RSFiniteExtension.CompletenessCore

set_option autoImplicit false
set_option Elab.async false

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension

theorem primeSpan_nil (a : ℕ) : PrimeSpan a a [] := by
  intro p
  simp only [List.not_mem_nil, false_iff, not_and]
  intros
  omega

theorem primeSpan_cons {a p b : ℕ} {ps : List ℕ}
    (ha : a < p) (hp : p.Prime) (hg : PrimeGap a p) (hb : p ≤ b)
    (h : PrimeSpan p b ps) : PrimeSpan a b (p :: ps) := by
  intro q
  rw [List.mem_cons, h q]
  constructor
  · rintro (he | ⟨hlo, hhi, hprime⟩)
    · subst q
      exact ⟨ha, hb, hp⟩
    · exact ⟨ha.trans hlo, hhi, hprime⟩
  · rintro ⟨hlo, hhi, hprime⟩
    by_cases he : q = p
    · exact Or.inl he
    right
    refine ⟨?_, hhi, hprime⟩
    by_contra! hle
    exact hg q (Finset.mem_Ioo.mpr ⟨hlo, lt_of_le_of_ne hle he⟩) hprime

theorem checked_of_primeSpan {a b : ℕ} {ps : List ℕ} (h : PrimeSpan a b ps) :
    ∀ p ∈ Finset.Ioc a b, p.Prime ↔ p ∈ ps := by
  intro p hp
  obtain ⟨ha, hb⟩ := Finset.mem_Ioc.mp hp
  exact ⟨fun hprime => (h p).mpr ⟨ha, hb, hprime⟩,
    fun hm => ((h p).mp hm).2.2⟩

end LiuWang.Proof.Campaign20260915.RSFiniteExtension
