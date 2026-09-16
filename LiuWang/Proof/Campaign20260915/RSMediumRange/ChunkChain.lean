import LiuWang.Proof.Campaign20260915.RSMediumRange.MediumWalk
import LiuWang.Proof.Campaign20260915.RSMediumRange.FactorialBase

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.RSMediumRange

deriving instance DecidableEq for MediumState

noncomputable section

def CertifiedChunk (s t : MediumState) : Prop :=
  s.p ≤ t.p ∧ (s.Actual → t.Actual ∧
    ∀ x : ℝ, (s.p : ℝ) ≤ x → x < t.p → MediumBounds x)

theorem certifiedChunk_of_walk {s t : MediumState} {rs : List MediumRow}
    (hs : 16000 ≤ s.p) (he : rs.foldl nextState s = t)
    (hc : MediumWalk s rs)
    (hpr : ∀ r ∈ rs, 2 ≤ r.p ∧ r.p ≤ 100000000)
    (hprime : Nat.Coprime (rs.map MediumRow.p).prod factorialBase) :
    CertifiedChunk s t := by
  have hp : ∀ r ∈ rs, r.p.Prime := by
    have h := batch_prime_of_coprime_factorial
      (ps := rs.map MediumRow.p) (by
        intro p hp
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
        exact hpr r hr) (by rwa [factorialBase_eq])
    intro r hr
    exact h r.p (List.mem_map.mpr ⟨r, hr, rfl⟩)
  have hmono : ∀ (s : MediumState) (rs : List MediumRow),
      MediumWalk s rs → s.p ≤ (rs.foldl nextState s).p := by
    intro s rs
    induction rs generalizing s with
    | nil => intro _; exact le_rfl
    | cons r rs ih =>
      rintro ⟨hc, ht⟩
      exact hc.1.le.trans (ih (nextState s r) ht)
  refine ⟨by simpa only [he] using hmono s rs hc, ?_⟩
  intro ha
  have h := mediumWalk_sound hs ha hc hp
  simpa only [he] using (show (rs.foldl nextState s).Actual ∧
    ∀ x : ℝ, (s.p : ℝ) ≤ x → x < (rs.foldl nextState s).p → MediumBounds x from
      ⟨h.1, h.2.2⟩)

theorem CertifiedChunk.trans {s t u : MediumState}
    (h : CertifiedChunk s t) (g : CertifiedChunk t u) : CertifiedChunk s u := by
  refine ⟨h.1.trans g.1, ?_⟩
  intro ha
  obtain ⟨ht, hb⟩ := h.2 ha
  obtain ⟨hu, hc⟩ := g.2 ht
  refine ⟨hu, ?_⟩
  intro x hsx hxu
  by_cases hxt : x < t.p
  · exact hb x hsx hxt
  · exact hc x (le_of_not_gt hxt) hxu

#print axioms certifiedChunk_of_walk
#print axioms CertifiedChunk.trans

end
end LiuWang.Proof.Campaign20260915.RSMediumRange
