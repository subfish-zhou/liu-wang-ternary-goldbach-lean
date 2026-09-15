import LiuWang.Proof.Campaign20260915.Totient.ProductCertificates

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.Totient

def productWalk : ℕ → ℕ → ℕ → ℕ → Prop
  | _, 0, U, V => U = V
  | n, k + 1, U, V =>
      (if n.Prime then
        0 < unitsFrom thetaLogRows n ∧
          (eulerStep n U : ℚ) / 10000000000 < productLower (unitsFrom thetaLogRows n)
       else True) ∧ productWalk (n + 1) k (eulerStep n U) V

theorem productWalk_sound {k a U V : ℕ} (ha : 0 < a)
    (hU : eulerUnits (a - 1) = U) (h : productWalk a k U V) :
    eulerUnits (a + k - 1) = V ∧
      ∀ p, a ≤ p → p < a + k → p.Prime →
        0 < unitsFrom thetaLogRows p ∧
          (eulerUnits p : ℚ) / 10000000000 < productLower (unitsFrom thetaLogRows p) := by
  induction k generalizing a U with
  | zero =>
    simp only [productWalk] at h
    exact ⟨by simpa only [Nat.add_zero] using hU.trans h, by intros; omega⟩
  | succ k ih =>
    obtain ⟨hp, ht⟩ := h
    have hs : eulerUnits a = eulerStep a U := by
      have he : a = (a - 1) + 1 := by omega
      conv_lhs => rw [he, eulerUnits, hU]
      rw [← he]
    have hr := ih (a := a + 1) (by omega) (by simpa using hs) ht
    refine ⟨by simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hr.1, ?_⟩
    intro p hpa hpk hprime
    by_cases he : p = a
    · subst p
      rw [if_pos hprime] at hp
      simpa only [hs] using hp
    · exact hr.2 p (by omega) (by omega) hprime

theorem product_walk_287 : productWalk 287 32 102257527751 103933995954 := by
  norm_num [productWalk, eulerStep, unitsFrom, thetaLogRows, productLower]

#print axioms product_walk_287

end LiuWang.Proof.Campaign20260915.Totient
