import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Finite
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper069

set_option autoImplicit false
set_option Elab.async false

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem theta_lt_self_1420_16000 {x : ℝ} (hx : 1420 ≤ x) (hi : x ≤ 16000) :
    Chebyshev.theta x < x := by
  by_cases hs : x ≤ 15991
  · exact upper_reach_15991.2 x hx hs
  rw [theta_between gap_15991_16001 (le_of_not_ge hs)
    (by norm_num only [Nat.cast_ofNat]; linarith)]
  exact (upper_reach_15991.2 15991 (by norm_num) le_rfl).trans_le (le_of_not_ge hs)

theorem theta_theorem18_extension {x : ℝ} (hx : 1420 ≤ x) (hi : x ≤ 16000) :
    x - 2.05282 * Real.sqrt x < Chebyshev.theta x ∧ Chebyshev.theta x < x :=
  ⟨theta_theorem18_lower_finite (by linarith) hi, theta_lt_self_1420_16000 hx hi⟩

theorem theta_theorem9_extension {x : ℝ} (hx : 1420 ≤ x) (hi : x ≤ 16000) :
    Chebyshev.theta x < 1.01624 * x := by
  have h := theta_lt_self_1420_16000 hx hi
  linarith

theorem theta_16000_enclosure :
    (158867924626313 : ℝ) / 10000000000 ≤ Chebyshev.theta 16000 ∧
      Chebyshev.theta 16000 ≤ (158867924837558 : ℝ) / 10000000000 := by
  refine ⟨state_16000.1, ?_⟩
  rw [theta_between gap_15991_16001
    (by norm_num : (15991 : ℝ) ≤ 16000) (by norm_num : (16000 : ℝ) < 16001)]
  exact upper_reach_15991.1

#print axioms theta_theorem18_extension
#print axioms theta_theorem9_extension
#print axioms theta_16000_enclosure

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
