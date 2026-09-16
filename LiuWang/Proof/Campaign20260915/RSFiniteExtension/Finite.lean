import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block069
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Exception

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem gap_15991_16001 : PrimeGap 15991 16001 := by decide +kernel

theorem state_16000 : State 16000 158867924626313 172591171463 := by
  have hs := reach_15991.1
  refine ⟨hs.1.trans (Chebyshev.theta_mono (by norm_num)), ?_⟩
  have he : prefixEuler 16000 = prefixEuler 15991 := by
    unfold prefixEuler
    rw [primesLE_gap gap_15991_16001 (by norm_num : 15991 ≤ 16000)
      (by norm_num : 16000 < 16001)]
  simpa only [he] using hs.2

theorem product_3_29_upto_16000 {x : ℝ} (hx : 286 ≤ x) (hi : x ≤ 16000) :
    (prefixEuler ⌊x⌋₊ : ℝ) <
      Real.exp Real.eulerMascheroniConstant *
        (Real.log x + 1 / (2 * Real.log x)) := by
  change _ < productEnvelope x
  by_cases hs : x ≤ 1420
  · exact product_3_29_finite hx hs
  by_cases hm : x ≤ 15991
  · exact reach_15991.2.1 x (le_of_not_ge hs) hm
  apply product_between (by norm_num : 3 ≤ (15991 : ℕ)) gap_15991_16001
    (le_of_not_ge hm) (by norm_num only [Nat.cast_ofNat]; linarith)
  simpa using reach_15991.2.1 15991 (by norm_num) le_rfl

theorem actual_product_3_29_upto_16000 {x : ℝ} (hx : 286 ≤ x) (hi : x ≤ 16000) :
    (∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / (p - 1)) <
      Real.exp Real.eulerMascheroniConstant *
        (Real.log x + 1 / (2 * Real.log x)) := by
  have h := product_3_29_upto_16000 hx hi
  unfold prefixEuler at h
  push_cast at h
  exact h

theorem theta_gt_sub_two_sqrt_1423_16000 {x : ℝ}
    (hx : 1423 ≤ x) (hi : x ≤ 16000) :
    x - 2 * Real.sqrt x < Chebyshev.theta x := by
  by_cases hs : x ≤ 15991
  · exact reach_15991.2.2 x hx hs
  apply theta_endpoint (T := 158867924626313) (b := 16000) (by linarith) hi
  · norm_num
  · exact reach_15991.1.1.trans
      (Chebyshev.theta_mono (by norm_num only [Nat.cast_ofNat]; exact le_of_not_ge hs))

theorem theta_theorem19_finite {x : ℝ} (hx : 0 < x) (hi : x ≤ 16000)
    (hdomain : x ≤ 1420.9 ∨ 1423 ≤ x) :
    x - 2 * Real.sqrt x < Chebyshev.theta x := by
  rcases hdomain with h | h
  · exact theta_gt_sub_two_sqrt_upto_1420_9 hx h
  · exact theta_gt_sub_two_sqrt_1423_16000 h hi

theorem theta_theorem18_lower_finite {x : ℝ} (hx : 0 < x) (hi : x ≤ 16000) :
    x - 2.05282 * Real.sqrt x < Chebyshev.theta x := by
  by_cases hd : x ≤ 1420.9 ∨ 1423 ≤ x
  · have ht := theta_theorem19_finite hx hi hd
    nlinarith [Real.sqrt_nonneg x]
  · push Not at hd
    exact theta_theorem18_lower_exception (by linarith [hd.1]) hd.2.le

theorem medium_start :
    (158867924626313 : ℝ) / 10000000000 ≤ Chebyshev.theta 16000 ∧
      (prefixEuler 16000 : ℝ) ≤ (172591171463 : ℝ) / 10000000000 :=
  state_16000

#print axioms actual_product_3_29_upto_16000
#print axioms theta_theorem19_finite
#print axioms theta_theorem18_lower_finite
#print axioms medium_start

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
