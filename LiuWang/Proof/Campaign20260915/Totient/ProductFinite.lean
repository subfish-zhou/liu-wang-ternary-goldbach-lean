import LiuWang.Proof.Campaign20260915.Totient.ProductBlocks

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace LiuWang.Proof.Campaign20260915.Totient

theorem product_3_29_nat {n : ℕ} (hn : 286 ≤ n) (hi : n ≤ 1420) :
    (prefixEuler n : ℝ) < productEnvelope n := by
  induction n, hn using Nat.le_induction with
  | base => exact product_endpoint_286
  | succ n hn ih =>
    by_cases hp : (n + 1).Prime
    · have hc := (productWalk_sound (by norm_num : 0 < (287 : ℕ))
        eulerUnits_286 product_walk_all).2 (n + 1) (by omega) (by omega) hp
      have hl := log_units_bounds hp (by omega) hi
      have h := productLower_le_envelope hc.1 hl.1 hl.2
      have hb : (eulerUnits (n + 1) : ℝ) / 10000000000 <
          (productLower (unitsFrom thetaLogRows (n + 1)) : ℝ) := by
        have ht := Rat.cast_lt (K := ℝ) |>.mpr hc.2
        simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using ht
      exact (prefixEuler_le_units (n + 1)).trans_lt (hb.trans_le h)
    · rw [prefixEuler_step, if_neg hp]
      exact (ih (by omega)).trans_le (productEnvelope_monotone
        (by change (3 : ℝ) ≤ n; exact_mod_cast (show 3 ≤ n by omega))
        (by change (3 : ℝ) ≤ (n + 1 : ℕ); exact_mod_cast (show 3 ≤ n + 1 by omega))
        (by exact_mod_cast (show n ≤ n + 1 by omega)))

theorem product_3_29_finite {x : ℝ} (hx : 286 ≤ x) (hi : x ≤ 1420) :
    (prefixEuler ⌊x⌋₊ : ℝ) <
      Real.exp Real.eulerMascheroniConstant *
        (Real.log x + 1 / (2 * Real.log x)) := by
  have hn : 286 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (by linarith)).mpr hx
  have hhi : ⌊x⌋₊ ≤ 1420 := by
    simpa using Nat.floor_le_floor hi
  exact (product_3_29_nat hn hhi).trans_le (productEnvelope_monotone
    (by change (3 : ℝ) ≤ ⌊x⌋₊; exact_mod_cast (show 3 ≤ ⌊x⌋₊ by omega))
    (by change 3 ≤ x; linarith)
    (Nat.floor_le (by linarith)))

#print axioms product_3_29_nat
#print axioms product_3_29_finite

end LiuWang.Proof.Campaign20260915.Totient
