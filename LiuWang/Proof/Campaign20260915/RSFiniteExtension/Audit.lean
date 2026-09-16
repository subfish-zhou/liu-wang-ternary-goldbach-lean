import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Completeness
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.UpperFinite

set_option autoImplicit false
set_option Elab.async false

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension

theorem finite_consumers_paid :
    (∀ x : ℝ, 286 ≤ x → x ≤ 16000 →
      (∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / (p - 1)) <
        Real.exp Real.eulerMascheroniConstant *
          (Real.log x + 1 / (2 * Real.log x))) ∧
    (∀ x : ℝ, 0 < x → x ≤ 16000 → (x ≤ 1420.9 ∨ 1423 ≤ x) →
      x - 2 * Real.sqrt x < Chebyshev.theta x) ∧
    (∀ x : ℝ, 1420 ≤ x → x ≤ 16000 →
      x - 2.05282 * Real.sqrt x < Chebyshev.theta x ∧ Chebyshev.theta x < x) :=
  ⟨fun _ hx hi => actual_product_3_29_upto_16000 hx hi,
    fun _ hx hi hd => theta_theorem19_finite hx hi hd,
    fun _ hx hi => theta_theorem18_extension hx hi⟩

#print axioms finite_consumers_paid
#print axioms extensionPrimes_complete
#print axioms extensionPrimes_nodup
#print axioms extensionPrimes_length
#print axioms primesLE_16000_eq
#print axioms theta_16000_enclosure
#print axioms medium_start

end LiuWang.Proof.Campaign20260915.RSFiniteExtension
